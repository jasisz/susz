// The walk back (owners, numbers, the frontier's items) and the writer of
// the canonical layout (spec section 9).

use super::pk::{rv, wv, Pk, FLAG, LOW, MAIN, NONE};
use super::{cant, inv, Stats, R};
use crate::format;
use std::io::Write;

const UNUSED: u32 = u32::MAX;
const USED: u32 = u32::MAX - 1;
// An owner slot, once its expression is written: its position in MAIN, or
// this for an expression in a block (its position there is in its a column).
// No MAIN position is that large: there are at most 2^32 - 1 expressions.
const OWNED: u32 = u32::MAX;

#[derive(Default)]
struct Acc {
    buf: Vec<u8>,
    k: u32,
}

struct Sink<'w, W: Write> {
    w: &'w mut W,
    total: u64,
}

impl<W: Write> Sink<'_, W> {
    fn put(&mut self, b: &[u8]) -> R<()> {
        self.w
            .write_all(b)
            .map_err(|e| cant!("cannot write: {e}"))?;
        self.total += b.len() as u64;
        Ok(())
    }
}

#[inline(always)]
unsafe fn pv(mut p: *mut u8, mut v: u64) -> *mut u8 {
    while v >= 128 {
        *p = (v as u8) | 128;
        p = p.add(1);
        v >>= 7;
    }
    *p = v as u8;
    p.add(1)
}

// Every declared name once (spec 5.2), checked on canonical names.
fn unique_names(pk: &Pk) -> R<()> {
    let mut by: Vec<u32> = vec![u32::MAX; pk.cn.count()];
    let mut q = 0usize;
    let mut di = 0u32;
    while q < pk.dmeta.len() {
        let cnt = pk.dmeta[q + 1] as usize;
        for &n in &pk.dmeta[q + 2..q + 2 + cnt] {
            let c = pk.canon[n as usize] as usize;
            if c == crate::canon::ANON as usize {
                // a structural error of MAIN (spec 5.2)
                return Err(inv!("declaration {di} declares the anonymous name"));
            }
            if by[c] != u32::MAX {
                let name = pk.cn.display(&pk.stream, c as u32);
                return Err(if by[c] == di {
                    inv!("declaration {di} declares {name} twice")
                } else {
                    inv!("{name} is declared twice (declarations {} and {di})", by[c])
                });
            }
            by[c] = di;
        }
        q += 2 + cnt;
        di += 1;
    }
    Ok(())
}

pub fn write<W: Write>(pk: Pk, w: &mut W, with_index: bool) -> R<Stats> {
    let mut pk = pk;
    let n = pk.exprs as usize;
    let nd = pk.decls as usize;
    if pk.names == u32::MAX || pk.levels == u32::MAX || pk.decls == u32::MAX {
        return Err(cant!("more than 2^32 - 1 names, levels or declarations"));
    }
    unique_names(&pk)?;
    let mut name_f: Vec<u32> = vec![UNUSED; pk.names as usize];
    let mut level_f: Vec<u32> = vec![UNUSED; pk.levels as usize];
    let mm: u32;
    let mut cols = std::mem::take(&mut pk.cols);
    if cols.k.len() != n || cols.a.len() != n || cols.b.len() != n || pk.owner.len() != n {
        return Err(cant!("internal: expression counts disagree"));
    }
    // The walk back: an expression is owned by theorem T when only T's value
    // reaches it (through expressions T owns); every other one is in MAIN.
    // Children of owned expressions get FLAG: those in MAIN are frontier items.
    unsafe {
        let mut wk = Wk {
            ow: pk.owner.as_mut_ptr(),
            kv: cols.k.as_ptr(),
            av: cols.a.as_ptr(),
            bv: cols.b.as_ptr(),
            nmv: cols.names.as_ptr(),
            ni: cols.names.len(),
            li: cols.loffs.len(),
            m: 0,
        };
        let mut e = n;
        while e > 0 {
            let v = *wk.ow.add(e - 1) & !FLAG;
            e = if v >= NONE {
                walk_main(&mut wk, e, &cols.x, &cols.loffs)
            } else {
                walk_owned(
                    &mut wk,
                    e,
                    v,
                    &cols.x,
                    &cols.loffs,
                    &mut name_f,
                    &mut level_f,
                )
            };
        }
        if wk.ni != 0 || wk.li != 0 {
            return Err(cant!("internal: records disagree"));
        }
        mm = wk.m;
    }

    let mut sink = Sink { w, total: 0 };
    let mut hd: Vec<u8> = format::MAGIC.to_vec();
    hd.extend_from_slice(&format::MAJOR.to_le_bytes());
    hd.extend_from_slice(&[0u8; 6]);
    sink.put(&hd)?;
    let moff = sink.total;

    // INDEX entries: kind, offset of the record's tag byte in MAIN, block length
    let mut ix_kind: Vec<u8> = Vec::new();
    let mut ix_off: Vec<u64> = Vec::new();
    let mut ix_blen: Vec<u64> = Vec::new();
    if with_index {
        ix_kind.reserve(nd);
        ix_off.reserve(nd);
    }

    const FLUSH: usize = 6 << 20;
    let mut out: Vec<u8> = Vec::with_capacity(FLUSH + (2 << 20));
    let mut accs: Vec<Acc> = (0..nd).map(|_| Acc::default()).collect();
    let mut pool: Vec<Vec<u8>> = Vec::new();
    let (mut f_n, mut f_l) = (0u32, 0u32);
    if name_f[0] == USED {
        out.extend_from_slice(&[19, 0, 1]);
        name_f[0] = f_n;
        f_n += 1;
    }
    if level_f[0] == USED {
        out.extend_from_slice(&[19, 1, 1]);
        level_f[0] = f_l;
        f_l += 1;
    }
    // Going forward, each expression's owner slot is replaced, once its
    // record is written, by its number in MAIN, or by OWNED for one in a
    // block. Its a column, whose children are read by then, takes its number
    // in its block, or a frontier item's number among the items.
    // PROOFS grows while the k, b and names columns already read are given
    // back (its pages are only taken as they are written).
    let mut proofs: Vec<u8> = Vec::with_capacity(n * 3 + n / 2 + 4096);
    let (mut name_id, mut level_id) = (1usize, 1usize);
    let mut e: u32 = 0;
    let mut di: u32 = 0;
    let mut lazy = 0u64;
    let s = &pk.stream[..];
    let ow = pk.owner.as_mut_ptr();
    // the k, b and names columns are given back below these
    let (mut rel, mut nrel) = (0usize, 0usize);
    let mut em = Em {
        ow,
        sk: cols.k.as_ptr(),
        sa: cols.a.as_mut_ptr(),
        sb: cols.b.as_ptr(),
        snm: cols.names.as_ptr(),
        slo: cols.loffs.as_ptr(),
        sn: 0,
        sl: 0,
        mnext: 0,
        f_e: 0,
    };
    let mut p = 0usize;
    while p < s.len() {
        if out.len() > FLUSH {
            sink.put(&out)?;
            out.clear();
        }
        let tag = s[p];
        match tag {
            1 | 2 => {
                let q0 = p;
                p += 1;
                rv(s, &mut p);
                let x = rv(s, &mut p);
                if tag == 1 {
                    p += x as usize;
                }
                out.extend_from_slice(&s[q0..p]);
                if name_f[name_id] == USED {
                    out.extend_from_slice(&[19, 0, 1]);
                    name_f[name_id] = f_n;
                    f_n += 1;
                }
                name_id += 1;
            }
            3..=6 => {
                let q0 = p;
                p += 1;
                rv(s, &mut p);
                if tag == 4 || tag == 5 {
                    rv(s, &mut p);
                }
                out.extend_from_slice(&s[q0..p]);
                if level_f[level_id] == USED {
                    out.extend_from_slice(&[19, 1, 1]);
                    level_f[level_id] = f_l;
                    f_l += 1;
                }
                level_id += 1;
            }
            20 => {
                p += 1;
                let kcount = rv(s, &mut p) as u32;
                let end = e + kcount;
                while e < end {
                    if out.len() > FLUSH {
                        sink.put(&out)?;
                        out.clear();
                    }
                    if e as usize - rel >= 1 << 20 {
                        super::give_back_range(&cols.k, rel, e as usize);
                        super::give_back_range(&cols.b, rel, e as usize);
                        rel = e as usize;
                    }
                    if em.sn - nrel >= 1 << 18 {
                        super::give_back_range(&cols.names, nrel, em.sn);
                        nrel = em.sn;
                    }
                    let sx = &cols.x[..];
                    let cend = end.min(e.saturating_add(32768));
                    out.reserve(32768 * 24);
                    while e < cend {
                        let x = unsafe { *ow.add(e as usize) };
                        if x & MAIN != 0 {
                            e = unsafe { main_run(&mut em, e, cend, &mut out, sx) };
                        } else {
                            let o = (x & LOW) as usize;
                            let a = &mut accs[o];
                            if a.k == 0 {
                                if let Some(b) = pool.pop() {
                                    a.buf = b;
                                }
                            }
                            e = unsafe {
                                owned_run(&mut em, e, cend, o as u32, a, sx, &name_f, &level_f)
                            };
                        }
                    }
                }
            }
            18 => {
                p += 1;
                let kind = s[p];
                p += 1;
                let is_lazy = accs[di as usize].k > 0;
                if with_index {
                    ix_off.push(sink.total + out.len() as u64 - moff);
                    ix_kind.push(if is_lazy { 6 } else { kind });
                }
                out.push(18);
                let mnext = em.mnext;
                let newid_back = |c: u32| -> u64 { (mnext - pk.owner[c as usize]) as u64 };
                if is_lazy {
                    let acc = std::mem::take(&mut accs[di as usize]);
                    let blen = acc.buf.len() as u64;
                    if with_index {
                        ix_blen.push(blen);
                    }
                    out.push(6);
                    loop {
                        let t = s[p];
                        p += 1;
                        match t {
                            0 => {
                                let l = rv(s, &mut p) as usize;
                                out.extend_from_slice(&s[p..p + l]);
                                p += l;
                            }
                            1 => {
                                let c = rv(s, &mut p) as u32;
                                wv(&mut out, newid_back(c));
                            }
                            2 => {
                                // the value: block length and expression count
                                rv(s, &mut p);
                                wv(&mut out, blen);
                                wv(&mut out, acc.k as u64);
                            }
                            _ => break,
                        }
                    }
                    proofs.extend_from_slice(&acc.buf);
                    let mut b = acc.buf;
                    b.clear();
                    pool.push(b);
                    lazy += 1;
                } else {
                    out.push(kind);
                    loop {
                        let t = s[p];
                        p += 1;
                        match t {
                            0 => {
                                let l = rv(s, &mut p) as usize;
                                out.extend_from_slice(&s[p..p + l]);
                                p += l;
                            }
                            1 | 2 => {
                                let c = rv(s, &mut p) as u32;
                                wv(&mut out, newid_back(c));
                            }
                            _ => break,
                        }
                    }
                }
                di += 1;
            }
            t => return Err(cant!("internal: bad stream tag {t} at {p}")),
        }
    }
    if em.mnext != mm || e as usize != n || di as usize != nd {
        return Err(cant!("internal: counts disagree"));
    }
    // what INDEX and the rest no longer need
    if em.sn != cols.names.len() || em.sl != cols.loffs.len() {
        return Err(cant!("internal: records disagree"));
    }
    cols.give_back();
    super::give_back(std::mem::take(&mut pk.owner));
    drop(accs);
    drop(pool);
    sink.put(&out)?;
    drop(out);
    let mlen = sink.total - moff;
    let mut dir: Vec<(u16, u16, u64, u64)> =
        vec![(format::SEC_MAIN, format::MUST_UNDERSTAND, moff, mlen)];
    let poff = sink.total;
    let plen = proofs.len() as u64;
    if lazy > 0 {
        sink.put(&proofs)?;
        dir.push((format::SEC_PROOFS, format::MUST_UNDERSTAND, poff, plen));
    }
    super::give_back(proofs);
    let mut index_bytes = 0u64;
    if with_index {
        let ix = build_index(&pk, &ix_kind, &ix_off, &ix_blen);
        let off = sink.total;
        sink.put(&ix)?;
        index_bytes = ix.len() as u64;
        dir.push((format::SEC_INDEX, 0, off, index_bytes));
    }
    let soff = sink.total;
    sink.put(&pk.meta)?;
    dir.push((format::SEC_SOURCE, 0, soff, pk.meta.len() as u64));
    let mut t: Vec<u8> = Vec::new();
    for x in [pk.names, pk.levels, mm, pk.decls] {
        t.extend_from_slice(&x.to_le_bytes());
    }
    t.extend_from_slice(&(dir.len() as u32).to_le_bytes());
    for &(id, fl, off, len) in &dir {
        t.extend_from_slice(&id.to_le_bytes());
        t.extend_from_slice(&fl.to_le_bytes());
        t.extend_from_slice(&0u32.to_le_bytes());
        t.extend_from_slice(&off.to_le_bytes());
        t.extend_from_slice(&len.to_le_bytes());
    }
    let tlen = 16 + 4 + 24 * dir.len() as u32 + 8;
    t.extend_from_slice(&tlen.to_le_bytes());
    t.extend_from_slice(&format::END_MAGIC);
    sink.put(&t)?;
    Ok(Stats {
        names: pk.names as u64,
        levels: pk.levels as u64,
        exprs: n as u64,
        main_exprs: mm as u64,
        decls: nd as u64,
        blocks: lazy,
        main_bytes: mlen,
        proofs_bytes: if lazy > 0 { plen } else { 0 },
        index_bytes,
        source_bytes: pk.meta.len() as u64,
        file_bytes: sink.total,
        parallel: false,
    })
}

// The walk back's columns and where it is in them.
struct Wk {
    ow: *mut u32,
    kv: *const u8,
    av: *const u32,
    bv: *const u32,
    nmv: *const u32,
    // the binder names and leaves before the expression reached
    ni: usize,
    li: usize,
    // expressions in MAIN
    m: u32,
}

// Back from expression e - 1 while the expressions are in MAIN (owned by no
// declaration, or by several): their children are in MAIN too. Returns how
// many expressions are left.
#[inline(never)]
unsafe fn walk_main(wk: &mut Wk, mut e: usize, xs: &[u8], loffs: &[u64]) -> usize {
    let (ow, kv, av, bv) = (wk.ow, wk.kv, wk.av, wk.bv);
    let (mut ni, mut li, mut m) = (wk.ni, wk.li, wk.m);
    while e > 0 {
        let i = e - 1;
        let x = *ow.add(i);
        if x & !FLAG < NONE {
            break;
        }
        *ow.add(i) = MAIN | (x & FLAG);
        m += 1;
        let kind = *kv.add(i);
        if kind != 0 {
            if kind >= 2 {
                ni -= 1;
            }
            let p1 = ow.add(*av.add(i) as usize);
            *p1 = MAIN | (*p1 & FLAG);
            let p2 = ow.add(*bv.add(i) as usize);
            *p2 = MAIN | (*p2 & FLAG);
        } else {
            li -= 1;
            xchildren(
                xs,
                *loffs.get_unchecked(li) as usize,
                |c| {
                    let p = ow.add(c as usize);
                    *p = MAIN | (*p & FLAG);
                },
                |_| {},
                |_| {},
            );
        }
        e = i;
    }
    wk.ni = ni;
    wk.li = li;
    wk.m = m;
    e
}

// Back from expression e - 1 while declaration o owns the expressions: each
// child is owned by o too unless something else reaches it, and gets FLAG.
#[inline(never)]
unsafe fn walk_owned(
    wk: &mut Wk,
    mut e: usize,
    o: u32,
    xs: &[u8],
    loffs: &[u64],
    name_f: &mut [u32],
    level_f: &mut [u32],
) -> usize {
    let (ow, kv, av, bv, nmv) = (wk.ow, wk.kv, wk.av, wk.bv, wk.nmv);
    let (mut ni, mut li) = (wk.ni, wk.li);
    let mark = |c: u32| {
        let p = ow.add(c as usize);
        let w = *p & !FLAG;
        let nw = if w == NONE || w == o { o } else { MAIN };
        *p = nw | FLAG;
    };
    while e > 0 {
        let i = e - 1;
        if *ow.add(i) & !FLAG != o {
            break;
        }
        let kind = *kv.add(i);
        if kind != 0 {
            mark(*av.add(i));
            mark(*bv.add(i));
            if kind >= 2 {
                ni -= 1;
                *name_f.get_unchecked_mut(*nmv.add(ni) as usize) = USED;
            }
        } else {
            li -= 1;
            xchildren(
                xs,
                *loffs.get_unchecked(li) as usize,
                mark,
                |x| name_f[x as usize] = USED,
                |l| level_f[l as usize] = USED,
            );
        }
        e = i;
    }
    wk.ni = ni;
    wk.li = li;
    e
}

// The columns the writer walks forward, and where it is in them.
struct Em {
    ow: *mut u32,
    sk: *const u8,
    sa: *mut u32,
    sb: *const u32,
    snm: *const u32,
    slo: *const u64,
    // the next binder's name, the next leaf
    sn: usize,
    sl: usize,
    // the next MAIN number, the next frontier item
    mnext: u32,
    f_e: u32,
}

// The MAIN expressions from e on, below cend: their records into out (room
// for 24 bytes each reserved). Returns the first expression not in MAIN.
#[inline(never)]
unsafe fn main_run(em: &mut Em, mut e: u32, cend: u32, out: &mut Vec<u8>, sx: &[u8]) -> u32 {
    let (ow, sk, sa, sb, snm, slo) = (em.ow, em.sk, em.sa, em.sb, em.snm, em.slo);
    let (mut sn, mut sl, mut mnext, mut f_e) = (em.sn, em.sl, em.mnext, em.f_e);
    let mut ob = out.as_mut_ptr();
    let mut op = ob.add(out.len());
    while e < cend {
        let i = e as usize;
        let x = *ow.add(i);
        if x & MAIN == 0 {
            break;
        }
        let kind = *sk.add(i) as u32;
        let re = mnext;
        let mref = |c: u32| (re - *ow.add(c as usize)) as u64;
        match kind {
            1 => {
                *op = 10;
                op = pv(op.add(1), mref(*sa.add(i)));
                op = pv(op, mref(*sb.add(i)));
            }
            2..=9 => {
                *op = if kind < 6 { 11 } else { 12 };
                *op.add(1) = ((kind - 2) & 3) as u8;
                op = pv(op.add(2), *snm.add(sn) as u64);
                sn += 1;
                op = pv(op, mref(*sa.add(i)));
                op = pv(op, mref(*sb.add(i)));
            }
            _ => {
                let lo = *slo.add(sl) as usize;
                sl += 1;
                out.set_len(op.offset_from(ob) as usize);
                main_other(sx, lo, out, mref);
                out.reserve(32768 * 24);
                ob = out.as_mut_ptr();
                op = ob.add(out.len());
            }
        }
        if x & FLAG != 0 {
            *op = 19;
            *op.add(1) = 2;
            *op.add(2) = 1;
            op = op.add(3);
            *sa.add(i) = f_e;
            f_e += 1;
        }
        *ow.add(i) = mnext;
        mnext += 1;
        e += 1;
    }
    out.set_len(op.offset_from(ob) as usize);
    em.sn = sn;
    em.sl = sl;
    em.mnext = mnext;
    em.f_e = f_e;
    e
}

// The expressions from e on, below cend, that block o owns: their records
// into its accumulator. Returns the first expression it does not own.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
unsafe fn owned_run(
    em: &mut Em,
    mut e: u32,
    cend: u32,
    o: u32,
    a: &mut Acc,
    sx: &[u8],
    name_f: &[u32],
    level_f: &[u32],
) -> u32 {
    let (ow, sk, sa, sb, snm, slo) = (em.ow, em.sk, em.sa, em.sb, em.snm, em.slo);
    let (mut sn, mut sl) = (em.sn, em.sl);
    let mut ck = a.k;
    a.buf.reserve(64);
    let mut cb = a.buf.as_mut_ptr();
    let mut cp = cb.add(a.buf.len());
    let mut ce = cb.add(a.buf.capacity());
    let nf = name_f.as_ptr();
    while e < cend {
        let i = e as usize;
        // FLAG may be set
        if *ow.add(i) & !FLAG != o {
            break;
        }
        if (ce.offset_from(cp) as usize) < 64 {
            a.buf.set_len(cp.offset_from(cb) as usize);
            let l = a.buf.len();
            a.buf.reserve(l.max(256));
            cb = a.buf.as_mut_ptr();
            cp = cb.add(a.buf.len());
            ce = cb.add(a.buf.capacity());
        }
        let kind = *sk.add(i) as u32;
        let kloc = ck;
        let er = |c: u32| -> u64 {
            let z = *sa.add(c as usize);
            if *ow.add(c as usize) == OWNED {
                (kloc - z) as u64
            } else {
                // a frontier item (spec 9)
                kloc as u64 + 1 + z as u64
            }
        };
        match kind {
            1 => {
                *cp = 10;
                cp = pv(cp.add(1), er(*sa.add(i)));
                cp = pv(cp, er(*sb.add(i)));
            }
            2..=9 => {
                *cp = if kind < 6 { 11 } else { 12 };
                *cp.add(1) = ((kind - 2) & 3) as u8;
                cp = pv(cp.add(2), *nf.add(*snm.add(sn) as usize) as u64);
                sn += 1;
                cp = pv(cp, er(*sa.add(i)));
                cp = pv(cp, er(*sb.add(i)));
            }
            _ => {
                let lo = *slo.add(sl) as usize;
                sl += 1;
                a.buf.set_len(cp.offset_from(cb) as usize);
                owned_other(sx, lo, &mut a.buf, &er, name_f, level_f);
                a.buf.reserve(64);
                cb = a.buf.as_mut_ptr();
                cp = cb.add(a.buf.len());
                ce = cb.add(a.buf.capacity());
            }
        }
        *ow.add(i) = OWNED;
        *sa.add(i) = kloc;
        ck += 1;
        e += 1;
    }
    a.buf.set_len(cp.offset_from(cb) as usize);
    a.k = ck;
    em.sn = sn;
    em.sl = sl;
    e
}

// The INDEX section (spec 6a.1).
fn build_index(pk: &Pk, kinds: &[u8], offs: &[u64], blens: &[u64]) -> Vec<u8> {
    let nd = kinds.len();
    let mut ix: Vec<u8> = Vec::with_capacity(nd * 4 + 1024);
    format::put_varint(&mut ix, nd as u64);
    let mut prev = 0u64;
    let mut b = 0usize;
    for i in 0..nd {
        ix.push(kinds[i]);
        format::put_varint(&mut ix, offs[i] - prev);
        prev = offs[i];
        if kinds[i] == 6 {
            format::put_varint(&mut ix, blens[b]);
            b += 1;
        }
    }
    // the name table: every declared name, sorted by key, front-coded
    let mut arena: Vec<u8> = Vec::new();
    let mut keys: Vec<(usize, usize, u32)> = Vec::new();
    let mut q = 0usize;
    let mut di = 0u32;
    while q < pk.dmeta.len() {
        let cnt = pk.dmeta[q + 1] as usize;
        for &nm in &pk.dmeta[q + 2..q + 2 + cnt] {
            let c = pk.canon[nm as usize];
            let start = arena.len();
            pk.cn.key(&pk.stream, c, &mut arena);
            keys.push((start, arena.len(), di));
        }
        q += 2 + cnt;
        di += 1;
    }
    let key = |k: &(usize, usize, u32)| &arena[k.0..k.1];
    keys.sort_unstable_by(|a, b| key(a).cmp(key(b)));
    format::put_varint(&mut ix, keys.len() as u64);
    let mut last: &[u8] = &[];
    for k in &keys {
        let cur = key(k);
        let shared = last
            .iter()
            .zip(cur.iter())
            .take_while(|(x, y)| x == y)
            .count();
        format::put_varint(&mut ix, shared as u64);
        format::put_varint(&mut ix, (cur.len() - shared) as u64);
        ix.extend_from_slice(&cur[shared..]);
        format::put_varint(&mut ix, k.2 as u64);
        last = cur;
    }
    ix
}

// The parts of an expression record of xbuf at off: expression children,
// its name, its levels.
#[inline(always)]
fn xchildren(
    xb: &[u8],
    off: usize,
    mut ch: impl FnMut(u32),
    mut name: impl FnMut(u32),
    mut level: impl FnMut(u32),
) {
    let mut q = off + 1;
    match xb[off] {
        8 => level(rv(xb, &mut q) as u32),
        9 => {
            name(rv(xb, &mut q) as u32);
            let k = rv(xb, &mut q);
            for _ in 0..k {
                level(rv(xb, &mut q) as u32);
            }
        }
        13 => {
            name(rv(xb, &mut q) as u32);
            for _ in 0..3 {
                ch(rv(xb, &mut q) as u32);
            }
        }
        16 => {
            name(rv(xb, &mut q) as u32);
            rv(xb, &mut q);
            ch(rv(xb, &mut q) as u32);
        }
        _ => {}
    }
}

// Where the record of section 9 at off ends.
fn rec_end(xb: &[u8], off: usize) -> usize {
    let mut q = off + 1;
    match xb[off] {
        7 | 8 => {
            rv(xb, &mut q);
        }
        9 => {
            rv(xb, &mut q);
            let k = rv(xb, &mut q);
            for _ in 0..k {
                rv(xb, &mut q);
            }
        }
        13 => {
            for _ in 0..4 {
                rv(xb, &mut q);
            }
        }
        14 | 15 => {
            let l = rv(xb, &mut q) as usize;
            q += l;
        }
        16 => {
            for _ in 0..3 {
                rv(xb, &mut q);
            }
        }
        _ => unreachable!(),
    }
    q
}

#[inline(never)]
fn main_other(xb: &[u8], off: usize, out: &mut Vec<u8>, mref: impl Fn(u32) -> u64) {
    let tag = xb[off];
    let mut q = off + 1;
    match tag {
        13 => {
            out.push(13);
            wv(out, rv(xb, &mut q));
            for _ in 0..3 {
                let c = rv(xb, &mut q) as u32;
                wv(out, mref(c));
            }
        }
        16 => {
            out.push(16);
            wv(out, rv(xb, &mut q));
            wv(out, rv(xb, &mut q));
            let c = rv(xb, &mut q) as u32;
            wv(out, mref(c));
        }
        _ => {
            let end = rec_end(xb, off);
            out.extend_from_slice(&xb[off..end]);
        }
    }
}

#[inline(never)]
fn owned_other(
    xb: &[u8],
    off: usize,
    buf: &mut Vec<u8>,
    er: &dyn Fn(u32) -> u64,
    name_f: &[u32],
    level_f: &[u32],
) {
    let tag = xb[off];
    let mut q = off + 1;
    buf.push(tag);
    match tag {
        7 => {
            wv(buf, rv(xb, &mut q));
        }
        8 => {
            let l = rv(xb, &mut q) as usize;
            wv(buf, level_f[l] as u64);
        }
        9 => {
            let n = rv(xb, &mut q) as usize;
            wv(buf, name_f[n] as u64);
            let k = rv(xb, &mut q);
            wv(buf, k);
            for _ in 0..k {
                let l = rv(xb, &mut q) as usize;
                wv(buf, level_f[l] as u64);
            }
        }
        13 => {
            let n = rv(xb, &mut q) as usize;
            wv(buf, name_f[n] as u64);
            for _ in 0..3 {
                let c = rv(xb, &mut q) as u32;
                wv(buf, er(c));
            }
        }
        14 | 15 => {
            buf.pop();
            let end = rec_end(xb, off);
            buf.extend_from_slice(&xb[off..end]);
        }
        16 => {
            let n = rv(xb, &mut q) as usize;
            wv(buf, name_f[n] as u64);
            wv(buf, rv(xb, &mut q));
            let c = rv(xb, &mut q) as u32;
            wv(buf, er(c));
        }
        _ => unreachable!(),
    }
}
