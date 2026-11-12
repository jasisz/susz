// The walk back (owners, numbers, the frontier's items) and the writer of
// the canonical layout (spec section 9).

use super::pk::{rv, wv, Pk, FLAG, LOW, MAIN, NONE};
use super::{cant, inv, Stats, R};
use crate::format;
use std::io::Write;

const UNUSED: u32 = u32::MAX;
const USED: u32 = u32::MAX - 1;

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
    let mut rev: Vec<u32> = vec![0; n];
    let mut bcnt: Vec<u32> = vec![0; nd];
    let mut name_f: Vec<u32> = vec![UNUSED; pk.names as usize];
    let mut level_f: Vec<u32> = vec![UNUSED; pk.levels as usize];
    let mut m: u32 = 0;
    let xbs: Vec<Vec<u8>> = if pk.xbufs.is_empty() {
        vec![std::mem::take(&mut pk.xbuf)]
    } else {
        std::mem::take(&mut pk.xbufs)
    };
    // The walk back: an expression is owned by theorem T when only T's value
    // reaches it (through expressions T owns); every other one is in MAIN.
    // Children of owned expressions get FLAG: those in MAIN are frontier items.
    unsafe {
        let ow = pk.owner.as_mut_ptr();
        let cols = pk.cols.as_ptr();
        let rv_ = rev.as_mut_ptr();
        let bc_ = bcnt.as_mut_ptr();
        let mut e = n;
        while e > 0 {
            e -= 1;
            let x = *ow.add(e);
            let mut v = x & !FLAG;
            if v == NONE {
                v = MAIN;
                *ow.add(e) = MAIN | (x & FLAG);
            }
            let c = *cols.add(e);
            let kind = c.k & 15;
            if v == MAIN {
                *rv_.add(e) = m;
                m += 1;
                if kind != 0 {
                    let p1 = ow.add(c.a as usize);
                    *p1 = MAIN | (*p1 & FLAG);
                    let p2 = ow.add(c.b as usize);
                    *p2 = MAIN | (*p2 & FLAG);
                } else {
                    xchildren(
                        xbs.get_unchecked(c.b as usize),
                        c.a as usize,
                        |c| {
                            let p = ow.add(c as usize);
                            *p = MAIN | (*p & FLAG);
                        },
                        |_| {},
                        |_| {},
                    );
                }
            } else {
                let o = v;
                let bp = bc_.add(o as usize);
                *rv_.add(e) = *bp;
                *bp += 1;
                let mark = |c: u32| {
                    let p = ow.add(c as usize);
                    let w = *p & !FLAG;
                    let nw = if w == NONE || w == o { o } else { MAIN };
                    *p = nw | FLAG;
                };
                if kind != 0 {
                    mark(c.a);
                    mark(c.b);
                    if kind >= 2 {
                        *name_f.get_unchecked_mut((c.k >> 4) as usize) = USED;
                    }
                } else {
                    xchildren(
                        xbs.get_unchecked(c.b as usize),
                        c.a as usize,
                        mark,
                        |x| name_f[x as usize] = USED,
                        |l| level_f[l as usize] = USED,
                    );
                }
            }
        }
    }
    let mm = m;

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
    let mut proofs: Vec<u8> = Vec::with_capacity(n * 3 + n / 2 + 4096);
    let mut accs: Vec<Acc> = (0..nd).map(|_| Acc::default()).collect();
    let mut pool: Vec<Vec<u8>> = Vec::new();
    let (mut f_n, mut f_l, mut f_e) = (0u32, 0u32, 0u32);
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
    let (mut name_id, mut level_id) = (1usize, 1usize);
    let mut e: u32 = 0;
    let mut di: u32 = 0;
    let mut mnext: u32 = 0;
    let mut lazy = 0u64;
    let s = &pk.stream[..];
    let ow = pk.owner.as_mut_ptr();
    let cols = pk.cols.as_ptr();
    let rvp = rev.as_ptr();
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
                    let cend = end.min(e + 32768);
                    out.reserve(32768 * 24);
                    unsafe {
                        let mut ob = out.as_mut_ptr();
                        let mut op = ob.add(out.len());
                        // the block being written to, kept in locals
                        let mut co = usize::MAX;
                        let (mut cb, mut cp, mut ce) = (
                            std::ptr::null_mut::<u8>(),
                            std::ptr::null_mut::<u8>(),
                            std::ptr::null_mut::<u8>(),
                        );
                        let mut ck = 0u32;
                        macro_rules! save {
                            () => {
                                if co != usize::MAX {
                                    let a = accs.get_unchecked_mut(co);
                                    a.buf.set_len(cp.offset_from(cb) as usize);
                                    a.k = ck;
                                }
                            };
                        }
                        macro_rules! reload {
                            () => {
                                let a = accs.get_unchecked_mut(co);
                                cb = a.buf.as_mut_ptr();
                                cp = cb.add(a.buf.len());
                                ce = cb.add(a.buf.capacity());
                            };
                        }
                        while e < cend {
                            let x = *ow.add(e as usize);
                            let c = *cols.add(e as usize);
                            let kind = c.k & 15;
                            let re = *rvp.add(e as usize);
                            if x & MAIN != 0 {
                                match kind {
                                    1 => {
                                        *op = 10;
                                        op = pv(op.add(1), (*rvp.add(c.a as usize) - re) as u64);
                                        op = pv(op, (*rvp.add(c.b as usize) - re) as u64);
                                    }
                                    2..=9 => {
                                        *op = if kind < 6 { 11 } else { 12 };
                                        *op.add(1) = ((kind - 2) & 3) as u8;
                                        op = pv(op.add(2), (c.k >> 4) as u64);
                                        op = pv(op, (*rvp.add(c.a as usize) - re) as u64);
                                        op = pv(op, (*rvp.add(c.b as usize) - re) as u64);
                                    }
                                    _ => {
                                        out.set_len(op.offset_from(ob) as usize);
                                        main_other(
                                            xbs.get_unchecked(c.b as usize),
                                            c.a as usize,
                                            &mut out,
                                            |c| (*rvp.add(c as usize) - re) as u64,
                                        );
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
                                    *ow.add(e as usize) = MAIN | FLAG | f_e;
                                    f_e += 1;
                                }
                                mnext += 1;
                            } else {
                                let o = (x & LOW) as usize;
                                if o != co {
                                    save!();
                                    co = o;
                                    let a = accs.get_unchecked_mut(o);
                                    if a.k == 0 {
                                        if let Some(b) = pool.pop() {
                                            a.buf = b;
                                        }
                                    }
                                    a.buf.reserve(64);
                                    ck = a.k;
                                    reload!();
                                }
                                if (ce.offset_from(cp) as usize) < 64 {
                                    let a = accs.get_unchecked_mut(co);
                                    a.buf.set_len(cp.offset_from(cb) as usize);
                                    let l = a.buf.len();
                                    a.buf.reserve(l.max(256));
                                    reload!();
                                }
                                let kloc = ck as u64;
                                let er = |c: u32| -> u64 {
                                    let y = *ow.add(c as usize);
                                    if y & MAIN == 0 {
                                        (*rvp.add(c as usize) - re) as u64
                                    } else {
                                        kloc + 1 + (y & LOW) as u64
                                    }
                                };
                                match kind {
                                    1 => {
                                        *cp = 10;
                                        cp = pv(cp.add(1), er(c.a));
                                        cp = pv(cp, er(c.b));
                                    }
                                    2..=9 => {
                                        *cp = if kind < 6 { 11 } else { 12 };
                                        *cp.add(1) = ((kind - 2) & 3) as u8;
                                        cp = pv(
                                            cp.add(2),
                                            *name_f.as_ptr().add((c.k >> 4) as usize) as u64,
                                        );
                                        cp = pv(cp, er(c.a));
                                        cp = pv(cp, er(c.b));
                                    }
                                    _ => {
                                        let a = accs.get_unchecked_mut(co);
                                        a.buf.set_len(cp.offset_from(cb) as usize);
                                        owned_other(
                                            xbs.get_unchecked(c.b as usize),
                                            c.a as usize,
                                            &mut a.buf,
                                            &er,
                                            &name_f,
                                            &level_f,
                                        );
                                        a.buf.reserve(64);
                                        reload!();
                                    }
                                }
                                ck += 1;
                            }
                            e += 1;
                        }
                        save!();
                        out.set_len(op.offset_from(ob) as usize);
                    }
                }
            }
            18 => {
                p += 1;
                let kind = s[p];
                p += 1;
                let is_lazy = bcnt[di as usize] > 0;
                if with_index {
                    ix_off.push(sink.total + out.len() as u64 - moff);
                    ix_kind.push(if is_lazy { 6 } else { kind });
                }
                out.push(18);
                let newid_back =
                    |c: u32| -> u64 { mnext as u64 + rev[c as usize] as u64 + 1 - mm as u64 };
                if is_lazy {
                    let acc = std::mem::take(&mut accs[di as usize]);
                    if acc.k != bcnt[di as usize] {
                        return Err(cant!("internal: declaration {di}: block count mismatch"));
                    }
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
    if mnext != mm || e as usize != n || di as usize != nd {
        return Err(cant!("internal: counts disagree"));
    }
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
    drop(proofs);
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

fn copy_rec(xb: &[u8], off: usize) -> usize {
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
        14 | 15 => {
            let l = rv(xb, &mut q) as usize;
            q += l;
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
            let end = copy_rec(xb, off);
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
            let end = copy_rec(xb, off);
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
