// The packer's state while reading lines: tables of ids (Ren), the columns
// of expressions, the stream of other records, names made canonical, owners
// seeded by declarations.

use super::api::{
    Decl, Head, Hints, IndCtor, IndFlags, IndRec, IndRule, IndType, QuotKind, Safety,
};
use super::json::{self, J};
use super::{cant, inv, R};
use crate::canon::Canon;
use std::collections::HashMap;

pub const NONE: u32 = 0x3FFF_FFFF;
pub const MAIN: u32 = 1 << 30;
pub const FLAG: u32 = 1 << 31;

#[inline(always)]
pub fn wv(out: &mut Vec<u8>, mut v: u64) {
    if out.capacity() - out.len() < 10 {
        out.reserve(4096);
    }
    unsafe {
        let mut p = out.as_mut_ptr().add(out.len());
        let s = p;
        while v >= 128 {
            *p = (v as u8) | 128;
            p = p.add(1);
            v >>= 7;
        }
        *p = v as u8;
        p = p.add(1);
        out.set_len(out.len() + p.offset_from(s) as usize);
    }
}

#[inline(always)]
pub fn rv(b: &[u8], p: &mut usize) -> u64 {
    let mut v: u64 = 0;
    let mut s = 0;
    loop {
        let x = unsafe { *b.get_unchecked(*p) };
        *p += 1;
        v |= ((x & 127) as u64) << s;
        if x < 128 {
            return v;
        }
        s += 7;
    }
}

pub struct Ren {
    pub below: u64,
    pub map: Option<HashMap<u64, u32>>,
    // a worker's table before its first definition: every id is taken, the
    // largest named is kept (pend), and the first defined is the start
    pub floating: bool,
    pub pend: std::cell::Cell<u64>,
    pub first: u64,
}

impl Ren {
    pub fn new(below: u64) -> Ren {
        Ren {
            below,
            map: None,
            floating: false,
            pend: std::cell::Cell::new(0),
            first: u64::MAX,
        }
    }
    pub fn new_floating() -> Ren {
        Ren {
            below: u64::MAX,
            map: None,
            floating: true,
            pend: std::cell::Cell::new(0),
            first: u64::MAX,
        }
    }
    #[inline(always)]
    pub fn note(&self, i: u64) {
        if self.floating && i + 1 > self.pend.get() {
            self.pend.set(i + 1);
        }
    }
    #[inline(always)]
    pub fn lookup(&self, i: u64) -> Option<u32> {
        match &self.map {
            None => {
                if i < self.below {
                    Some(i as u32)
                } else {
                    None
                }
            }
            Some(m) => self.lookup_mapped(m, i),
        }
    }
    #[inline(never)]
    fn lookup_mapped(&self, m: &HashMap<u64, u32>, i: u64) -> Option<u32> {
        match m.get(&i) {
            Some(&x) => Some(x),
            None => {
                if i < self.below {
                    Some(i as u32)
                } else {
                    None
                }
            }
        }
    }
    // Defines src as the next dense id, refusing an id bound already.
    #[inline(always)]
    pub fn define(&mut self, src: u64, dense: u32, kind: &str) -> R<()> {
        if self.floating {
            self.floating = false;
            self.first = src;
        }
        if self.map.is_none() && src == dense as u64 {
            self.below = dense as u64 + 1;
            return Ok(());
        }
        self.define_slow(src, dense, kind)
    }
    #[inline(never)]
    fn define_slow(&mut self, src: u64, dense: u32, kind: &str) -> R<()> {
        if self.lookup(src).is_some() {
            return Err(inv!("{kind} index {src} is already bound"));
        }
        self.map.get_or_insert_with(HashMap::new).insert(src, dense);
        Ok(())
    }
    // Binds src to an existing dense id (an mdata expression stands for the
    // expression it wraps, spec 9.1).
    pub fn alias(&mut self, src: u64, dense: u32, kind: &str) -> R<()> {
        if self.lookup(src).is_some() {
            return Err(inv!("{kind} index {src} is already bound"));
        }
        self.map.get_or_insert_with(HashMap::new).insert(src, dense);
        Ok(())
    }
    pub fn fresh(&self, src: u64, kind: &str) -> R<()> {
        if self.floating {
            return Ok(());
        }
        if self.lookup(src).is_some() {
            return Err(inv!("{kind} index {src} is already bound"));
        }
        Ok(())
    }
}

// The writer works in segments of this many expressions (a multiple of 32).
pub const SEG: u64 = 1 << 19;

// Where in the stream a segment starts: at record p, or just after the header
// of a run record at p with `left` of its expressions from e0 on; and the
// ids of the next name, level and declaration there.
pub struct SegStart {
    pub p: usize,
    pub left: u32,
    pub e0: u32,
    pub name_id: u32,
    pub level_id: u32,
    pub di: u32,
}

// Notes the segments that start in a run record of k expressions after e,
// written at p0 with its header ending at p1; b is the next segment's start.
#[allow(clippy::too_many_arguments)]
#[inline(always)]
pub fn note_segs(
    segs: &mut Vec<SegStart>,
    b: &mut u64,
    p0: usize,
    p1: usize,
    e: u64,
    k: u64,
    name_id: u32,
    level_id: u32,
    di: u32,
) {
    while *b < e + k {
        let (p, left) = if *b == e {
            (p0, 0)
        } else {
            (p1, (e + k - *b) as u32)
        };
        segs.push(SegStart {
            p,
            left,
            e0: *b as u32,
            name_id,
            level_id,
            di,
        });
        *b += SEG;
    }
}

// Expressions are numbered below 2^32 - 1, as the format allows.
pub const MAX_EXPRS: u32 = u32::MAX;
// The expressions in columns, by id. k holds the kind (0, a leaf: any
// expression that is not an application or a binder), a and b the children
// of an application or binder. names holds each binder's name in turn. A
// leaf's record (as section 9 writes it, with absolute ids) is in x, at
// loffs, in turn.
#[derive(Default)]
pub struct Cols {
    pub k: Vec<u8>,
    pub a: Vec<u32>,
    pub b: Vec<u32>,
    pub names: Vec<u32>,
    pub x: Vec<u8>,
    pub loffs: Vec<u64>,
}

impl Cols {
    pub fn give_back(self) {
        use super::give_back;
        give_back(self.k);
        give_back(self.a);
        give_back(self.b);
        give_back(self.names);
        give_back(self.x);
        give_back(self.loffs);
    }
}

unsafe impl Send for Pk {}

// Stream records: 1,2 names and 3..6 levels as in Susz v0; 20 K: a run of K
// expressions (columns); 18 kind pieces...: a declaration whose pieces are
// 0 len raw | 1 abs ref | 2 abs value, ended by 3.
pub struct Pk {
    pub nr: Ren,
    pub lr: Ren,
    pub er: Ren,
    pub names: u32,
    pub levels: u32,
    pub exprs: u32,
    pub decls: u32,
    pub run: u32,
    pub stream: Vec<u8>,
    // the expressions read: k, a and b written at the expression's id
    // through kp, ap and bp, room for colcap (one allocation for every
    // expression the file can hold; workers share one and write at global
    // ids); the other columns are a worker's own until merged
    pub cols: Cols,
    pub kp: *mut u8,
    pub ap: *mut u32,
    pub bp: *mut u32,
    pub colcap: u64,
    // a leaf record being built
    pub xbuf: Vec<u8>,
    pub canon: Vec<u32>,
    pub cn: Canon,
    pub owner: Vec<u32>,
    pub meta: Vec<u8>,
    // the header's format.version is 3.2.x: every inductive type must carry
    // its flags
    pub needs_flags: bool,
    // parsing a range on a worker: no owners or canonical names made here
    pub worker: bool,
    pub fl: bool,
    // per declaration: its kind, the number of names it declares, those
    // names (dense name ids)
    pub dmeta: Vec<u32>,
    // the writer's segments after the first, and the next one's start
    pub segs: Vec<SegStart>,
    seg_b: u64,
    // a declaration being built
    draw: Vec<u8>,
    dpieces: Vec<u8>,
    dnames: Vec<u32>,
    drefs: Vec<(u32, bool)>,
}

pub fn binder_of(s: &[u8]) -> R<u32> {
    match s {
        b"default" => Ok(0),
        b"implicit" => Ok(1),
        b"strictImplicit" => Ok(2),
        b"instImplicit" => Ok(3),
        _ => Err(cant!("unknown binderInfo '{}'", String::from_utf8_lossy(s))),
    }
}

impl Pk {
    pub fn new(size_hint: usize) -> Pk {
        let ex = size_hint / 48 + 16;
        let _ = ex;
        Pk {
            nr: Ren::new(1),
            lr: Ren::new(1),
            er: Ren::new(0),
            names: 1,
            levels: 1,
            exprs: 0,
            decls: 0,
            run: 0,
            stream: Vec::with_capacity(size_hint / 16 + 1024),
            cols: Cols::default(),
            kp: std::ptr::null_mut(),
            ap: std::ptr::null_mut(),
            bp: std::ptr::null_mut(),
            colcap: 0,
            xbuf: Vec::with_capacity(1024),
            canon: {
                let mut v = Vec::with_capacity(size_hint / 400 + 16);
                v.push(0);
                v
            },
            cn: Canon::new(),
            owner: Vec::new(),
            meta: Vec::new(),
            needs_flags: false,
            worker: false,
            fl: false,
            dmeta: Vec::new(),
            segs: Vec::new(),
            seg_b: SEG,
            draw: Vec::new(),
            dpieces: Vec::new(),
            dnames: Vec::new(),
            drefs: Vec::new(),
        }
    }

    pub fn new_worker(size_hint: usize) -> Pk {
        let mut pk = Pk::new(size_hint);
        pk.worker = true;
        pk.fl = true;
        pk.nr = Ren::new_floating();
        pk.lr = Ren::new_floating();
        pk.er = Ren::new_floating();
        pk.names = 0;
        pk.levels = 0;
        pk.exprs = 0;
        pk
    }
    #[inline(always)]
    fn refl(&mut self) {
        self.fl = self.nr.floating || self.lr.floating || self.er.floating;
    }

    #[inline(always)]
    pub fn eref(&self, i: u64) -> R<u32> {
        if self.fl {
            self.er.note(i);
        }
        match self.er.lookup(i) {
            Some(x) => Ok(x),
            None => Err(inv!("unknown expression index {i}")),
        }
    }
    #[inline(always)]
    pub fn nm(&self, i: u64) -> R<u32> {
        if self.fl {
            self.nr.note(i);
        }
        match self.nr.lookup(i) {
            Some(x) => Ok(x),
            None => Err(inv!("unknown name index {i}")),
        }
    }
    #[inline(always)]
    pub fn lv(&self, i: u64) -> R<u32> {
        if self.fl {
            self.lr.note(i);
        }
        match self.lr.lookup(i) {
            Some(x) => Ok(x),
            None => Err(inv!("unknown level index {i}")),
        }
    }

    #[inline(always)]
    fn flush_run(&mut self) {
        if self.run > 0 {
            let p0 = self.stream.len();
            self.stream.push(20);
            wv(&mut self.stream, self.run as u64);
            if !self.worker {
                let k = self.run as u64;
                note_segs(
                    &mut self.segs,
                    &mut self.seg_b,
                    p0,
                    self.stream.len(),
                    self.exprs as u64 - k,
                    k,
                    self.names,
                    self.levels,
                    self.decls,
                );
            }
            self.run = 0;
        }
    }
    // Reading on one worker: room reserved for the columns and owners of all
    // the expressions the file can hold (a line takes at least 16 bytes);
    // pages are only taken as they are written.
    pub fn reserve_all(&mut self, size: usize) {
        let cap = size / 16 + 16;
        self.cols.k = Vec::with_capacity(cap);
        self.cols.a = Vec::with_capacity(cap);
        self.cols.b = Vec::with_capacity(cap);
        self.kp = self.cols.k.as_mut_ptr();
        self.ap = self.cols.a.as_mut_ptr();
        self.bp = self.cols.b.as_mut_ptr();
        self.colcap = cap as u64;
        self.owner = Vec::with_capacity(cap);
    }
    pub fn finish_range(&mut self) {
        self.flush_run();
    }
    pub fn finish(&mut self) {
        self.finish_range();
        self.owner.resize(self.exprs as usize, NONE);
        unsafe {
            self.cols.k.set_len(self.exprs as usize);
            self.cols.a.set_len(self.exprs as usize);
            self.cols.b.set_len(self.exprs as usize);
        }
    }

    #[inline(always)]
    fn begin(&mut self, ie: u64) -> R<u32> {
        if self.er.floating {
            if ie >= MAX_EXPRS as u64 {
                return Err(cant!("expression id out of range for a worker"));
            }
            self.exprs = ie as u32;
            self.er.define(ie, ie as u32, "expression")?;
            self.refl();
            self.er.below = ie;
        }
        let e = self.exprs;
        if e == MAX_EXPRS {
            return Err(cant!("more than 2^32 - 1 expressions"));
        }
        if e as u64 >= self.colcap {
            self.grow_cols()?;
        }
        self.er.define(ie, e, "expression")?;
        self.exprs = e + 1;
        self.run += 1;
        Ok(e)
    }
    // Past the room reserved: a worker's columns are shared and cannot move;
    // on one worker (records handed over one by one) they grow.
    #[inline(never)]
    fn grow_cols(&mut self) -> R<()> {
        if self.worker {
            return Err(cant!("more expressions than the file can hold"));
        }
        let n = self.exprs as usize;
        let cap = (self.colcap as usize).max(1 << 16) * 2;
        unsafe {
            self.cols.k.set_len(n);
            self.cols.a.set_len(n);
            self.cols.b.set_len(n);
        }
        self.cols.k.reserve_exact(cap - n);
        self.cols.a.reserve_exact(cap - n);
        self.cols.b.reserve_exact(cap - n);
        self.kp = self.cols.k.as_mut_ptr();
        self.ap = self.cols.a.as_mut_ptr();
        self.bp = self.cols.b.as_mut_ptr();
        self.colcap = cap as u64;
        Ok(())
    }
    #[inline(always)]
    fn new_expr(&mut self, ie: u64, k: u32, a: u32, b: u32) -> R<()> {
        let e = self.begin(ie)?;
        unsafe {
            self.kp.add(e as usize).write((k & 15) as u8);
            self.ap.add(e as usize).write(a);
            self.bp.add(e as usize).write(b);
        }
        if k & 15 >= 2 {
            self.cols.names.push(k >> 4);
        }
        Ok(())
    }
    fn new_leaf(&mut self, ie: u64) -> R<()> {
        let e = self.begin(ie)?;
        unsafe {
            self.kp.add(e as usize).write(0);
            self.ap.add(e as usize).write(0);
            self.bp.add(e as usize).write(0);
        }
        self.cols.loffs.push(self.cols.x.len() as u64);
        self.cols.x.extend_from_slice(&self.xbuf);
        Ok(())
    }
    #[inline(always)]
    fn xstart(&mut self, ie: u64) -> R<()> {
        self.er.fresh(ie, "expression")?;
        self.xbuf.clear();
        Ok(())
    }

    #[inline(always)]
    pub fn app(&mut self, ie: u64, f: u64, a: u64) -> R<()> {
        let kf = self.eref(f)?;
        let ka = self.eref(a)?;
        self.new_expr(ie, 1, kf, ka)
    }
    #[inline(always)]
    pub fn bind(&mut self, ie: u64, lam: bool, bi: u32, n: u64, t: u64, body: u64) -> R<()> {
        let nn = self.nm(n)?;
        let kt = self.eref(t)?;
        let kb = self.eref(body)?;
        if nn >= 1 << 28 {
            return Err(cant!("too many names for this packer"));
        }
        self.new_expr(ie, (nn << 4) | ((if lam { 2 } else { 6 }) + bi), kt, kb)
    }
    pub fn bvar(&mut self, ie: u64, k: u64) -> R<()> {
        self.xstart(ie)?;
        self.xbuf.push(7);
        wv(&mut self.xbuf, k);
        self.new_leaf(ie)
    }
    pub fn sort(&mut self, ie: u64, l: u64) -> R<()> {
        self.xstart(ie)?;
        let kl = self.lv(l)?;
        self.xbuf.push(8);
        wv(&mut self.xbuf, kl as u64);
        self.new_leaf(ie)
    }
    pub fn cnst(&mut self, ie: u64, n: u64, us: &[u64]) -> R<()> {
        self.xstart(ie)?;
        let nn = self.nm(n)?;
        self.xbuf.push(9);
        wv(&mut self.xbuf, nn as u64);
        wv(&mut self.xbuf, us.len() as u64);
        for &u in us {
            let l = self.lv(u)?;
            wv(&mut self.xbuf, l as u64);
        }
        self.new_leaf(ie)
    }
    pub fn let_e(&mut self, ie: u64, n: u64, t: u64, v: u64, b: u64) -> R<()> {
        self.xstart(ie)?;
        let nn = self.nm(n)?;
        let (kt, kv, kb) = (self.eref(t)?, self.eref(v)?, self.eref(b)?);
        self.xbuf.push(13);
        for x in [nn, kt, kv, kb] {
            wv(&mut self.xbuf, x as u64);
        }
        self.new_leaf(ie)
    }
    pub fn nat(&mut self, ie: u64, digits: &[u8]) -> R<()> {
        self.xstart(ie)?;
        if digits.first() == Some(&b'-') {
            return Err("negative Nat literal".into());
        }
        let Some(bytes) = crate::format::nat_from_decimal(digits) else {
            return Err("malformed Nat literal".into());
        };
        self.xbuf.push(14);
        wv(&mut self.xbuf, bytes.len() as u64);
        self.xbuf.extend_from_slice(&bytes);
        self.new_leaf(ie)
    }
    // A Nat literal already in its Susz form: minimal little-endian bytes
    // (slicing a Susz file; no decimal round trip for huge literals).
    pub fn nat_le(&mut self, ie: u64, bytes: &[u8]) -> R<()> {
        self.xstart(ie)?;
        if bytes.last() == Some(&0) {
            return Err(cant!("internal: a Nat literal that is not minimal"));
        }
        self.xbuf.push(14);
        wv(&mut self.xbuf, bytes.len() as u64);
        self.xbuf.extend_from_slice(bytes);
        self.new_leaf(ie)
    }
    pub fn strv(&mut self, ie: u64, s: &[u8]) -> R<()> {
        self.xstart(ie)?;
        self.xbuf.push(15);
        wv(&mut self.xbuf, s.len() as u64);
        self.xbuf.extend_from_slice(s);
        self.new_leaf(ie)
    }
    pub fn proj(&mut self, ie: u64, tn: u64, idx: u64, st: u64) -> R<()> {
        self.xstart(ie)?;
        let ks = self.eref(st)?;
        let nn = self.nm(tn)?;
        self.xbuf.push(16);
        wv(&mut self.xbuf, nn as u64);
        wv(&mut self.xbuf, idx);
        wv(&mut self.xbuf, ks as u64);
        self.new_leaf(ie)
    }
    // mdata is not written: ie stands for the expression it wraps.
    pub fn mdata(&mut self, ie: u64, x: u64) -> R<()> {
        if self.worker {
            // the parallel read assumes dense ids; the read on one worker takes it
            return Err(cant!("mdata on a worker"));
        }
        self.er.fresh(ie, "expression")?;
        let kx = self.eref(x)?;
        self.er.alias(ie, kx, "expression")
    }

    // Names and levels.
    #[inline(always)]
    fn float_name(&mut self, i: u64) -> R<()> {
        if self.nr.floating {
            if i >= u32::MAX as u64 {
                return Err(cant!("name id out of range for a worker"));
            }
            self.names = i as u32;
            self.nr.define(i, i as u32, "name")?;
            self.refl();
            self.nr.below = i;
        }
        Ok(())
    }
    pub fn name_str(&mut self, i: u64, pre: u64, s: &[u8]) -> R<()> {
        let kp = self.nm(pre)?;
        if s.len() as u64 >= crate::canon::MAX_COMPONENT {
            return Err(cant!(
                "a name component of {} bytes is too long for this packer",
                s.len()
            ));
        }
        self.float_name(i)?;
        let id = self.names;
        self.nr.define(i, id, "name")?;
        self.flush_run();
        self.stream.push(1);
        wv(&mut self.stream, kp as u64);
        wv(&mut self.stream, s.len() as u64);
        let off = self.stream.len() as u64;
        self.stream.extend_from_slice(s);
        if !self.worker {
            let cp = self.canon[kp as usize];
            let c = self.cn.str_id(&self.stream, cp, off, s.len() as u32);
            self.canon.push(c);
        }
        self.names = id + 1;
        Ok(())
    }
    pub fn name_num(&mut self, i: u64, pre: u64, k: u64) -> R<()> {
        let kp = self.nm(pre)?;
        self.float_name(i)?;
        let id = self.names;
        self.nr.define(i, id, "name")?;
        self.flush_run();
        self.stream.push(2);
        wv(&mut self.stream, kp as u64);
        wv(&mut self.stream, k);
        if !self.worker {
            let cp = self.canon[kp as usize];
            let c = self.cn.num_id(cp, k);
            self.canon.push(c);
        }
        self.names = id + 1;
        Ok(())
    }
    fn level(&mut self, i: u64, tag: u8, x: u32, y: Option<u32>) -> R<()> {
        if self.lr.floating {
            if i >= u32::MAX as u64 {
                return Err(cant!("level id out of range for a worker"));
            }
            self.levels = i as u32;
            self.lr.define(i, i as u32, "level")?;
            self.refl();
            self.lr.below = i;
        }
        let id = self.levels;
        self.lr.define(i, id, "level")?;
        self.flush_run();
        self.stream.push(tag);
        wv(&mut self.stream, x as u64);
        if let Some(y) = y {
            wv(&mut self.stream, y as u64);
        }
        self.levels = id + 1;
        Ok(())
    }
    pub fn succ(&mut self, i: u64, a: u64) -> R<()> {
        let ka = self.lv(a)?;
        self.level(i, 3, ka, None)
    }
    pub fn param(&mut self, i: u64, n: u64) -> R<()> {
        let kn = self.nm(n)?;
        self.level(i, 6, kn, None)
    }
    pub fn pair(&mut self, i: u64, a: u64, b: u64, max: bool) -> R<()> {
        let ka = self.lv(a)?;
        let kb = self.lv(b)?;
        self.level(i, if max { 4 } else { 5 }, ka, Some(kb))
    }

    // Declarations.
    fn d_start(&mut self) {
        self.draw.clear();
        self.dpieces.clear();
        self.dnames.clear();
        self.drefs.clear();
    }
    #[inline(always)]
    fn dv(&mut self, v: u64) {
        wv(&mut self.draw, v);
    }
    fn dbyte(&mut self, x: u8) {
        self.draw.push(x);
    }
    fn dflush(&mut self) {
        if !self.draw.is_empty() {
            self.dpieces.push(0);
            wv(&mut self.dpieces, self.draw.len() as u64);
            self.dpieces.extend_from_slice(&self.draw);
            self.draw.clear();
        }
    }
    fn dref(&mut self, i: u64, val: bool) -> R<()> {
        let e = self.eref(i)?;
        self.dflush();
        self.dpieces.push(if val { 2 } else { 1 });
        wv(&mut self.dpieces, e as u64);
        self.drefs.push((e, val));
        Ok(())
    }
    fn dnms(&mut self, xs: &[u64]) -> R<()> {
        self.dv(xs.len() as u64);
        for &x in xs {
            let n = self.nm(x)?;
            self.dv(n as u64);
        }
        Ok(())
    }
    fn dhead(&mut self, name: u64, params: &[u64], ty: u64) -> R<()> {
        let n = self.nm(name)?;
        self.dnames.push(n);
        self.dv(n as u64);
        self.dnms(params)?;
        self.dref(ty, false)
    }
    fn d_end(&mut self, kind: u8) {
        self.dflush();
        self.flush_run();
        self.stream.push(18);
        self.stream.push(kind);
        self.stream.extend_from_slice(&self.dpieces);
        self.stream.push(3);
        let di = self.decls;
        self.dmeta.push(kind as u32);
        self.dmeta.push(self.dnames.len() as u32);
        self.dmeta.extend_from_slice(&self.dnames);
        if self.worker {
            self.decls = di + 1;
            return;
        }
        if self.owner.len() < self.exprs as usize {
            self.owner.resize(self.exprs as usize, NONE);
        }
        for &(e, val) in self.drefs.iter() {
            let x = &mut self.owner[e as usize];
            if val {
                let w = *x & !FLAG;
                let nw = if w == NONE {
                    di
                } else if w == di {
                    w
                } else {
                    MAIN
                };
                *x = nw | (*x & FLAG);
            } else {
                *x = MAIN | (*x & FLAG);
            }
        }
        self.decls = di + 1;
    }
    fn check_decls(&self) -> R<()> {
        if self.decls >= NONE - 1 {
            return Err(cant!("too many declarations for this packer"));
        }
        Ok(())
    }

    // The line forms read without the JSON parser (lines.rs, slice.rs): the
    // same encoding as `decl`, without building a `Decl`.
    pub fn thm(&mut self, name: u64, params: &[u64], ty: u64, v: u64, all: &[u64]) -> R<()> {
        self.check_decls()?;
        self.d_start();
        self.dhead(name, params, ty)?;
        self.dref(v, true)?;
        self.dnms(all)?;
        self.d_end(2);
        Ok(())
    }
    // hints: 0 opaque, 1 abbrev, 2 regular(h); safety 0 safe 1 unsafe 2 partial
    #[allow(clippy::too_many_arguments)]
    pub fn defn(
        &mut self,
        name: u64,
        params: &[u64],
        ty: u64,
        v: u64,
        hints: u8,
        h: u64,
        safety: u8,
        all: &[u64],
    ) -> R<()> {
        self.check_decls()?;
        self.d_start();
        self.dhead(name, params, ty)?;
        self.dref(v, false)?;
        self.dbyte(hints);
        if hints == 2 {
            self.dv(h);
        }
        self.dbyte(safety);
        self.dnms(all)?;
        self.d_end(1);
        Ok(())
    }

    fn head(&mut self, h: &Head) -> R<()> {
        self.dhead(h.name, &h.level_params, h.ty)
    }

    // A declaration (spec section 9: its fields in the order written).
    pub fn decl(&mut self, d: &Decl) -> R<()> {
        self.check_decls()?;
        self.d_start();
        let kind = match d {
            Decl::Axiom { head, is_unsafe } => {
                self.head(head)?;
                self.dbyte(*is_unsafe as u8);
                0
            }
            Decl::Def {
                head,
                value,
                hints,
                safety,
                all,
            } => {
                self.head(head)?;
                self.dref(*value, false)?;
                match hints {
                    Hints::Opaque => self.dbyte(0),
                    Hints::Abbrev => self.dbyte(1),
                    Hints::Regular(h) => {
                        self.dbyte(2);
                        self.dv(*h);
                    }
                }
                self.dbyte(match safety {
                    Safety::Safe => 0,
                    Safety::Unsafe => 1,
                    Safety::Partial => 2,
                });
                self.dnms(all)?;
                1
            }
            Decl::Thm { head, value, all } => {
                self.head(head)?;
                self.dref(*value, true)?;
                self.dnms(all)?;
                2
            }
            Decl::Opaque {
                head,
                value,
                is_unsafe,
                all,
            } => {
                self.head(head)?;
                self.dref(*value, false)?;
                self.dbyte(*is_unsafe as u8);
                self.dnms(all)?;
                3
            }
            Decl::Quot { head, kind } => {
                self.head(head)?;
                self.dbyte(match kind {
                    QuotKind::Type => 0,
                    QuotKind::Ctor => 1,
                    QuotKind::Lift => 2,
                    QuotKind::Ind => 3,
                });
                4
            }
            Decl::Inductive { types, ctors, recs } => {
                let flagged = types.first().is_some_and(|t| t.flags.is_some());
                if types.iter().any(|t| t.flags.is_some() != flagged) {
                    return Err(inv!(
                        "the types of an inductive block do not agree on carrying their flags"
                    ));
                }
                if self.needs_flags && !flagged && !types.is_empty() {
                    return Err(inv!(
                        "an inductive type without its flags in a format 3.2 export"
                    ));
                }
                self.dv(types.len() as u64);
                for t in types {
                    self.head(&t.head)?;
                    self.dbyte(t.is_unsafe as u8);
                    self.dv(t.num_params);
                    self.dv(t.num_indices);
                    self.dnms(&t.all)?;
                    self.dnms(&t.ctors)?;
                    self.dv(t.num_nested);
                    self.dbyte(t.is_rec as u8);
                    self.dbyte(t.is_reflexive as u8);
                    if let Some(f) = t.flags {
                        for x in f.to_array() {
                            self.dbyte(x as u8);
                        }
                    }
                }
                self.dv(ctors.len() as u64);
                for c in ctors {
                    self.head(&c.head)?;
                    self.dbyte(c.is_unsafe as u8);
                    let ind = self.nm(c.induct)?;
                    self.dv(ind as u64);
                    self.dv(c.cidx);
                    self.dv(c.num_params);
                    self.dv(c.num_fields);
                }
                self.dv(recs.len() as u64);
                for r in recs {
                    self.head(&r.head)?;
                    self.dbyte(r.is_unsafe as u8);
                    self.dnms(&r.all)?;
                    self.dv(r.num_params);
                    self.dv(r.num_indices);
                    self.dv(r.num_motives);
                    self.dv(r.num_minors);
                    self.dv(r.rules.len() as u64);
                    for x in &r.rules {
                        let c = self.nm(x.ctor)?;
                        self.dv(c as u64);
                        self.dv(x.nfields);
                        self.dref(x.rhs, false)?;
                    }
                    self.dbyte(r.k as u8);
                }
                if flagged {
                    7
                } else {
                    5
                }
            }
        };
        self.d_end(kind);
        Ok(())
    }

    // {"meta":M}: M is kept byte for byte (SOURCE). The object must be
    // written exactly so, without spaces around the one key, to be kept.
    pub fn header(&mut self, l: &[u8]) -> R<()> {
        std::str::from_utf8(l).map_err(|e| format!("not UTF-8: {e}"))?;
        let j = json::parse(l)?;
        let J::Obj(fs) = j else {
            return Err("the header is not an object".into());
        };
        let meta = json::obj(&fs, "meta")?;
        json::exact(&fs, &["meta"])?;
        let v = json::text(json::obj(meta, "format")?, "version")?;
        if !crate::format::version_supported(v) {
            return Err(cant!(
                "format version {} is not supported",
                String::from_utf8_lossy(v)
            ));
        }
        if !(l.starts_with(b"{\"meta\":") && l.ends_with(b"}")) {
            return Err(cant!("the header is not in the form {{\"meta\":...}}"));
        }
        self.needs_flags = crate::format::version_requires_flags(v);
        self.meta = l[8..l.len() - 1].to_vec();
        Ok(())
    }

    // A line parsed by the JSON parser: pack.av's obj.
    pub fn obj(&mut self, fs: &[(Vec<u8>, J)]) -> R<()> {
        if fs.len() == 1 {
            if let J::Obj(o) = &fs[0].1 {
                return self.decl_obj(&fs[0].0, o);
            }
        }
        if json::has(fs, "ie") {
            if fs.len() != 2 {
                return Err(cant!("an expression line takes exactly one kind"));
            }
            let ie = json::int(fs, "ie")?;
            self.er.fresh(ie, "expression")?;
            self.expr_obj(ie, fs)
        } else if json::has(fs, "in") {
            let i = json::int(fs, "in")?;
            self.nr.fresh(i, "name")?;
            if json::has(fs, "str") {
                json::exact(fs, &["in", "str"])?;
                let o = json::obj(fs, "str")?;
                json::exact(o, &["pre", "str"])?;
                let pre = json::int(o, "pre")?;
                let s = json::text(o, "str")?.to_vec();
                self.name_str(i, pre, &s)
            } else {
                json::exact(fs, &["in", "num"])?;
                let o = json::obj(fs, "num")?;
                json::exact(o, &["i", "pre"])?;
                let pre = json::int(o, "pre")?;
                let k = json::int(o, "i")?;
                self.name_num(i, pre, k)
            }
        } else if json::has(fs, "il") {
            let i = json::int(fs, "il")?;
            self.lr.fresh(i, "level")?;
            if fs.len() != 2 {
                return Err(cant!("a level line takes exactly one kind"));
            }
            if json::has(fs, "succ") {
                self.succ(i, json::int(fs, "succ")?)
            } else if json::has(fs, "param") {
                self.param(i, json::int(fs, "param")?)
            } else {
                let (xs, max) = if json::has(fs, "max") {
                    (json::ints(fs, "max")?, true)
                } else if json::has(fs, "imax") {
                    (json::ints(fs, "imax")?, false)
                } else {
                    return Err(cant!("unknown level kind"));
                };
                if xs.len() != 2 {
                    return Err("max and imax take exactly two levels".into());
                }
                self.pair(i, xs[0], xs[1], max)
            }
        } else {
            Err(cant!("unknown record kind"))
        }
    }

    fn expr_obj(&mut self, ie: u64, fs: &[(Vec<u8>, J)]) -> R<()> {
        if json::has(fs, "app") {
            let o = json::obj(fs, "app")?;
            json::exact(o, &["arg", "fn"])?;
            return self.app(ie, json::int(o, "fn")?, json::int(o, "arg")?);
        }
        for (key, lam) in [("lam", true), ("forallE", false)] {
            if json::has(fs, key) {
                let o = json::obj(fs, key)?;
                json::exact(o, &["binderInfo", "body", "name", "type"])?;
                let bi = binder_of(json::text(o, "binderInfo")?)?;
                return self.bind(
                    ie,
                    lam,
                    bi,
                    json::int(o, "name")?,
                    json::int(o, "type")?,
                    json::int(o, "body")?,
                );
            }
        }
        if json::has(fs, "bvar") {
            return self.bvar(ie, json::int(fs, "bvar")?);
        }
        if json::has(fs, "sort") {
            return self.sort(ie, json::int(fs, "sort")?);
        }
        if json::has(fs, "const") {
            let o = json::obj(fs, "const")?;
            json::exact(o, &["name", "us"])?;
            let n = json::int(o, "name")?;
            let us = json::ints(o, "us")?;
            return self.cnst(ie, n, &us);
        }
        if json::has(fs, "letE") {
            let o = json::obj(fs, "letE")?;
            json::exact(o, &["body", "name", "nondep", "type", "value"])?;
            json::boolean(o, "nondep")?;
            return self.let_e(
                ie,
                json::int(o, "name")?,
                json::int(o, "type")?,
                json::int(o, "value")?,
                json::int(o, "body")?,
            );
        }
        if json::has(fs, "natVal") {
            let d = json::text(fs, "natVal")?.to_vec();
            return self.nat(ie, &d);
        }
        if json::has(fs, "strVal") {
            let s = json::text(fs, "strVal")?.to_vec();
            return self.strv(ie, &s);
        }
        if json::has(fs, "proj") {
            let o = json::obj(fs, "proj")?;
            json::exact(o, &["idx", "struct", "typeName"])?;
            let st = json::int(o, "struct")?;
            let tn = json::int(o, "typeName")?;
            let idx = json::int(o, "idx")?;
            return self.proj(ie, tn, idx, st);
        }
        if json::has(fs, "mdata") {
            let o = json::obj(fs, "mdata")?;
            // lean4export writes `data`; other exporters (olean-export) leave it
            // out, and it is dropped either way (spec 9.1)
            json::only(o, &["data", "expr"])?;
            return self.mdata(ie, json::int(o, "expr")?);
        }
        Err(cant!("unknown expression kind"))
    }

    fn head_obj(o: &[(Vec<u8>, J)]) -> R<Head> {
        Ok(Head {
            name: json::int(o, "name")?,
            level_params: json::ints(o, "levelParams")?,
            ty: json::int(o, "type")?,
        })
    }

    pub(crate) fn decl_obj(&mut self, k: &[u8], o: &[(Vec<u8>, J)]) -> R<()> {
        self.check_decls()?;
        let d = match k {
            b"axiom" => {
                json::exact(o, &["isUnsafe", "levelParams", "name", "type"])?;
                Decl::Axiom {
                    head: Self::head_obj(o)?,
                    is_unsafe: json::boolean(o, "isUnsafe")?,
                }
            }
            b"def" => {
                json::exact(
                    o,
                    &[
                        "all",
                        "hints",
                        "levelParams",
                        "name",
                        "safety",
                        "type",
                        "value",
                    ],
                )?;
                let hints = match json::need(o, "hints")? {
                    J::Str(s) if s.as_slice() == b"opaque" => Hints::Opaque,
                    J::Str(s) if s.as_slice() == b"abbrev" => Hints::Abbrev,
                    J::Obj(fs) => {
                        json::exact(fs, &["regular"])?;
                        Hints::Regular(json::int(fs, "regular")?)
                    }
                    J::Str(_) => return Err(cant!("unknown hints")),
                    _ => return Err("malformed hints".into()),
                };
                let safety = match json::text(o, "safety")? {
                    b"safe" => Safety::Safe,
                    b"unsafe" => Safety::Unsafe,
                    b"partial" => Safety::Partial,
                    x => return Err(cant!("unknown safety '{}'", String::from_utf8_lossy(x))),
                };
                Decl::Def {
                    head: Self::head_obj(o)?,
                    value: json::int(o, "value")?,
                    hints,
                    safety,
                    all: json::ints(o, "all")?,
                }
            }
            b"thm" => {
                json::exact(o, &["all", "levelParams", "name", "type", "value"])?;
                Decl::Thm {
                    head: Self::head_obj(o)?,
                    value: json::int(o, "value")?,
                    all: json::ints(o, "all")?,
                }
            }
            b"opaque" => {
                json::exact(
                    o,
                    &["all", "isUnsafe", "levelParams", "name", "type", "value"],
                )?;
                Decl::Opaque {
                    head: Self::head_obj(o)?,
                    value: json::int(o, "value")?,
                    is_unsafe: json::boolean(o, "isUnsafe")?,
                    all: json::ints(o, "all")?,
                }
            }
            b"quot" => {
                json::exact(o, &["kind", "levelParams", "name", "type"])?;
                let kind = match json::text(o, "kind")? {
                    b"type" => QuotKind::Type,
                    b"ctor" => QuotKind::Ctor,
                    b"lift" => QuotKind::Lift,
                    b"ind" => QuotKind::Ind,
                    x => return Err(cant!("unknown quot kind '{}'", String::from_utf8_lossy(x))),
                };
                Decl::Quot {
                    head: Self::head_obj(o)?,
                    kind,
                }
            }
            b"inductive" => {
                json::exact(o, &["ctors", "recs", "types"])?;
                let mut types = Vec::new();
                for t in json::arr(o, "types")? {
                    let J::Obj(t) = t else {
                        return Err("expected an object".into());
                    };
                    const BASE: [&str; 11] = [
                        "all",
                        "ctors",
                        "isRec",
                        "isReflexive",
                        "isUnsafe",
                        "levelParams",
                        "name",
                        "numIndices",
                        "numNested",
                        "numParams",
                        "type",
                    ];
                    // the flags of lean4export 3.2: all five or none
                    let fk = IndFlags::KEYS;
                    let flags = if fk.iter().any(|k| json::has(t, k)) {
                        let mut keys = BASE.to_vec();
                        keys.extend_from_slice(&fk);
                        json::exact(t, &keys)?;
                        let mut a = [false; 5];
                        for (x, k) in a.iter_mut().zip(fk) {
                            *x = json::boolean(t, k)?;
                        }
                        Some(IndFlags::from_array(a))
                    } else {
                        json::exact(t, &BASE)?;
                        None
                    };
                    types.push(IndType {
                        head: Self::head_obj(t)?,
                        is_unsafe: json::boolean(t, "isUnsafe")?,
                        num_params: json::int(t, "numParams")?,
                        num_indices: json::int(t, "numIndices")?,
                        all: json::ints(t, "all")?,
                        ctors: json::ints(t, "ctors")?,
                        num_nested: json::int(t, "numNested")?,
                        is_rec: json::boolean(t, "isRec")?,
                        is_reflexive: json::boolean(t, "isReflexive")?,
                        flags,
                    });
                }
                let mut ctors = Vec::new();
                for c in json::arr(o, "ctors")? {
                    let J::Obj(c) = c else {
                        return Err("expected an object".into());
                    };
                    json::exact(
                        c,
                        &[
                            "cidx",
                            "induct",
                            "isUnsafe",
                            "levelParams",
                            "name",
                            "numFields",
                            "numParams",
                            "type",
                        ],
                    )?;
                    ctors.push(IndCtor {
                        head: Self::head_obj(c)?,
                        is_unsafe: json::boolean(c, "isUnsafe")?,
                        induct: json::int(c, "induct")?,
                        cidx: json::int(c, "cidx")?,
                        num_params: json::int(c, "numParams")?,
                        num_fields: json::int(c, "numFields")?,
                    });
                }
                let mut recs = Vec::new();
                for r in json::arr(o, "recs")? {
                    let J::Obj(r) = r else {
                        return Err("expected an object".into());
                    };
                    json::exact(
                        r,
                        &[
                            "all",
                            "isUnsafe",
                            "k",
                            "levelParams",
                            "name",
                            "numIndices",
                            "numMinors",
                            "numMotives",
                            "numParams",
                            "rules",
                            "type",
                        ],
                    )?;
                    let mut rules = Vec::new();
                    for x in json::arr(r, "rules")? {
                        let J::Obj(x) = x else {
                            return Err("expected an object".into());
                        };
                        json::exact(x, &["ctor", "nfields", "rhs"])?;
                        rules.push(IndRule {
                            ctor: json::int(x, "ctor")?,
                            nfields: json::int(x, "nfields")?,
                            rhs: json::int(x, "rhs")?,
                        });
                    }
                    recs.push(IndRec {
                        head: Self::head_obj(r)?,
                        is_unsafe: json::boolean(r, "isUnsafe")?,
                        all: json::ints(r, "all")?,
                        num_params: json::int(r, "numParams")?,
                        num_indices: json::int(r, "numIndices")?,
                        num_motives: json::int(r, "numMotives")?,
                        num_minors: json::int(r, "numMinors")?,
                        rules,
                        k: json::boolean(r, "k")?,
                    });
                }
                Decl::Inductive { types, ctors, recs }
            }
            _ => {
                return Err(cant!(
                    "unknown declaration kind '{}'",
                    String::from_utf8_lossy(k)
                ))
            }
        };
        self.decl(&d)
    }
}
