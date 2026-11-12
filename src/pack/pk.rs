// The packer's state while reading lines: tables of ids (Ren), the columns
// of expressions, the stream of other records, names made canonical, owners
// seeded by declarations.

use super::json::{self, J};
use super::{cant, inv, R};
use crate::canon::Canon;
use std::collections::HashMap;

pub const NONE: u32 = 0x3FFF_FFFF;
pub const MAIN: u32 = 1 << 30;
pub const FLAG: u32 = 1 << 31;
pub const LOW: u32 = MAIN - 1;

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

#[derive(Clone, Copy)]
#[repr(C)]
pub struct Col {
    pub k: u32,
    pub a: u32,
    pub b: u32,
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
    // the columns: one allocation for every expression the file can hold
    // (a line takes at least 16 bytes), written at the expression's id;
    // workers share one and write at global ids
    pub cols: Vec<Col>,
    pub colp: *mut Col,
    pub colcap: u64,
    pub xbuf: Vec<u8>,
    pub xbufs: Vec<Vec<u8>>,
    pub canon: Vec<u32>,
    pub cn: Canon,
    pub owner: Vec<u32>,
    pub meta: Vec<u8>,
    // parsing a range on a worker: no owners or canonical names made here
    pub worker: bool,
    pub fl: bool,
    pub xid: u32,
    // per declaration: its kind, the number of names it declares, those
    // names (dense name ids)
    pub dmeta: Vec<u32>,
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
            cols: Vec::new(),
            colp: std::ptr::null_mut(),
            colcap: 0,
            xbuf: Vec::with_capacity(size_hint / 256 + 1024),
            xbufs: Vec::new(),
            canon: {
                let mut v = Vec::with_capacity(size_hint / 400 + 16);
                v.push(0);
                v
            },
            cn: Canon::new(),
            owner: Vec::new(),
            meta: Vec::new(),
            worker: false,
            fl: false,
            xid: 0,
            dmeta: Vec::new(),
            draw: Vec::new(),
            dpieces: Vec::new(),
            dnames: Vec::new(),
            drefs: Vec::new(),
        }
    }

    pub fn new_worker(size_hint: usize, xid: u32) -> Pk {
        let mut pk = Pk::new(size_hint);
        pk.worker = true;
        pk.fl = true;
        pk.xid = xid;
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
            self.stream.push(20);
            wv(&mut self.stream, self.run as u64);
            self.run = 0;
        }
    }
    // Columns of their own, for one worker or none.
    pub fn own_cols(&mut self, size: usize) {
        let cap = size / 16 + 16;
        self.cols = Vec::with_capacity(cap);
        self.colp = self.cols.as_mut_ptr();
        self.colcap = cap as u64;
    }
    pub fn flush_run_pub(&mut self) {
        self.flush_run();
    }
    pub fn finish(&mut self) {
        self.flush_run();
        self.owner.resize(self.exprs as usize, NONE);
        unsafe {
            self.cols.set_len(self.exprs as usize);
        }
    }

    #[inline(always)]
    fn new_expr(&mut self, ie: u64, k: u32, a: u32, b: u32) -> R<()> {
        if self.er.floating {
            if ie >= u32::MAX as u64 {
                return Err(cant!("expression id out of range for a worker"));
            }
            self.exprs = ie as u32;
            self.er.define(ie, ie as u32, "expression")?;
            self.refl();
            self.er.below = ie;
        }
        let e = self.exprs;
        if e == u32::MAX {
            return Err(cant!("too many expressions"));
        }
        self.er.define(ie, e, "expression")?;
        if e as u64 >= self.colcap {
            return Err(cant!("more expressions than the file can hold"));
        }
        unsafe {
            self.colp.add(e as usize).write(Col { k, a, b });
        }
        self.exprs = e + 1;
        self.run += 1;
        Ok(())
    }
    #[inline(always)]
    fn xstart(&mut self, ie: u64) -> R<u32> {
        self.er.fresh(ie, "expression")?;
        let off = self.xbuf.len();
        if off > u32::MAX as usize - 1 {
            return Err(cant!("too many literal bytes for this packer"));
        }
        Ok(off as u32)
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
        let off = self.xstart(ie)?;
        self.xbuf.push(7);
        wv(&mut self.xbuf, k);
        self.new_expr(ie, 0, off, self.xid)
    }
    pub fn sort(&mut self, ie: u64, l: u64) -> R<()> {
        let off = self.xstart(ie)?;
        let kl = self.lv(l)?;
        self.xbuf.push(8);
        wv(&mut self.xbuf, kl as u64);
        self.new_expr(ie, 0, off, self.xid)
    }
    pub fn cnst(&mut self, ie: u64, n: u64, us: &[u64]) -> R<()> {
        let off = self.xstart(ie)?;
        let nn = self.nm(n)?;
        self.xbuf.push(9);
        wv(&mut self.xbuf, nn as u64);
        wv(&mut self.xbuf, us.len() as u64);
        for &u in us {
            let l = self.lv(u)?;
            wv(&mut self.xbuf, l as u64);
        }
        self.new_expr(ie, 0, off, self.xid)
    }
    pub fn let_e(&mut self, ie: u64, n: u64, t: u64, v: u64, b: u64) -> R<()> {
        let off = self.xstart(ie)?;
        let nn = self.nm(n)?;
        let (kt, kv, kb) = (self.eref(t)?, self.eref(v)?, self.eref(b)?);
        self.xbuf.push(13);
        for x in [nn, kt, kv, kb] {
            wv(&mut self.xbuf, x as u64);
        }
        self.new_expr(ie, 0, off, self.xid)
    }
    pub fn nat(&mut self, ie: u64, digits: &[u8]) -> R<()> {
        let off = self.xstart(ie)?;
        if digits.first() == Some(&b'-') {
            return Err("negative Nat literal".into());
        }
        let Some(bytes) = crate::format::nat_from_decimal(digits) else {
            return Err("malformed Nat literal".into());
        };
        self.xbuf.push(14);
        wv(&mut self.xbuf, bytes.len() as u64);
        self.xbuf.extend_from_slice(&bytes);
        self.new_expr(ie, 0, off, self.xid)
    }
    pub fn strv(&mut self, ie: u64, s: &[u8]) -> R<()> {
        let off = self.xstart(ie)?;
        self.xbuf.push(15);
        wv(&mut self.xbuf, s.len() as u64);
        self.xbuf.extend_from_slice(s);
        self.new_expr(ie, 0, off, self.xid)
    }
    pub fn proj(&mut self, ie: u64, tn: u64, idx: u64, st: u64) -> R<()> {
        let off = self.xstart(ie)?;
        let ks = self.eref(st)?;
        let nn = self.nm(tn)?;
        self.xbuf.push(16);
        wv(&mut self.xbuf, nn as u64);
        wv(&mut self.xbuf, idx);
        wv(&mut self.xbuf, ks as u64);
        self.new_expr(ie, 0, off, self.xid)
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
            json::exact(o, &["data", "expr"])?;
            return self.mdata(ie, json::int(o, "expr")?);
        }
        Err(cant!("unknown expression kind"))
    }

    fn head_obj(&mut self, o: &[(Vec<u8>, J)]) -> R<()> {
        let name = json::int(o, "name")?;
        let ps = json::ints(o, "levelParams")?;
        let ty = json::int(o, "type")?;
        self.dhead(name, &ps, ty)
    }

    fn decl_obj(&mut self, k: &[u8], o: &[(Vec<u8>, J)]) -> R<()> {
        self.check_decls()?;
        match k {
            b"axiom" => {
                json::exact(o, &["isUnsafe", "levelParams", "name", "type"])?;
                self.d_start();
                self.head_obj(o)?;
                let u = json::boolean(o, "isUnsafe")?;
                self.dbyte(u as u8);
                self.d_end(0);
                Ok(())
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
                let (hk, h) = match json::need(o, "hints")? {
                    J::Str(s) if s.as_slice() == b"opaque" => (0u8, 0u64),
                    J::Str(s) if s.as_slice() == b"abbrev" => (1, 0),
                    J::Obj(fs) => {
                        json::exact(fs, &["regular"])?;
                        (2, json::int(fs, "regular")?)
                    }
                    J::Str(_) => return Err(cant!("unknown hints")),
                    _ => return Err("malformed hints".into()),
                };
                let s = match json::text(o, "safety")? {
                    b"safe" => 0u8,
                    b"unsafe" => 1,
                    b"partial" => 2,
                    x => return Err(cant!("unknown safety '{}'", String::from_utf8_lossy(x))),
                };
                let name = json::int(o, "name")?;
                let ps = json::ints(o, "levelParams")?;
                let ty = json::int(o, "type")?;
                let v = json::int(o, "value")?;
                let all = json::ints(o, "all")?;
                self.defn(name, &ps, ty, v, hk, h, s, &all)
            }
            b"thm" => {
                json::exact(o, &["all", "levelParams", "name", "type", "value"])?;
                let name = json::int(o, "name")?;
                let ps = json::ints(o, "levelParams")?;
                let ty = json::int(o, "type")?;
                let v = json::int(o, "value")?;
                let all = json::ints(o, "all")?;
                self.thm(name, &ps, ty, v, &all)
            }
            b"opaque" => {
                json::exact(
                    o,
                    &["all", "isUnsafe", "levelParams", "name", "type", "value"],
                )?;
                self.d_start();
                self.head_obj(o)?;
                self.dref(json::int(o, "value")?, false)?;
                let u = json::boolean(o, "isUnsafe")?;
                self.dbyte(u as u8);
                let all = json::ints(o, "all")?;
                self.dnms(&all)?;
                self.d_end(3);
                Ok(())
            }
            b"quot" => {
                json::exact(o, &["kind", "levelParams", "name", "type"])?;
                self.d_start();
                self.head_obj(o)?;
                let kb = match json::text(o, "kind")? {
                    b"type" => 0u8,
                    b"ctor" => 1,
                    b"lift" => 2,
                    b"ind" => 3,
                    x => return Err(cant!("unknown quot kind '{}'", String::from_utf8_lossy(x))),
                };
                self.dbyte(kb);
                self.d_end(4);
                Ok(())
            }
            b"inductive" => {
                json::exact(o, &["ctors", "recs", "types"])?;
                let ts = json::arr(o, "types")?;
                let cs = json::arr(o, "ctors")?;
                let rs = json::arr(o, "recs")?;
                self.d_start();
                self.dv(ts.len() as u64);
                for t in ts {
                    let J::Obj(t) = t else {
                        return Err("expected an object".into());
                    };
                    json::exact(
                        t,
                        &[
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
                        ],
                    )?;
                    self.head_obj(t)?;
                    let u = json::boolean(t, "isUnsafe")?;
                    self.dbyte(u as u8);
                    self.dv(json::int(t, "numParams")?);
                    self.dv(json::int(t, "numIndices")?);
                    self.dnms(&json::ints(t, "all")?)?;
                    self.dnms(&json::ints(t, "ctors")?)?;
                    self.dv(json::int(t, "numNested")?);
                    let r = json::boolean(t, "isRec")?;
                    let f = json::boolean(t, "isReflexive")?;
                    self.dbyte(r as u8);
                    self.dbyte(f as u8);
                }
                self.dv(cs.len() as u64);
                for c in cs {
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
                    self.head_obj(c)?;
                    let u = json::boolean(c, "isUnsafe")?;
                    self.dbyte(u as u8);
                    let ind = self.nm(json::int(c, "induct")?)?;
                    self.dv(ind as u64);
                    self.dv(json::int(c, "cidx")?);
                    self.dv(json::int(c, "numParams")?);
                    self.dv(json::int(c, "numFields")?);
                }
                self.dv(rs.len() as u64);
                for r in rs {
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
                    self.head_obj(r)?;
                    let u = json::boolean(r, "isUnsafe")?;
                    self.dbyte(u as u8);
                    self.dnms(&json::ints(r, "all")?)?;
                    self.dv(json::int(r, "numParams")?);
                    self.dv(json::int(r, "numIndices")?);
                    self.dv(json::int(r, "numMotives")?);
                    self.dv(json::int(r, "numMinors")?);
                    let rules = json::arr(r, "rules")?;
                    self.dv(rules.len() as u64);
                    for x in rules {
                        let J::Obj(x) = x else {
                            return Err("expected an object".into());
                        };
                        json::exact(x, &["ctor", "nfields", "rhs"])?;
                        let c = self.nm(json::int(x, "ctor")?)?;
                        self.dv(c as u64);
                        self.dv(json::int(x, "nfields")?);
                        self.dref(json::int(x, "rhs")?, false)?;
                    }
                    let k = json::boolean(r, "k")?;
                    self.dbyte(k as u8);
                }
                self.d_end(5);
                Ok(())
            }
            _ => Err(cant!(
                "unknown declaration kind '{}'",
                String::from_utf8_lossy(k)
            )),
        }
    }
}
