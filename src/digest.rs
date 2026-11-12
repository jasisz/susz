//! A digest of the declarations a file holds: every declaration in order,
//! with names, levels and expressions hashed by structure (so ids, layout,
//! proof blocks, `mdata` and `letE.nondep` do not count, spec 9.1). Computed
//! from a Susz file ([`of_susz`]) and from an ndjson export ([`of_ndjson`]),
//! for differential tests.

use crate::format;
use crate::pack::json::{self, J};
use crate::read::{
    Block, Component, Decl, Event, Expr, Failure, File, Head, Hints, Ids, Level, Ref,
};
use std::collections::HashMap;
use std::io::BufRead;

#[inline]
fn mix(h: u64, x: u64) -> u64 {
    let v = (h ^ x).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    v ^ (v >> 29)
}

/// Hash of a tag and parts.
pub fn h(tag: u64, parts: &[u64]) -> u64 {
    let mut x = mix(0xcbf2_9ce4_8422_2325, tag);
    for &p in parts {
        x = mix(x, p);
    }
    mix(x, parts.len() as u64)
}

/// Hash of bytes.
pub fn hb(b: &[u8]) -> u64 {
    let mut x = 0xcbf2_9ce4_8422_2325u64;
    for &c in b {
        x = (x ^ c as u64).wrapping_mul(0x100_0000_01b3);
    }
    mix(x, b.len() as u64)
}

pub const ANON: u64 = 0x5155_5a53_0000_0000;
pub const ZERO: u64 = 0x5155_5a53_0000_0001;

fn hints_h(hk: u64, height: u64) -> u64 {
    h(100 + hk, &[height])
}

/// The digest of a Susz file (after a successful full check, or the first
/// structural error).
pub fn of_susz(bytes: &[u8]) -> Result<u64, Failure> {
    let f = File::open(bytes)?;
    let mut m = f.main();
    let mut names: Vec<u64> = vec![ANON];
    let mut levels: Vec<u64> = vec![ZERO];
    let mut exprs: Vec<u64> = Vec::new();
    let mut acc = h(0, &[]);
    let lst = |ids: &Ids, t: &[u64]| -> Vec<u64> { ids.iter().map(|x| t[x as usize]).collect() };
    while let Some(ev) = m.next() {
        match ev? {
            Event::Name { prefix, part, .. } => {
                let p = names[prefix as usize];
                names.push(match part {
                    Component::Str(s) => h(1, &[p, hb(s.as_bytes())]),
                    Component::Num(k) => h(2, &[p, k]),
                });
            }
            Event::Level { level, .. } => levels.push(level_h(level, &levels, &names)),
            Event::Expr { expr, .. } => {
                let e = expr_h(&expr, &names, &levels, &exprs, &[]);
                exprs.push(e);
            }
            Event::Frontier { .. } => {}
            Event::Decl { decl, .. } => {
                let head = |hd: &Head| -> Vec<u64> {
                    let mut v = vec![names[hd.name as usize], exprs[hd.ty as usize]];
                    v.extend(lst(&hd.params, &names));
                    v
                };
                let d = match &decl {
                    Decl::Axiom {
                        head: hd,
                        is_unsafe,
                    } => h(10, &[h(0, &head(hd)), *is_unsafe as u64]),
                    Decl::Defn {
                        head: hd,
                        value,
                        hints,
                        safety,
                        all,
                    } => {
                        let hh = match hints {
                            Hints::Opaque => hints_h(0, 0),
                            Hints::Abbrev => hints_h(1, 0),
                            Hints::Regular(k) => hints_h(2, *k),
                        };
                        h(
                            11,
                            &[
                                h(0, &head(hd)),
                                exprs[*value as usize],
                                hh,
                                *safety as u64,
                                h(0, &lst(all, &names)),
                            ],
                        )
                    }
                    Decl::Thm {
                        head: hd,
                        value,
                        all,
                    } => h(
                        12,
                        &[
                            h(0, &head(hd)),
                            exprs[*value as usize],
                            h(0, &lst(all, &names)),
                        ],
                    ),
                    Decl::ThmBlock {
                        head: hd,
                        block,
                        all,
                    } => {
                        let mut local: Vec<u64> = Vec::with_capacity(block.exprs as usize);
                        for r in Block::new(bytes, m.state(), *block) {
                            let (_, e) = r?;
                            let x = expr_h(&e, &names, &levels, &exprs, &local);
                            local.push(x);
                        }
                        h(
                            12,
                            &[
                                h(0, &head(hd)),
                                *local.last().unwrap(),
                                h(0, &lst(all, &names)),
                            ],
                        )
                    }
                    Decl::Opaque {
                        head: hd,
                        value,
                        is_unsafe,
                        all,
                    } => h(
                        13,
                        &[
                            h(0, &head(hd)),
                            exprs[*value as usize],
                            *is_unsafe as u64,
                            h(0, &lst(all, &names)),
                        ],
                    ),
                    Decl::Quot { head: hd, kind } => h(14, &[h(0, &head(hd)), *kind as u64]),
                    Decl::Inductive(ind) => {
                        let mut parts = Vec::new();
                        for t in &ind.types {
                            parts.push(h(
                                20,
                                &[
                                    h(0, &head(&t.head)),
                                    t.is_unsafe as u64,
                                    t.num_params,
                                    t.num_indices,
                                    h(0, &lst(&t.all, &names)),
                                    h(0, &lst(&t.ctors, &names)),
                                    t.num_nested,
                                    t.is_rec as u64,
                                    t.is_reflexive as u64,
                                ],
                            ));
                        }
                        for c in &ind.ctors {
                            parts.push(h(
                                21,
                                &[
                                    h(0, &head(&c.head)),
                                    c.is_unsafe as u64,
                                    names[c.induct as usize],
                                    c.cidx,
                                    c.num_params,
                                    c.num_fields,
                                ],
                            ));
                        }
                        for r in &ind.recs {
                            let rules: Vec<u64> = r
                                .rules
                                .iter()
                                .map(|x| {
                                    h(
                                        23,
                                        &[names[x.ctor as usize], x.nfields, exprs[x.rhs as usize]],
                                    )
                                })
                                .collect();
                            parts.push(h(
                                22,
                                &[
                                    h(0, &head(&r.head)),
                                    r.is_unsafe as u64,
                                    h(0, &lst(&r.all, &names)),
                                    r.num_params,
                                    r.num_indices,
                                    r.num_motives,
                                    r.num_minors,
                                    h(0, &rules),
                                    r.k as u64,
                                ],
                            ));
                        }
                        h(
                            15,
                            &[
                                ind.types.len() as u64,
                                ind.ctors.len() as u64,
                                ind.recs.len() as u64,
                                h(0, &parts),
                            ],
                        )
                    }
                };
                acc = mix(acc, d);
            }
        }
    }
    Ok(acc)
}

fn level_h(l: Level, levels: &[u64], names: &[u64]) -> u64 {
    match l {
        Level::Succ(a) => h(3, &[levels[a as usize]]),
        Level::Max(a, b) => h(4, &[levels[a as usize], levels[b as usize]]),
        Level::IMax(a, b) => h(5, &[levels[a as usize], levels[b as usize]]),
        Level::Param(n) => h(6, &[names[n as usize]]),
    }
}

fn expr_h(e: &Expr, names: &[u64], levels: &[u64], exprs: &[u64], local: &[u64]) -> u64 {
    let r = |x: &Ref| match x {
        Ref::Main(i) => exprs[*i as usize],
        Ref::Block(k) => local[*k as usize],
    };
    match e {
        Expr::BVar(i) => h(7, &[*i]),
        Expr::Sort(l) => h(8, &[levels[*l as usize]]),
        Expr::Const(n, us) => {
            let mut v = vec![names[*n as usize]];
            v.extend(us.iter().map(|u| levels[u as usize]));
            h(9, &v)
        }
        Expr::App(f, a) => h(10, &[r(f), r(a)]),
        Expr::Lam(bi, n, t, b) => h(11, &[*bi as u64, names[*n as usize], r(t), r(b)]),
        Expr::Pi(bi, n, t, b) => h(12, &[*bi as u64, names[*n as usize], r(t), r(b)]),
        Expr::Let(n, t, v, b) => h(13, &[names[*n as usize], r(t), r(v), r(b)]),
        Expr::Nat(b) => h(14, &[hb(b)]),
        Expr::Str(s) => h(15, &[hb(s.as_bytes())]),
        Expr::Proj(n, i, x) => h(16, &[names[*n as usize], *i, r(x)]),
    }
}

/// The digest of an ndjson export, read line by line with a plain JSON
/// parser (independently of the packer's fast paths and tables).
pub fn of_ndjson(path: &str) -> Result<u64, String> {
    let f = std::fs::File::open(path).map_err(|e| e.to_string())?;
    let rd = std::io::BufReader::with_capacity(1 << 20, f);
    let mut names: HashMap<u64, u64> = HashMap::new();
    let mut levels: HashMap<u64, u64> = HashMap::new();
    let mut exprs: HashMap<u64, u64> = HashMap::new();
    names.insert(0, ANON);
    levels.insert(0, ZERO);
    let mut acc = h(0, &[]);
    for (ln, line) in rd.split(b'\n').enumerate() {
        let line = line.map_err(|e| e.to_string())?;
        if ln == 0 || line.is_empty() {
            continue;
        }
        let err = |m: String| format!("line {}: {m}", ln + 1);
        let J::Obj(fs) = json::parse(&line).map_err(|e| err(e.msg))? else {
            return Err(err("not an object".into()));
        };
        let int = |o: &[(Vec<u8>, J)], k: &str| json::int(o, k).map_err(|e| err(e.msg));
        let get = |t: &HashMap<u64, u64>, i: u64| {
            t.get(&i)
                .copied()
                .ok_or_else(|| err(format!("unknown id {i}")))
        };
        if json::has(&fs, "in") {
            let i = int(&fs, "in")?;
            let v = if let Ok(o) = json::obj(&fs, "str") {
                h(
                    1,
                    &[
                        get(&names, int(o, "pre")?)?,
                        hb(json::text(o, "str").map_err(|e| err(e.msg))?),
                    ],
                )
            } else {
                let o = json::obj(&fs, "num").map_err(|e| err(e.msg))?;
                h(2, &[get(&names, int(o, "pre")?)?, int(o, "i")?])
            };
            names.insert(i, v);
        } else if json::has(&fs, "il") {
            let i = int(&fs, "il")?;
            let v = if json::has(&fs, "succ") {
                h(3, &[get(&levels, int(&fs, "succ")?)?])
            } else if json::has(&fs, "param") {
                h(6, &[get(&names, int(&fs, "param")?)?])
            } else {
                let (k, t) = if json::has(&fs, "max") {
                    ("max", 4)
                } else {
                    ("imax", 5)
                };
                let xs = json::ints(&fs, k).map_err(|e| err(e.msg))?;
                h(t, &[get(&levels, xs[0])?, get(&levels, xs[1])?])
            };
            levels.insert(i, v);
        } else if json::has(&fs, "ie") {
            let i = int(&fs, "ie")?;
            let (k, val) = fs
                .iter()
                .find(|(k, _)| k.as_slice() != b"ie")
                .ok_or_else(|| err("no kind".into()))?;
            let o: &[(Vec<u8>, J)] = match val {
                J::Obj(o) => o,
                _ => &[],
            };
            let e = |x: u64| get(&exprs, x);
            let v = match k.as_slice() {
                b"bvar" => h(7, &[int(&fs, "bvar")?]),
                b"sort" => h(8, &[get(&levels, int(&fs, "sort")?)?]),
                b"const" => {
                    let mut v = vec![get(&names, int(o, "name")?)?];
                    for u in json::ints(o, "us").map_err(|e| err(e.msg))? {
                        v.push(get(&levels, u)?);
                    }
                    h(9, &v)
                }
                b"app" => h(10, &[e(int(o, "fn")?)?, e(int(o, "arg")?)?]),
                b"lam" | b"forallE" => {
                    let bi = match json::text(o, "binderInfo").map_err(|e| err(e.msg))? {
                        b"default" => 0,
                        b"implicit" => 1,
                        b"strictImplicit" => 2,
                        _ => 3,
                    };
                    h(
                        if k.as_slice() == b"lam" { 11 } else { 12 },
                        &[
                            bi,
                            get(&names, int(o, "name")?)?,
                            e(int(o, "type")?)?,
                            e(int(o, "body")?)?,
                        ],
                    )
                }
                b"letE" => h(
                    13,
                    &[
                        get(&names, int(o, "name")?)?,
                        e(int(o, "type")?)?,
                        e(int(o, "value")?)?,
                        e(int(o, "body")?)?,
                    ],
                ),
                b"natVal" => {
                    let d = json::text(&fs, "natVal").map_err(|e| err(e.msg))?;
                    h(
                        14,
                        &[hb(
                            &format::nat_from_decimal(d).ok_or_else(|| err("bad natVal".into()))?
                        )],
                    )
                }
                b"strVal" => h(
                    15,
                    &[hb(json::text(&fs, "strVal").map_err(|e| err(e.msg))?)],
                ),
                b"proj" => h(
                    16,
                    &[
                        get(&names, int(o, "typeName")?)?,
                        int(o, "idx")?,
                        e(int(o, "struct")?)?,
                    ],
                ),
                b"mdata" => e(int(o, "expr")?)?,
                _ => return Err(err("unknown expression kind".into())),
            };
            exprs.insert(i, v);
        } else {
            let (k, val) = &fs[0];
            let J::Obj(o) = val else {
                return Err(err("bad declaration".into()));
            };
            let o: &[(Vec<u8>, J)] = o;
            let nl = |o: &[(Vec<u8>, J)], key: &str| -> Result<u64, String> {
                let mut v = Vec::new();
                for x in json::ints(o, key).map_err(|e| err(e.msg))? {
                    v.push(get(&names, x)?);
                }
                Ok(h(0, &v))
            };
            let head = |o: &[(Vec<u8>, J)]| -> Result<u64, String> {
                let mut v = vec![get(&names, int(o, "name")?)?, get(&exprs, int(o, "type")?)?];
                for x in json::ints(o, "levelParams").map_err(|e| err(e.msg))? {
                    v.push(get(&names, x)?);
                }
                Ok(h(0, &v))
            };
            let boolean = |o: &[(Vec<u8>, J)], key: &str| {
                json::boolean(o, key)
                    .map(|b| b as u64)
                    .map_err(|e| err(e.msg))
            };
            let d = match k.as_slice() {
                b"axiom" => h(10, &[head(o)?, boolean(o, "isUnsafe")?]),
                b"def" => {
                    let hh = match json::need(o, "hints").map_err(|e| err(e.msg))? {
                        J::Str(s) if s.as_slice() == b"opaque" => hints_h(0, 0),
                        J::Str(s) if s.as_slice() == b"abbrev" => hints_h(1, 0),
                        J::Obj(r) => hints_h(2, int(r, "regular")?),
                        _ => return Err(err("bad hints".into())),
                    };
                    let s = match json::text(o, "safety").map_err(|e| err(e.msg))? {
                        b"safe" => 0,
                        b"unsafe" => 1,
                        _ => 2,
                    };
                    h(
                        11,
                        &[
                            head(o)?,
                            get(&exprs, int(o, "value")?)?,
                            hh,
                            s,
                            nl(o, "all")?,
                        ],
                    )
                }
                b"thm" => h(
                    12,
                    &[head(o)?, get(&exprs, int(o, "value")?)?, nl(o, "all")?],
                ),
                b"opaque" => h(
                    13,
                    &[
                        head(o)?,
                        get(&exprs, int(o, "value")?)?,
                        boolean(o, "isUnsafe")?,
                        nl(o, "all")?,
                    ],
                ),
                b"quot" => {
                    let kd = match json::text(o, "kind").map_err(|e| err(e.msg))? {
                        b"type" => 0,
                        b"ctor" => 1,
                        b"lift" => 2,
                        _ => 3,
                    };
                    h(14, &[head(o)?, kd])
                }
                b"inductive" => {
                    let arr = |key: &str| json::arr(o, key).map_err(|e| err(e.msg));
                    let mut parts = Vec::new();
                    let (ts, cs, rs) = (arr("types")?, arr("ctors")?, arr("recs")?);
                    for t in ts {
                        let J::Obj(t) = t else {
                            return Err(err("bad type".into()));
                        };
                        parts.push(h(
                            20,
                            &[
                                head(t)?,
                                boolean(t, "isUnsafe")?,
                                int(t, "numParams")?,
                                int(t, "numIndices")?,
                                nl(t, "all")?,
                                nl(t, "ctors")?,
                                int(t, "numNested")?,
                                boolean(t, "isRec")?,
                                boolean(t, "isReflexive")?,
                            ],
                        ));
                    }
                    for c in cs {
                        let J::Obj(c) = c else {
                            return Err(err("bad ctor".into()));
                        };
                        parts.push(h(
                            21,
                            &[
                                head(c)?,
                                boolean(c, "isUnsafe")?,
                                get(&names, int(c, "induct")?)?,
                                int(c, "cidx")?,
                                int(c, "numParams")?,
                                int(c, "numFields")?,
                            ],
                        ));
                    }
                    for r in rs {
                        let J::Obj(r) = r else {
                            return Err(err("bad rec".into()));
                        };
                        let mut rules = Vec::new();
                        for x in json::arr(r, "rules").map_err(|e| err(e.msg))? {
                            let J::Obj(x) = x else {
                                return Err(err("bad rule".into()));
                            };
                            rules.push(h(
                                23,
                                &[
                                    get(&names, int(x, "ctor")?)?,
                                    int(x, "nfields")?,
                                    get(&exprs, int(x, "rhs")?)?,
                                ],
                            ));
                        }
                        parts.push(h(
                            22,
                            &[
                                head(r)?,
                                boolean(r, "isUnsafe")?,
                                nl(r, "all")?,
                                int(r, "numParams")?,
                                int(r, "numIndices")?,
                                int(r, "numMotives")?,
                                int(r, "numMinors")?,
                                h(0, &rules),
                                boolean(r, "k")?,
                            ],
                        ));
                    }
                    h(
                        15,
                        &[
                            ts.len() as u64,
                            cs.len() as u64,
                            rs.len() as u64,
                            h(0, &parts),
                        ],
                    )
                }
                _ => return Err(err("unknown declaration kind".into())),
            };
            acc = mix(acc, d);
        }
    }
    Ok(acc)
}
