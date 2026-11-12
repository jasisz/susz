//! Susz 1 back to lean4export 3.1 ndjson. Names and levels keep their ids;
//! expressions are numbered in the order written, each proof block right
//! before its theorem. What packing drops (spec 9.1) stays dropped:
//! `letE.nondep` is written `false`. Packing the output again gives the
//! same Susz bytes.

use crate::canon::Part;
use crate::format;
use crate::read::{Block, Decl, Event, Expr, Failure, File, Head, Hints, Ids, Level, Ref};
use std::fmt::Write as _;
use std::io::Write;

#[derive(Debug)]
pub enum UnpackError {
    File(Failure),
    Io(std::io::Error),
}

impl std::fmt::Display for UnpackError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnpackError::File(e) => write!(f, "{e}"),
            UnpackError::Io(e) => write!(f, "cannot write: {e}"),
        }
    }
}

impl From<Failure> for UnpackError {
    fn from(e: Failure) -> Self {
        UnpackError::File(e)
    }
}
impl From<std::io::Error> for UnpackError {
    fn from(e: std::io::Error) -> Self {
        UnpackError::Io(e)
    }
}

fn jstr(out: &mut String, s: &[u8]) {
    out.push('"');
    for ch in String::from_utf8_lossy(s).chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

fn ids(out: &mut String, xs: &Ids) {
    out.push('[');
    for (i, x) in xs.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        let _ = write!(out, "{x}");
    }
    out.push(']');
}

const BINDER: [&str; 4] = ["default", "implicit", "strictImplicit", "instImplicit"];

fn expr_line(out: &mut String, ie: u64, e: &Expr, r: &dyn Fn(&Ref) -> u64) {
    match e {
        Expr::BVar(i) => {
            let _ = write!(out, "{{\"bvar\":{i},\"ie\":{ie}}}");
        }
        Expr::Sort(l) => {
            let _ = write!(out, "{{\"ie\":{ie},\"sort\":{l}}}");
        }
        Expr::Const(n, us) => {
            let _ = write!(out, "{{\"const\":{{\"name\":{n},\"us\":");
            ids(out, us);
            let _ = write!(out, "}},\"ie\":{ie}}}");
        }
        Expr::App(f, a) => {
            let _ = write!(
                out,
                "{{\"app\":{{\"arg\":{},\"fn\":{}}},\"ie\":{ie}}}",
                r(a),
                r(f)
            );
        }
        Expr::Lam(bi, n, t, b) => {
            let _ = write!(out, "{{\"ie\":{ie},\"lam\":{{\"binderInfo\":\"{}\",\"body\":{},\"name\":{n},\"type\":{}}}}}", BINDER[*bi as usize], r(b), r(t));
        }
        Expr::Pi(bi, n, t, b) => {
            let _ = write!(out, "{{\"forallE\":{{\"binderInfo\":\"{}\",\"body\":{},\"name\":{n},\"type\":{}}},\"ie\":{ie}}}", BINDER[*bi as usize], r(b), r(t));
        }
        Expr::Let(n, t, v, b) => {
            let _ = write!(out, "{{\"ie\":{ie},\"letE\":{{\"body\":{},\"name\":{n},\"nondep\":false,\"type\":{},\"value\":{}}}}}", r(b), r(t), r(v));
        }
        Expr::Nat(b) => {
            let _ = write!(
                out,
                "{{\"ie\":{ie},\"natVal\":\"{}\"}}",
                format::nat_to_decimal(b)
            );
        }
        Expr::Str(s) => {
            let _ = write!(out, "{{\"ie\":{ie},\"strVal\":");
            jstr(out, s.as_bytes());
            out.push('}');
        }
        Expr::Proj(n, i, x) => {
            let _ = write!(
                out,
                "{{\"ie\":{ie},\"proj\":{{\"idx\":{i},\"struct\":{},\"typeName\":{n}}}}}",
                r(x)
            );
        }
    }
    out.push('\n');
}

fn head(out: &mut String, h: &Head, ie: &[u64]) {
    let _ = write!(out, "\"levelParams\":");
    ids(out, &h.params);
    let _ = write!(out, ",\"name\":{},\"type\":{}", h.name, ie[h.ty as usize]);
}

/// Writes the ndjson form of a Susz file; checks it on the way (the first
/// structural error stops it).
pub fn unpack<W: Write>(bytes: &[u8], w: &mut W) -> Result<(), UnpackError> {
    let f = File::open(bytes)?;
    let mut out = String::with_capacity(1 << 20);
    out.push_str("{\"meta\":");
    match f.source() {
        Some(s) if !s.is_empty() => out.push_str(&String::from_utf8_lossy(s)),
        _ => out.push_str("{}"),
    }
    out.push_str("}\n");
    let mut m = f.main();
    // MAIN expression id to the ndjson id
    let mut ie: Vec<u64> = Vec::with_capacity(f.counts[2] as usize);
    let mut next: u64 = 0;
    while let Some(ev) = m.next() {
        if out.len() > 1 << 20 {
            w.write_all(out.as_bytes())?;
            out.clear();
        }
        match ev? {
            Event::Name { id, prefix, part } => match part {
                Part::Str(s) => {
                    let _ = write!(out, "{{\"in\":{id},\"str\":{{\"pre\":{prefix},\"str\":");
                    jstr(&mut out, s);
                    out.push_str("}}\n");
                }
                Part::Num(k) => {
                    let _ = writeln!(
                        out,
                        "{{\"in\":{id},\"num\":{{\"i\":{k},\"pre\":{prefix}}}}}"
                    );
                }
            },
            Event::Level { id, level } => {
                let _ = match level {
                    Level::Succ(a) => writeln!(out, "{{\"il\":{id},\"succ\":{a}}}"),
                    Level::Max(a, b) => writeln!(out, "{{\"il\":{id},\"max\":[{a},{b}]}}"),
                    Level::IMax(a, b) => writeln!(out, "{{\"il\":{id},\"imax\":[{a},{b}]}}"),
                    Level::Param(n) => writeln!(out, "{{\"il\":{id},\"param\":{n}}}"),
                };
            }
            Event::Expr { expr, .. } => {
                let r = |x: &Ref| match x {
                    Ref::Main(i) => ie[*i as usize],
                    Ref::Block(_) => unreachable!(),
                };
                expr_line(&mut out, next, &expr, &r);
                ie.push(next);
                next += 1;
            }
            Event::Frontier { .. } => {}
            Event::Decl { decl, .. } => match &decl {
                Decl::Axiom { head: h, is_unsafe } => {
                    out.push_str("{\"axiom\":{\"isUnsafe\":");
                    out.push_str(if *is_unsafe { "true," } else { "false," });
                    head(&mut out, h, &ie);
                    out.push_str("}}\n");
                }
                Decl::Defn {
                    head: h,
                    value,
                    hints,
                    safety,
                    all,
                } => {
                    out.push_str("{\"def\":{\"all\":");
                    ids(&mut out, all);
                    out.push_str(",\"hints\":");
                    match hints {
                        Hints::Opaque => out.push_str("\"opaque\""),
                        Hints::Abbrev => out.push_str("\"abbrev\""),
                        Hints::Regular(k) => {
                            let _ = write!(out, "{{\"regular\":{k}}}");
                        }
                    }
                    out.push(',');
                    let _ = write!(out, "\"levelParams\":");
                    ids(&mut out, &h.params);
                    let _ = write!(
                        out,
                        ",\"name\":{},\"safety\":\"{}\",\"type\":{},\"value\":{}}}}}",
                        h.name,
                        ["safe", "unsafe", "partial"][*safety as usize],
                        ie[h.ty as usize],
                        ie[*value as usize]
                    );
                    out.push('\n');
                }
                Decl::Thm {
                    head: h,
                    value,
                    all,
                } => {
                    out.push_str("{\"thm\":{\"all\":");
                    ids(&mut out, all);
                    out.push(',');
                    head(&mut out, h, &ie);
                    let _ = writeln!(out, ",\"value\":{}}}}}", ie[*value as usize]);
                }
                Decl::ThmBlock {
                    head: h,
                    block,
                    all,
                } => {
                    let mut local: Vec<u64> = Vec::with_capacity(block.exprs as usize);
                    for r in Block::new(bytes, m.state(), *block).without_rule_p() {
                        let (_, e) = r?;
                        let rf = |x: &Ref| match x {
                            Ref::Main(i) => ie[*i as usize],
                            Ref::Block(k) => local[*k as usize],
                        };
                        expr_line(&mut out, next, &e, &rf);
                        local.push(next);
                        next += 1;
                    }
                    out.push_str("{\"thm\":{\"all\":");
                    ids(&mut out, all);
                    out.push(',');
                    head(&mut out, h, &ie);
                    let _ = writeln!(out, ",\"value\":{}}}}}", local.last().unwrap());
                }
                Decl::Opaque {
                    head: h,
                    value,
                    is_unsafe,
                    all,
                } => {
                    out.push_str("{\"opaque\":{\"all\":");
                    ids(&mut out, all);
                    let _ = write!(out, ",\"isUnsafe\":{},", is_unsafe);
                    head(&mut out, h, &ie);
                    let _ = writeln!(out, ",\"value\":{}}}}}", ie[*value as usize]);
                }
                Decl::Quot { head: h, kind } => {
                    let _ = write!(
                        out,
                        "{{\"quot\":{{\"kind\":\"{}\",",
                        ["type", "ctor", "lift", "ind"][*kind as usize]
                    );
                    head(&mut out, h, &ie);
                    out.push_str("}}\n");
                }
                Decl::Inductive(ind) => {
                    out.push_str("{\"inductive\":{\"ctors\":[");
                    for (i, c) in ind.ctors.iter().enumerate() {
                        if i > 0 {
                            out.push(',');
                        }
                        let _ = write!(
                            out,
                            "{{\"cidx\":{},\"induct\":{},\"isUnsafe\":{},",
                            c.cidx, c.induct, c.is_unsafe
                        );
                        let _ = write!(out, "\"levelParams\":");
                        ids(&mut out, &c.head.params);
                        let _ = write!(
                            out,
                            ",\"name\":{},\"numFields\":{},\"numParams\":{},\"type\":{}}}",
                            c.head.name, c.num_fields, c.num_params, ie[c.head.ty as usize]
                        );
                    }
                    out.push_str("],\"recs\":[");
                    for (i, r) in ind.recs.iter().enumerate() {
                        if i > 0 {
                            out.push(',');
                        }
                        out.push_str("{\"all\":");
                        ids(&mut out, &r.all);
                        let _ = write!(
                            out,
                            ",\"isUnsafe\":{},\"k\":{},\"levelParams\":",
                            r.is_unsafe, r.k
                        );
                        ids(&mut out, &r.head.params);
                        let _ = write!(
                                out,
                                ",\"name\":{},\"numIndices\":{},\"numMinors\":{},\"numMotives\":{},\"numParams\":{},\"rules\":[",
                                r.head.name, r.num_indices, r.num_minors, r.num_motives, r.num_params
                            );
                        for (j, x) in r.rules.iter().enumerate() {
                            if j > 0 {
                                out.push(',');
                            }
                            let _ = write!(
                                out,
                                "{{\"ctor\":{},\"nfields\":{},\"rhs\":{}}}",
                                x.ctor, x.nfields, ie[x.rhs as usize]
                            );
                        }
                        let _ = write!(out, "],\"type\":{}}}", ie[r.head.ty as usize]);
                    }
                    out.push_str("],\"types\":[");
                    for (i, t) in ind.types.iter().enumerate() {
                        if i > 0 {
                            out.push(',');
                        }
                        out.push_str("{\"all\":");
                        ids(&mut out, &t.all);
                        out.push_str(",\"ctors\":");
                        ids(&mut out, &t.ctors);
                        let _ = write!(
                            out,
                            ",\"isRec\":{},\"isReflexive\":{},\"isUnsafe\":{},\"levelParams\":",
                            t.is_rec, t.is_reflexive, t.is_unsafe
                        );
                        ids(&mut out, &t.head.params);
                        let _ = write!(out, ",\"name\":{},\"numIndices\":{},\"numNested\":{},\"numParams\":{},\"type\":{}}}", t.head.name, t.num_indices, t.num_nested, t.num_params, ie[t.head.ty as usize]);
                    }
                    out.push_str("]}}\n");
                }
            },
        }
    }
    w.write_all(out.as_bytes())?;
    Ok(())
}
