//! Packing record by record: a producer that already holds the export's
//! records (an exporter reading `.olean` files, say) hands them to a
//! [`Packer`] one at a time instead of writing ndjson for `pack` to read.
//!
//! The records are lean4export 3.1's, with its ids: names and levels count
//! from 1 (0 is the anonymous name and the zero level), expressions from 0,
//! and a record refers only to earlier ones. The packer checks what it checks
//! reading ndjson, and the file it writes is byte for byte the one `pack`
//! writes from the same records as ndjson.

use super::pk::{self, Pk};
use super::{Options, PackError, Stats, R};

/// How a binder binds (`binderInfo`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Binder {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
}

/// A definition's reducibility hints.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Hints {
    Opaque,
    Abbrev,
    Regular(u64),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Safety {
    Safe,
    Unsafe,
    Partial,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuotKind {
    Type,
    Ctor,
    Lift,
    Ind,
}

/// The fields every declaration starts with: `name`, `levelParams`, `type`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Head {
    pub name: u64,
    pub level_params: Vec<u64>,
    pub ty: u64,
}

/// A declaration, as lean4export writes it on one line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Decl {
    Axiom {
        head: Head,
        is_unsafe: bool,
    },
    Def {
        head: Head,
        value: u64,
        hints: Hints,
        safety: Safety,
        all: Vec<u64>,
    },
    Thm {
        head: Head,
        value: u64,
        all: Vec<u64>,
    },
    Opaque {
        head: Head,
        value: u64,
        is_unsafe: bool,
        all: Vec<u64>,
    },
    Quot {
        head: Head,
        kind: QuotKind,
    },
    Inductive {
        types: Vec<IndType>,
        ctors: Vec<IndCtor>,
        recs: Vec<IndRec>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IndType {
    pub head: Head,
    pub is_unsafe: bool,
    pub num_params: u64,
    pub num_indices: u64,
    pub all: Vec<u64>,
    pub ctors: Vec<u64>,
    pub num_nested: u64,
    pub is_rec: bool,
    pub is_reflexive: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IndCtor {
    pub head: Head,
    pub is_unsafe: bool,
    pub induct: u64,
    pub cidx: u64,
    pub num_params: u64,
    pub num_fields: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IndRec {
    pub head: Head,
    pub is_unsafe: bool,
    pub all: Vec<u64>,
    pub num_params: u64,
    pub num_indices: u64,
    pub num_motives: u64,
    pub num_minors: u64,
    pub rules: Vec<IndRule>,
    pub k: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IndRule {
    pub ctor: u64,
    pub nfields: u64,
    pub rhs: u64,
}

/// Packs records handed over one at a time; [`Packer::write_file`] or
/// [`Packer::to_vec`] writes the file once the last one is in.
///
/// The first record is the header ([`Packer::meta`]). Any failure leaves the
/// packer unusable for more records: a [`PackError`] with the same fault
/// (invalid export, or cannot pack) the `pack` command reports.
pub struct Packer {
    pk: Pk,
    meta: bool,
}

impl Default for Packer {
    fn default() -> Self {
        Packer::new()
    }
}

impl Packer {
    pub fn new() -> Packer {
        Packer::with_capacity(0)
    }

    /// Room for about `exprs` expressions up front (the packer grows past it).
    pub fn with_capacity(exprs: usize) -> Packer {
        let mut pk = Pk::new(exprs.saturating_mul(16));
        pk.reserve_all(exprs.saturating_mul(16));
        Packer { pk, meta: false }
    }

    #[inline(always)]
    fn started(&self) -> R<()> {
        if self.meta {
            Ok(())
        } else {
            Err(PackError::invalid("a record before the header"))
        }
    }

    /// The header: `json` is the value of the `meta` key, kept byte for byte
    /// (SOURCE), as in the line `{"meta":JSON}`.
    pub fn meta(&mut self, json: &str) -> R<()> {
        if self.meta {
            return Err(PackError::invalid("a second header"));
        }
        let line = format!("{{\"meta\":{json}}}");
        self.pk.header(line.as_bytes())?;
        self.meta = true;
        Ok(())
    }

    // Names and levels.

    pub fn name_str(&mut self, id: u64, pre: u64, s: &str) -> R<()> {
        self.started()?;
        self.pk.nr.fresh(id, "name")?;
        self.pk.name_str(id, pre, s.as_bytes())
    }
    pub fn name_num(&mut self, id: u64, pre: u64, i: u64) -> R<()> {
        self.started()?;
        self.pk.nr.fresh(id, "name")?;
        self.pk.name_num(id, pre, i)
    }
    pub fn succ(&mut self, id: u64, l: u64) -> R<()> {
        self.started()?;
        self.pk.lr.fresh(id, "level")?;
        self.pk.succ(id, l)
    }
    pub fn max(&mut self, id: u64, a: u64, b: u64) -> R<()> {
        self.started()?;
        self.pk.lr.fresh(id, "level")?;
        self.pk.pair(id, a, b, true)
    }
    pub fn imax(&mut self, id: u64, a: u64, b: u64) -> R<()> {
        self.started()?;
        self.pk.lr.fresh(id, "level")?;
        self.pk.pair(id, a, b, false)
    }
    pub fn param(&mut self, id: u64, name: u64) -> R<()> {
        self.started()?;
        self.pk.lr.fresh(id, "level")?;
        self.pk.param(id, name)
    }

    // Expressions.

    pub fn bvar(&mut self, id: u64, i: u64) -> R<()> {
        self.started()?;
        self.pk.bvar(id, i)
    }
    pub fn sort(&mut self, id: u64, level: u64) -> R<()> {
        self.started()?;
        self.pk.sort(id, level)
    }
    pub fn constant(&mut self, id: u64, name: u64, us: &[u64]) -> R<()> {
        self.started()?;
        self.pk.cnst(id, name, us)
    }
    #[inline]
    pub fn app(&mut self, id: u64, fun: u64, arg: u64) -> R<()> {
        self.started()?;
        self.pk.er.fresh(id, "expression")?;
        self.pk.app(id, fun, arg)
    }
    pub fn lam(&mut self, id: u64, info: Binder, name: u64, ty: u64, body: u64) -> R<()> {
        self.binding(id, true, info, name, ty, body)
    }
    pub fn pi(&mut self, id: u64, info: Binder, name: u64, ty: u64, body: u64) -> R<()> {
        self.binding(id, false, info, name, ty, body)
    }
    #[inline]
    fn binding(&mut self, id: u64, lam: bool, info: Binder, n: u64, t: u64, b: u64) -> R<()> {
        self.started()?;
        self.pk.er.fresh(id, "expression")?;
        let bi = match info {
            Binder::Default => 0,
            Binder::Implicit => 1,
            Binder::StrictImplicit => 2,
            Binder::InstImplicit => 3,
        };
        self.pk.bind(id, lam, bi, n, t, b)
    }
    /// `nondep` is not kept (lean4export writes it; kernels do not read it).
    pub fn let_e(&mut self, id: u64, name: u64, ty: u64, value: u64, body: u64) -> R<()> {
        self.started()?;
        self.pk.let_e(id, name, ty, value, body)
    }
    /// A Nat literal in decimal, as `natVal` holds it.
    pub fn nat_decimal(&mut self, id: u64, digits: &str) -> R<()> {
        self.started()?;
        self.pk.nat(id, digits.as_bytes())
    }
    /// A Nat literal as little-endian bytes (trailing zero bytes are
    /// dropped: the format keeps the minimal form).
    pub fn nat_le(&mut self, id: u64, bytes: &[u8]) -> R<()> {
        self.started()?;
        let mut n = bytes.len();
        while n > 0 && bytes[n - 1] == 0 {
            n -= 1;
        }
        self.pk.nat_le(id, &bytes[..n])
    }
    pub fn str_lit(&mut self, id: u64, s: &str) -> R<()> {
        self.started()?;
        self.pk.strv(id, s.as_bytes())
    }
    pub fn proj(&mut self, id: u64, type_name: u64, idx: u64, struct_: u64) -> R<()> {
        self.started()?;
        self.pk.proj(id, type_name, idx, struct_)
    }
    /// Metadata around `expr`: not written, `id` stands for `expr` (the
    /// data itself is not taken).
    pub fn mdata(&mut self, id: u64, expr: u64) -> R<()> {
        self.started()?;
        self.pk.mdata(id, expr)
    }

    // Declarations.

    pub fn decl(&mut self, d: &Decl) -> R<()> {
        self.started()?;
        self.pk.decl(d)
    }

    // The file.

    /// Writes the file to `output`, under a temporary name renamed when
    /// complete (as `pack` does).
    pub fn write_file(self, output: &str, opts: &Options) -> R<Stats> {
        let pk = self.done()?;
        super::write_file(pk, output, opts)
    }

    /// The file's bytes.
    pub fn to_vec(self, opts: &Options) -> R<(Vec<u8>, Stats)> {
        let pk = self.done()?;
        super::write_vec(pk, opts)
    }

    fn done(mut self) -> R<pk::Pk> {
        if !self.meta {
            return Err(PackError::invalid("empty file"));
        }
        self.pk.finish();
        Ok(self.pk)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const META: &str = r#"{"exporter":{"name":"t","version":"0"},"format":{"version":"3.1.0"}}"#;

    // The same export as ndjson and as records: the same bytes.
    #[test]
    fn records_pack_as_their_ndjson() {
        let big = "1".repeat(60) + "7";
        let nd = format!(
            r#"{{"meta":{META}}}
{{"in":1,"str":{{"pre":0,"str":"A"}}}}
{{"in":2,"str":{{"pre":0,"str":"u"}}}}
{{"in":3,"num":{{"i":4,"pre":1}}}}
{{"il":1,"param":2}}
{{"il":2,"succ":1}}
{{"il":3,"max":[1,2]}}
{{"ie":0,"sort":3}}
{{"axiom":{{"isUnsafe":false,"levelParams":[2],"name":1,"type":0}}}}
{{"const":{{"name":1,"us":[1]}},"ie":1}}
{{"bvar":0,"ie":2}}
{{"ie":3,"lam":{{"binderInfo":"implicit","body":2,"name":2,"type":1}}}}
{{"forallE":{{"binderInfo":"default","body":1,"name":2,"type":1}},"ie":4}}
{{"ie":5,"natVal":"{big}"}}
{{"ie":6,"mdata":{{"data":{{}},"expr":5}}}}
{{"app":{{"arg":6,"fn":3}},"ie":7}}
{{"ie":8,"strVal":"s\"x"}}
{{"thm":{{"all":[3],"levelParams":[2],"name":3,"type":4,"value":7}}}}
{{"def":{{"all":[],"hints":{{"regular":3}},"levelParams":[],"name":2,"safety":"safe","type":0,"value":8}}}}
"#
        );
        let dir = std::env::temp_dir().join(format!("susz-api-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let f = dir.join("t.ndjson");
        std::fs::write(&f, nd).unwrap();
        let opts = Options::default();
        let (want, _) = super::super::pack_to_vec(f.to_str().unwrap(), &opts).unwrap();
        std::fs::remove_dir_all(&dir).unwrap();

        let mut p = Packer::new();
        p.meta(META).unwrap();
        p.name_str(1, 0, "A").unwrap();
        p.name_str(2, 0, "u").unwrap();
        p.name_num(3, 1, 4).unwrap();
        p.param(1, 2).unwrap();
        p.succ(2, 1).unwrap();
        p.max(3, 1, 2).unwrap();
        p.sort(0, 3).unwrap();
        let head = |name, ps: &[u64], ty| Head {
            name,
            level_params: ps.to_vec(),
            ty,
        };
        p.decl(&Decl::Axiom {
            head: head(1, &[2], 0),
            is_unsafe: false,
        })
        .unwrap();
        p.constant(1, 1, &[1]).unwrap();
        p.bvar(2, 0).unwrap();
        p.lam(3, Binder::Implicit, 2, 1, 2).unwrap();
        p.pi(4, Binder::Default, 2, 1, 1).unwrap();
        p.nat_decimal(5, &big).unwrap();
        p.mdata(6, 5).unwrap();
        p.app(7, 3, 6).unwrap();
        p.str_lit(8, "s\"x").unwrap();
        p.decl(&Decl::Thm {
            head: head(3, &[2], 4),
            value: 7,
            all: vec![3],
        })
        .unwrap();
        p.decl(&Decl::Def {
            head: head(2, &[], 0),
            value: 8,
            hints: Hints::Regular(3),
            safety: Safety::Safe,
            all: vec![],
        })
        .unwrap();
        let (got, _) = p.to_vec(&opts).unwrap();
        assert_eq!(got, want);
    }

    #[test]
    fn records_are_checked() {
        let mut p = Packer::new();
        assert!(p.name_str(1, 0, "A").is_err());
        p.meta(META).unwrap();
        assert!(p.app(0, 1, 2).is_err());
        let mut p = Packer::new();
        p.meta(META).unwrap();
        p.name_str(1, 0, "A").unwrap();
        assert!(p.name_str(1, 0, "B").is_err());
        // past the room reserved up front
        let mut p = Packer::with_capacity(1);
        p.meta(META).unwrap();
        p.bvar(0, 0).unwrap();
        for i in 1..200_000u64 {
            p.app(i, i - 1, 0).unwrap();
        }
        p.to_vec(&Options::default()).unwrap();
    }
}
