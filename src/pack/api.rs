//! Packing record by record: a producer that already holds the export's
//! records (an exporter reading `.olean` files, say) hands them to a
//! [`Packer`] one at a time instead of writing ndjson for `pack` to read.
//!
//! The records are lean4export's (3.1, or 3.2 with the flags of inductive
//! types, [`IndType::flags`]), with its ids: names and levels count
//! from 1 (0 is the anonymous name and the zero level), expressions from 0,
//! and a record refers only to earlier ones. Each kind of record has its own
//! method, named after the ndjson record it stands for, and takes that
//! record's fields as ids. The packer checks what it checks reading ndjson,
//! and the file it writes is byte for byte the one `pack` writes from the
//! same records as ndjson.

use super::pk::{self, Pk};
use super::{Options, PackError, Stats, R};
pub use crate::format::IndFlags;

/// How a binder binds (`binderInfo`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Binder {
    /// `"default"`: `(x : A)`.
    Default,
    /// `"implicit"`: `{x : A}`.
    Implicit,
    /// `"strictImplicit"`: `⦃x : A⦄`.
    StrictImplicit,
    /// `"instImplicit"`: `[x : A]`.
    InstImplicit,
}

/// A definition's reducibility hints (`hints`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Hints {
    /// `"opaque"`: never unfolded by height.
    Opaque,
    /// `"abbrev"`: always unfolded first.
    Abbrev,
    /// `{"regular":H}`: unfolded by its definitional height `H`.
    Regular(u64),
}

/// A definition's safety (`safety`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Safety {
    /// `"safe"`.
    Safe,
    /// `"unsafe"`.
    Unsafe,
    /// `"partial"`.
    Partial,
}

/// Which of the four quotient constants a `quot` declaration is (`kind`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuotKind {
    /// `"type"`: `Quot`.
    Type,
    /// `"ctor"`: `Quot.mk`.
    Ctor,
    /// `"lift"`: `Quot.lift`.
    Lift,
    /// `"ind"`: `Quot.ind`.
    Ind,
}

/// The fields every declaration starts with: `name`, `levelParams`, `type`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Head {
    /// The declaration's name (a name id).
    pub name: u64,
    /// Its universe parameters, in order (name ids).
    pub level_params: Vec<u64>,
    /// Its type (an expression id).
    pub ty: u64,
}

/// A declaration, as lean4export writes it on one line. Names are name ids,
/// `value` and `ty` expression ids; `all` lists the names of the mutual
/// block the declaration belongs to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Decl {
    /// `axiom`.
    Axiom {
        /// Name, universe parameters, type.
        head: Head,
        /// `isUnsafe`.
        is_unsafe: bool,
    },
    /// `def`.
    Def {
        /// Name, universe parameters, type.
        head: Head,
        /// `value`.
        value: u64,
        /// `hints`.
        hints: Hints,
        /// `safety`.
        safety: Safety,
        /// `all`.
        all: Vec<u64>,
    },
    /// `thm`. Its value is a proof, which the file keeps in a proof block
    /// when no other declaration reaches it.
    Thm {
        /// Name, universe parameters, type.
        head: Head,
        /// `value`.
        value: u64,
        /// `all`.
        all: Vec<u64>,
    },
    /// `opaque`.
    Opaque {
        /// Name, universe parameters, type.
        head: Head,
        /// `value`.
        value: u64,
        /// `isUnsafe`.
        is_unsafe: bool,
        /// `all`.
        all: Vec<u64>,
    },
    /// `quot`.
    Quot {
        /// Name, universe parameters, type.
        head: Head,
        /// `kind`.
        kind: QuotKind,
    },
    /// `inductive`: a mutual block of types with their constructors and
    /// recursors, one record for the whole block.
    Inductive {
        /// `types`.
        types: Vec<IndType>,
        /// `ctors`.
        ctors: Vec<IndCtor>,
        /// `recs`.
        recs: Vec<IndRec>,
    },
}

/// One type of an [`Decl::Inductive`] block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IndType {
    /// Name, universe parameters, type.
    pub head: Head,
    /// `isUnsafe`.
    pub is_unsafe: bool,
    /// `numParams`.
    pub num_params: u64,
    /// `numIndices`.
    pub num_indices: u64,
    /// `all`: the names of the block's types.
    pub all: Vec<u64>,
    /// `ctors`: the names of this type's constructors.
    pub ctors: Vec<u64>,
    /// `numNested`.
    pub num_nested: u64,
    /// `isRec`.
    pub is_rec: bool,
    /// `isReflexive`.
    pub is_reflexive: bool,
    /// The five flags of lean4export 3.2 (`isImpredicative`, `isK`,
    /// `hasProjections`, `hasEta`, `hasLargeElim`), or `None` for a type
    /// written without them (lean4export 3.1). The types of one block all
    /// have them or all do not; under a 3.2 header every type has them.
    pub flags: Option<IndFlags>,
}

/// One constructor of an [`Decl::Inductive`] block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IndCtor {
    /// Name, universe parameters, type.
    pub head: Head,
    /// `isUnsafe`.
    pub is_unsafe: bool,
    /// `induct`: the name of the type it constructs.
    pub induct: u64,
    /// `cidx`: its place among that type's constructors.
    pub cidx: u64,
    /// `numParams`.
    pub num_params: u64,
    /// `numFields`.
    pub num_fields: u64,
}

/// One recursor of an [`Decl::Inductive`] block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IndRec {
    /// Name, universe parameters, type.
    pub head: Head,
    /// `isUnsafe`.
    pub is_unsafe: bool,
    /// `all`.
    pub all: Vec<u64>,
    /// `numParams`.
    pub num_params: u64,
    /// `numIndices`.
    pub num_indices: u64,
    /// `numMotives`.
    pub num_motives: u64,
    /// `numMinors`.
    pub num_minors: u64,
    /// `rules`: one per constructor.
    pub rules: Vec<IndRule>,
    /// `k`: whether the recursor reduces by K-like reduction.
    pub k: bool,
}

/// One rule of an [`IndRec`]: what the recursor reduces to on a constructor.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IndRule {
    /// `ctor`: the constructor's name.
    pub ctor: u64,
    /// `nfields`.
    pub nfields: u64,
    /// `rhs`: an expression id.
    pub rhs: u64,
}

/// Packs records handed over one at a time; [`Packer::write_file`] or
/// [`Packer::to_vec`] writes the file once the last one is in.
///
/// The first record is the header ([`Packer::meta`]). Any failure leaves the
/// packer unusable for more records: a [`PackError`] with the same fault
/// (invalid export, or cannot pack) the `pack` command reports.
///
/// ```
/// use susz::pack::{Decl, Head, Options, Packer};
///
/// # fn main() -> Result<(), susz::pack::PackError> {
/// let mut p = Packer::new();
/// p.meta(r#"{"exporter":{"name":"me","version":"0"},"format":{"version":"3.1.0"}}"#)?;
/// p.name_str(1, 0, "P")?; // name 1: `P`
/// p.sort(0, 0)?; // expression 0: `Sort 0`, that is `Prop`
/// p.decl(&Decl::Axiom {
///     head: Head { name: 1, level_params: vec![], ty: 0 },
///     is_unsafe: false,
/// })?;
/// let (bytes, stats) = p.to_vec(&Options::default())?;
/// assert_eq!(stats.decls, 1);
/// assert!(matches!(susz::verify(&bytes), susz::Outcome::Accepted(_)));
/// # Ok(())
/// # }
/// ```
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
    /// A packer with no room reserved up front.
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

    /// Name `id` is `pre` followed by the string `s` (`"str"`).
    pub fn name_str(&mut self, id: u64, pre: u64, s: &str) -> R<()> {
        self.started()?;
        self.pk.nr.fresh(id, "name")?;
        self.pk.name_str(id, pre, s.as_bytes())
    }
    /// Name `id` is `pre` followed by the number `i` (`"num"`).
    pub fn name_num(&mut self, id: u64, pre: u64, i: u64) -> R<()> {
        self.started()?;
        self.pk.nr.fresh(id, "name")?;
        self.pk.name_num(id, pre, i)
    }
    /// Level `id` is `l + 1` (`"succ"`).
    pub fn succ(&mut self, id: u64, l: u64) -> R<()> {
        self.started()?;
        self.pk.lr.fresh(id, "level")?;
        self.pk.succ(id, l)
    }
    /// Level `id` is `max a b` (`"max"`).
    pub fn max(&mut self, id: u64, a: u64, b: u64) -> R<()> {
        self.started()?;
        self.pk.lr.fresh(id, "level")?;
        self.pk.pair(id, a, b, true)
    }
    /// Level `id` is `imax a b` (`"imax"`).
    pub fn imax(&mut self, id: u64, a: u64, b: u64) -> R<()> {
        self.started()?;
        self.pk.lr.fresh(id, "level")?;
        self.pk.pair(id, a, b, false)
    }
    /// Level `id` is the universe parameter named `name` (`"param"`).
    pub fn param(&mut self, id: u64, name: u64) -> R<()> {
        self.started()?;
        self.pk.lr.fresh(id, "level")?;
        self.pk.param(id, name)
    }

    // Expressions.

    /// Expression `id` is the bound variable of de Bruijn index `i`
    /// (`"bvar"`).
    pub fn bvar(&mut self, id: u64, i: u64) -> R<()> {
        self.started()?;
        self.pk.bvar(id, i)
    }
    /// Expression `id` is `Sort level` (`"sort"`).
    pub fn sort(&mut self, id: u64, level: u64) -> R<()> {
        self.started()?;
        self.pk.sort(id, level)
    }
    /// Expression `id` is the constant `name` at universe levels `us`
    /// (`"const"`).
    pub fn constant(&mut self, id: u64, name: u64, us: &[u64]) -> R<()> {
        self.started()?;
        self.pk.cnst(id, name, us)
    }
    /// Expression `id` is `fun` applied to `arg` (`"app"`).
    #[inline]
    pub fn app(&mut self, id: u64, fun: u64, arg: u64) -> R<()> {
        self.started()?;
        self.pk.er.fresh(id, "expression")?;
        self.pk.app(id, fun, arg)
    }
    /// Expression `id` is `fun (name : ty) => body` (`"lam"`).
    pub fn lam(&mut self, id: u64, info: Binder, name: u64, ty: u64, body: u64) -> R<()> {
        self.binding(id, true, info, name, ty, body)
    }
    /// Expression `id` is `(name : ty) → body` (`"forallE"`).
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
    /// Expression `id` is `let name : ty := value; body` (`"letE"`).
    /// `nondep` is not kept (lean4export writes it; kernels do not read it).
    pub fn let_e(&mut self, id: u64, name: u64, ty: u64, value: u64, body: u64) -> R<()> {
        self.started()?;
        self.pk.let_e(id, name, ty, value, body)
    }
    /// Expression `id` is a Nat literal in decimal, as `natVal` holds it.
    pub fn nat_decimal(&mut self, id: u64, digits: &str) -> R<()> {
        self.started()?;
        self.pk.nat(id, digits.as_bytes())
    }
    /// Expression `id` is a Nat literal given as little-endian bytes
    /// (trailing zero bytes are dropped: the format keeps the minimal form).
    /// It packs as [`Packer::nat_decimal`] does with the same number.
    pub fn nat_le(&mut self, id: u64, bytes: &[u8]) -> R<()> {
        self.started()?;
        let mut n = bytes.len();
        while n > 0 && bytes[n - 1] == 0 {
            n -= 1;
        }
        self.pk.nat_le(id, &bytes[..n])
    }
    /// Expression `id` is the String literal `s` (`"strVal"`).
    pub fn str_lit(&mut self, id: u64, s: &str) -> R<()> {
        self.started()?;
        self.pk.strv(id, s.as_bytes())
    }
    /// Expression `id` is field `idx` of `struct_`, a value of the structure
    /// named `type_name` (`"proj"`).
    pub fn proj(&mut self, id: u64, type_name: u64, idx: u64, struct_: u64) -> R<()> {
        self.started()?;
        self.pk.proj(id, type_name, idx, struct_)
    }
    /// Metadata around `expr` (`"mdata"`): not written, `id` stands for
    /// `expr` (the data itself is not taken).
    pub fn mdata(&mut self, id: u64, expr: u64) -> R<()> {
        self.started()?;
        self.pk.mdata(id, expr)
    }

    // Declarations.

    /// A declaration; every id it names must already be in.
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
