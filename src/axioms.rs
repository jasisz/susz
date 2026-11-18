//! The axioms some declarations depend on: the axiom declarations in the
//! same dependency closure `slice` keeps (see [`crate::slice`]), found
//! without writing anything. No root means every declaration, so every
//! axiom the file declares.

use crate::closure::{close, Bits, Clock, CloseError, Closed, Roots};
use crate::read::{Failure, File};
use std::fmt;

/// Where the closure starts.
#[derive(Debug, Clone, Default)]
pub struct AxiomsOptions {
    /// Declarations named exactly so (dotted form, as `verify` prints names).
    pub roots: Vec<String>,
    /// Every declaration whose dotted name starts with one of these strings.
    /// With no roots and no prefixes, every declaration.
    pub prefixes: Vec<String>,
    /// Report each phase on stderr.
    pub progress: bool,
}

#[derive(Debug)]
pub enum AxiomsError {
    /// The input failed a check (rejected or declined).
    File(Failure),
    /// Roots that name no declaration.
    NotFound(Vec<String>),
    /// No declaration matched the prefixes.
    Empty,
}

impl fmt::Display for AxiomsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AxiomsError::File(e) => write!(f, "{e}"),
            AxiomsError::NotFound(xs) => write!(f, "no declaration named {}", xs.join(", ")),
            AxiomsError::Empty => write!(f, "no declaration matches"),
        }
    }
}

impl std::error::Error for AxiomsError {}

impl From<Failure> for AxiomsError {
    fn from(e: Failure) -> Self {
        AxiomsError::File(e)
    }
}

impl From<CloseError> for AxiomsError {
    fn from(e: CloseError) -> Self {
        match e {
            CloseError::File(f) => AxiomsError::File(f),
            CloseError::NotFound(xs) => AxiomsError::NotFound(xs),
            CloseError::Empty => AxiomsError::Empty,
        }
    }
}

/// The axiom declarations of a file, by dotted name, each list sorted.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Axioms {
    /// In the closure of the roots.
    pub used: Vec<String>,
    /// Declared in the file, not in the closure.
    pub unused: Vec<String>,
}

/// The axioms of the Susz file `bytes`, split by the closure of the roots.
pub fn axioms(bytes: &[u8], opts: &AxiomsOptions) -> Result<Axioms, AxiomsError> {
    let mut clock = Clock {
        what: "axioms",
        on: opts.progress,
        t: std::time::Instant::now(),
    };
    let f = File::open(bytes)?;
    let roots = if opts.roots.is_empty() && opts.prefixes.is_empty() {
        Roots::All
    } else {
        Roots::Named {
            roots: &opts.roots,
            prefixes: &opts.prefixes,
        }
    };
    let Closed {
        st, decls, axioms, ..
    } = close(bytes, &f, roots, &mut clock)?;
    // the axioms' names: one sweep over the declared names
    let mut is_axiom = Bits::new(st.decls as usize);
    for &a in &axioms {
        is_axiom.set(a);
    }
    let mut out = Axioms::default();
    for (c, &d) in st.canon_decl.iter().enumerate() {
        if d != u32::MAX && is_axiom.get(d) {
            let name = st.canon.display(bytes, c as u32);
            if decls.get(d) {
                out.used.push(name);
            } else {
                out.unused.push(name);
            }
        }
    }
    out.used.sort_unstable();
    out.unused.sort_unstable();
    clock.lap(format_args!(
        "{} axioms used, {} unused",
        out.used.len(),
        out.unused.len()
    ));
    Ok(out)
}
