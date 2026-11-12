//! The packer: lean4export 3.1 ndjson to canonical Susz 1 (spec section 9).
//!
//! Reading lines fills columns of expressions and a stream of the other
//! records (`pk`, `lines`, `par`); a walk back from the last expression
//! decides which expressions only one theorem's value reaches; the writer
//! (`write`) then emits MAIN, PROOFS, INDEX and SOURCE.

pub(crate) mod json;
mod lines;
mod par;
mod pk;
mod write;

use std::fmt;

/// Whose fault a packing failure is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Fault {
    /// The input is not a valid export (exit code 1).
    Invalid,
    /// The input may be fine but this packer cannot pack it: a limit, a
    /// record or field it does not know, I/O, an internal error (exit code 2).
    Cannot,
}

#[derive(Debug, Clone)]
pub struct PackError {
    pub fault: Fault,
    pub msg: String,
}

impl PackError {
    pub fn invalid(msg: impl Into<String>) -> PackError {
        PackError {
            fault: Fault::Invalid,
            msg: msg.into(),
        }
    }
    pub fn cannot(msg: impl Into<String>) -> PackError {
        PackError {
            fault: Fault::Cannot,
            msg: msg.into(),
        }
    }
    /// The same failure with a prefix (for instance the line number).
    pub fn at(self, prefix: impl fmt::Display) -> PackError {
        PackError {
            fault: self.fault,
            msg: format!("{prefix}: {}", self.msg),
        }
    }
}

impl From<String> for PackError {
    fn from(s: String) -> Self {
        PackError::invalid(s)
    }
}
impl From<&str> for PackError {
    fn from(s: &str) -> Self {
        PackError::invalid(s)
    }
}

impl fmt::Display for PackError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.msg)
    }
}

impl std::error::Error for PackError {}

pub type R<T> = Result<T, PackError>;

macro_rules! inv {
    ($($t:tt)*) => { $crate::pack::PackError::invalid(format!($($t)*)) };
}
macro_rules! cant {
    ($($t:tt)*) => { $crate::pack::PackError::cannot(format!($($t)*)) };
}
pub(crate) use cant;
pub(crate) use inv;

/// Packing options.
#[derive(Debug, Clone)]
pub struct Options {
    /// Write the INDEX section (the default).
    pub index: bool,
    /// Workers reading the input (1: one thread). The output does not depend on it.
    pub threads: usize,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            index: true,
            threads: 1,
        }
    }
}

/// What a packing run wrote.
#[derive(Debug, Clone, Default)]
pub struct Stats {
    /// Names and levels with their implicit id 0, as the trailer counts them.
    pub names: u64,
    pub levels: u64,
    pub exprs: u64,
    pub main_exprs: u64,
    pub decls: u64,
    pub blocks: u64,
    pub main_bytes: u64,
    pub proofs_bytes: u64,
    pub index_bytes: u64,
    pub source_bytes: u64,
    pub file_bytes: u64,
    pub parallel: bool,
}

impl fmt::Display for Stats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "names {}, levels {}, expressions {} (MAIN {}, in blocks {}), declarations {} (blocks {}); MAIN {} bytes, PROOFS {}, INDEX {}, SOURCE {}; file {} bytes{}",
            self.names - 1,
            self.levels - 1,
            self.exprs,
            self.main_exprs,
            self.exprs - self.main_exprs,
            self.decls,
            self.blocks,
            self.main_bytes,
            self.proofs_bytes,
            self.index_bytes,
            self.source_bytes,
            self.file_bytes,
            if self.parallel { " (read on several workers)" } else { "" }
        )
    }
}

/// Reads the export at `input` and returns the packed file's bytes.
pub fn pack_to_vec(input: &str, opts: &Options) -> R<(Vec<u8>, Stats)> {
    let (pk, parallel) = read(input, opts)?;
    let mut out = Vec::new();
    let mut st = write::write(pk, &mut out, opts.index)?;
    st.parallel = parallel;
    Ok((out, st))
}

/// Packs the export at `input` into `output`. The file is written under a
/// temporary name next to `output` and renamed when complete, so `output`
/// never holds a partial file.
pub fn pack_file(input: &str, output: &str, opts: &Options) -> R<Stats> {
    let (pk, parallel) = read(input, opts)?;
    let tmp = format!("{output}.tmp-{}", std::process::id());
    crate::cleanup::register(&tmp);
    let res = (|| {
        let f = std::fs::File::create(&tmp).map_err(|e| cant!("cannot write {tmp}: {e}"))?;
        let mut w = std::io::BufWriter::with_capacity(1 << 20, f);
        let mut st = write::write(pk, &mut w, opts.index)?;
        use std::io::Write;
        w.flush().map_err(|e| cant!("cannot write {tmp}: {e}"))?;
        // complete for every other process once renamed; no fsync (on macOS a
        // full flush to the device costs seconds on mathlib)
        let f = w
            .into_inner()
            .map_err(|e| cant!("cannot write {tmp}: {e}"))?;
        drop(f);
        std::fs::rename(&tmp, output).map_err(|e| cant!("cannot rename {tmp} to {output}: {e}"))?;
        st.parallel = parallel;
        Ok(st)
    })();
    if res.is_err() {
        let _ = std::fs::remove_file(&tmp);
    }
    crate::cleanup::unregister();
    res
}

fn read(input: &str, opts: &Options) -> R<(pk::Pk, bool)> {
    let size = std::fs::metadata(input)
        .map_err(|e| cant!("cannot read {input}: {e}"))?
        .len() as usize;
    if opts.threads > 1 {
        if let Some(p) = par::parse_parallel(input, opts.threads)? {
            return Ok((p, true));
        }
    }
    let mut pk = pk::Pk::new(size);
    pk.own_cols(size);
    lines::read_file(input, &mut pk, 16 << 20)?;
    pk.finish();
    Ok((pk, false))
}
