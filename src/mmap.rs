//! A file's bytes through a memory map (cargo feature `mmap`).
//!
//! The reader works on `&[u8]`, so a mapped file is just another way to get
//! the slice: the system reads pages as the reader touches them instead of
//! copying the whole file into the process first.

use std::fs;
use std::io::{self, Read};
use std::ops::Deref;
use std::path::Path;

/// A file's bytes: mapped when the file could be mapped, read into memory
/// otherwise. Derefs to `[u8]`.
pub struct Mapped(Inner);

enum Inner {
    Map(memmap2::Mmap),
    Read(Vec<u8>),
}

impl Mapped {
    /// Whether the bytes are mapped (`false`: they were read into memory).
    pub fn is_mapped(&self) -> bool {
        matches!(self.0, Inner::Map(_))
    }
}

impl Deref for Mapped {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        match &self.0 {
            Inner::Map(m) => m,
            Inner::Read(v) => v,
        }
    }
}

impl AsRef<[u8]> for Mapped {
    fn as_ref(&self) -> &[u8] {
        self
    }
}

/// Opens `path` read-only and maps it. When it is not a regular file (a
/// pipe, a terminal) or the system refuses to map it, the file is read into
/// memory instead, as `std::fs::read` would.
///
/// # Safety
///
/// While the result is alive, nothing may truncate or modify the file. A
/// write by another process shows through in the bytes the reader already
/// trusts. A truncation makes any later access to the lost pages raise
/// `SIGBUS` on Unix, which kills the process unless it handles that signal.
/// The same happens when the system cannot read a page in (an I/O error, a
/// network file system going away).
pub unsafe fn open_mmap(path: impl AsRef<Path>) -> io::Result<Mapped> {
    let mut f = fs::File::open(path)?;
    if f.metadata()?.is_file() {
        // SAFETY: the caller's promise above.
        if let Ok(m) = unsafe { memmap2::Mmap::map(&f) } {
            return Ok(Mapped(Inner::Map(m)));
        }
    }
    let mut v = Vec::new();
    f.read_to_end(&mut v)?;
    Ok(Mapped(Inner::Read(v)))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn maps_a_regular_file_and_reads_the_same_bytes() {
        let p = std::env::temp_dir().join(format!("susz-mmap-{}", std::process::id()));
        fs::write(&p, b"Susz bytes").unwrap();
        let m = unsafe { open_mmap(&p) }.unwrap();
        assert!(m.is_mapped());
        assert_eq!(&m[..], b"Susz bytes");
        drop(m);
        fs::write(&p, b"").unwrap();
        assert!(unsafe { open_mmap(&p) }.unwrap().is_empty());
        fs::remove_file(&p).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn falls_back_to_reading_a_non_regular_file() {
        let m = unsafe { open_mmap("/dev/null") }.unwrap();
        assert!(!m.is_mapped());
        assert!(m.is_empty());
    }
}
