//! Susz 1: a binary form of a Lean 4 kernel export (lean4export 3.1).
//!
//! - [`pack`]: lean4export ndjson to canonical Susz 1 bytes.
//! - [`read`]: the reader. [`read::decode`] reads a file in one pass into
//!   the caller's own structures, checking every rule as it goes;
//!   [`read::decode_block`] reads one proof block later; [`verify`] is the
//!   full structural check, with located errors.
//! - [`index`]: the INDEX section: lookups and their verification.
//! - [`unpack`]: Susz 1 back to ndjson.
//! - `mmap` (cargo feature `mmap`): `open_mmap`, a file's bytes through a
//!   memory map.
//!
//! The format is specified in `docs/spec.md`.

pub mod asm;
pub mod canon;
pub mod digest;
pub mod format;
pub mod index;
#[cfg(feature = "mmap")]
pub mod mmap;
pub mod pack;
pub mod read;
pub mod unpack;
#[doc(hidden)]
pub mod vectors;

#[cfg(feature = "mmap")]
pub use mmap::{open_mmap, Mapped};
pub use read::{decode, verify, Failure, Outcome};

/// A path removed if the process panics (the packer's temporary output).
#[doc(hidden)]
pub mod cleanup {
    use std::sync::Mutex;

    static TMP: Mutex<Option<String>> = Mutex::new(None);

    pub fn register(path: &str) {
        if let Ok(mut g) = TMP.lock() {
            *g = Some(path.to_string());
        }
    }
    pub fn unregister() {
        if let Ok(mut g) = TMP.lock() {
            *g = None;
        }
    }
    /// Removes the registered path, if any (from a panic hook).
    pub fn remove() {
        if let Ok(g) = TMP.try_lock() {
            if let Some(p) = g.as_ref() {
                let _ = std::fs::remove_file(p);
            }
        }
    }
}
