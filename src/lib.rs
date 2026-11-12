//! Susz 1: a binary form of a Lean 4 kernel export (lean4export 3.1).
//!
//! - [`pack`]: lean4export ndjson to canonical Susz 1 bytes.
//! - [`read`]: the reader: framing, MAIN records, proof blocks by range,
//!   full structural verification with located errors.
//! - [`index`]: the INDEX section: lookups and their verification.
//! - [`unpack`]: Susz 1 back to ndjson.
//!
//! The format is specified in `docs/spec.md`.

pub mod asm;
pub mod canon;
pub mod digest;
pub mod format;
pub mod index;
pub mod pack;
pub mod read;
pub mod unpack;
#[doc(hidden)]
pub mod vectors;

pub use read::{verify, Failure, Outcome};

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
