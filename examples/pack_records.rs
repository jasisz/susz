// Packs a tiny export from records, without ndjson, and checks the file:
//
//   theorem id_p : ∀ (p : Prop), p → p := fun p h => h
//
//   cargo run --example pack-records -- id_p.susz

use susz::pack::{Binder, Decl, Head, Options, PackError, Packer};

fn main() -> Result<(), PackError> {
    let out = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "id_p.susz".into());
    let mut p = Packer::new();
    // The header comes first; the packer keeps it byte for byte.
    p.meta(r#"{"exporter":{"name":"pack-records","version":"0"},"format":{"version":"3.1.0"}}"#)?;
    // Names count from 1 (0 is the anonymous name), each after its prefix.
    p.name_str(1, 0, "id_p")?;
    p.name_str(2, 0, "p")?;
    p.name_str(3, 0, "h")?;
    // Expressions count from 0 and refer only to earlier ones.
    p.sort(0, 0)?; // Prop (level 0 is the zero level)
    p.bvar(1, 0)?;
    p.bvar(2, 1)?;
    p.pi(3, Binder::Default, 3, 1, 2)?; // (h : p) → p
    p.pi(4, Binder::Default, 2, 0, 3)?; // ∀ (p : Prop), p → p
    p.lam(5, Binder::Default, 3, 1, 1)?; // fun (h : p) => h
    p.lam(6, Binder::Default, 2, 0, 5)?; // fun (p : Prop) (h : p) => h
    p.decl(&Decl::Thm {
        head: Head {
            name: 1,
            level_params: vec![],
            ty: 4,
        },
        value: 6,
        all: vec![1],
    })?;
    let stats = p.write_file(&out, &Options::default())?;
    eprintln!("{out}: {stats}");

    let bytes = std::fs::read(&out).map_err(|e| PackError::cannot(e.to_string()))?;
    match susz::verify(&bytes) {
        susz::Outcome::Accepted(_) => eprintln!("{out}: accepted"),
        susz::Outcome::Rejected(e) | susz::Outcome::Declined(e) => {
            return Err(PackError::cannot(format!("{out}: {e}")))
        }
    }
    Ok(())
}
