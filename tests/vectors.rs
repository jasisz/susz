// The committed vectors are what the generator writes, and the reader
// gives exactly the expected outcome and location for each.

use std::path::Path;
use susz::vectors;

#[test]
fn vectors_are_current_and_read_as_expected() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/vectors");
    let all = vectors::all();
    let mut bad = Vec::new();
    for v in &all {
        let a = vectors::build(v);
        let dir = root.join(v.dir());
        let bytes = std::fs::read(dir.join(format!("{}.susz", v.name))).unwrap_or_default();
        let expect =
            std::fs::read_to_string(dir.join(format!("{}.expect", v.name))).unwrap_or_default();
        if bytes != a.bytes || expect != vectors::expect_text(v, &a) {
            bad.push(format!(
                "{}/{}: committed files are stale (run cargo run --example gen-vectors)",
                v.dir(),
                v.name
            ));
            continue;
        }
        let got = vectors::observed_text(v, &bytes);
        if got != expect {
            bad.push(format!(
                "{}/{}:\n--- expected\n{expect}--- read\n{got}",
                v.dir(),
                v.name
            ));
        }
    }
    // no stray files
    for d in ["accept", "reject", "decline", "index"] {
        for e in std::fs::read_dir(root.join(d)).unwrap() {
            let p = e.unwrap().path();
            let stem = p.file_stem().unwrap().to_string_lossy().to_string();
            if !all.iter().any(|v| v.name == stem && v.dir() == d) {
                bad.push(format!("stray file {}", p.display()));
            }
        }
    }
    assert!(
        bad.is_empty(),
        "{} of {} vectors fail:\n{}",
        bad.len(),
        all.len(),
        bad.join("\n")
    );
}

// A full check does not depend on INDEX's content (spec section 10, item 5): the
// base vector with its INDEX bytes replaced by any bytes of the same length
// has the same outcome.
#[test]
fn full_check_ignores_index_content() {
    let v = vectors::all()
        .into_iter()
        .find(|v| v.name == "blocks")
        .unwrap();
    let a = vectors::build(&v);
    let f = susz::read::File::open(&a.bytes).unwrap();
    let s = f.section(susz::format::SEC_INDEX).unwrap();
    let base = susz::digest::of_susz(&a.bytes).unwrap();
    for fill in [0u8, 0xff, 0x80, 7] {
        let mut b = a.bytes.clone();
        for x in &mut b[s.offset as usize..(s.offset + s.length) as usize] {
            *x = fill;
        }
        assert!(matches!(susz::verify(&b), susz::Outcome::Accepted(_)));
        assert_eq!(susz::digest::of_susz(&b).unwrap(), base);
    }
}

// Every single-byte change of the base vector gives some outcome without a
// panic, and never allocates beyond reason (a smoke test, not fuzzing).
#[test]
fn single_byte_mutations_do_not_panic() {
    let v = vectors::all()
        .into_iter()
        .find(|v| v.name == "blocks")
        .unwrap();
    let a = vectors::build(&v);
    for i in 0..a.bytes.len() {
        for x in [0u8, 1, 0x7f, 0x80, 0xff] {
            let mut b = a.bytes.clone();
            b[i] = x;
            let _ = susz::verify(&b);
            let _ = susz::digest::of_susz(&b);
            if let Ok(f) = susz::read::File::open(&b) {
                let _ = susz::index::verify_index(&f);
            }
        }
    }
}
