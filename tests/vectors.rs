// The committed vectors are what the generator writes, and the reader
// gives exactly the expected outcome and location for each.

mod common;

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
        if let Err(e) = common::same_outcomes(&bytes) {
            bad.push(format!(
                "{}/{}: the single pass differs:\n{e}",
                v.dir(),
                v.name
            ));
        }
        if matches!(susz::verify(&bytes), susz::Outcome::Accepted(_)) {
            if let Err(e) = common::same_events(&bytes) {
                bad.push(format!("{}/{}: {e}", v.dir(), v.name));
            }
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
// panic, and never allocates beyond reason (a smoke test, not fuzzing). The
// single pass, the two-pass check and the lazy order agree on each.
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
            if let Err(e) = common::same_outcomes(&b) {
                panic!("byte {i} set to {x:#x}: the single pass differs:\n{e}");
            }
            let _ = susz::digest::of_susz(&b);
            if let Ok(f) = susz::read::File::open(&b) {
                let _ = susz::index::verify_index(&f);
            }
        }
    }
}

// An error inside a block is reported only when MAIN, the counts and the
// PROOFS fill have none (spec 8.1 before 8.2), even though the single pass
// meets the block first. Two changes: one in PROOFS, one in MAIN or the
// trailer.
#[test]
fn main_errors_come_before_block_errors() {
    let v = vectors::all()
        .into_iter()
        .find(|v| v.name == "blocks")
        .unwrap();
    let a = vectors::build(&v);
    let f = susz::read::File::open(&a.bytes).unwrap();
    let main = f.section(susz::format::SEC_MAIN).unwrap();
    let proofs = f.section(susz::format::SEC_PROOFS).unwrap();
    let trailer = f.trailer as usize;
    let later: Vec<usize> = (main.offset as usize..(main.offset + main.length) as usize)
        .chain(trailer..trailer + 16)
        .collect();
    for i in proofs.offset as usize..(proofs.offset + proofs.length) as usize {
        for &j in &later {
            let mut b = a.bytes.clone();
            b[i] = 0xff;
            b[j] ^= 0x41;
            if let Err(e) = common::same_outcomes(&b) {
                panic!("PROOFS byte {i}, byte {j}: the single pass differs:\n{e}");
            }
        }
    }
    // a bad tag in the first block and a wrong name count: the count wins
    let mut b = a.bytes.clone();
    b[proofs.offset as usize] = 0xff;
    b[trailer] ^= 1;
    match susz::verify(&b) {
        susz::Outcome::Rejected(e) => assert_eq!(e.class, susz::read::Class::Counts),
        o => panic!("{o:?}"),
    }
}

// The fast paths of the single pass read varints of up to 8 bytes with one
// load and hand anything else to the checked reader. Every byte of the
// base vector's MAIN and PROOFS is replaced by longer varint bytes (minimal
// or not, up to 10 bytes and past), with the directory and trailer moved to
// fit, so that the records around it are read through both paths. The
// single pass, the two-pass check and the lazy order agree on each, and on
// an accepted file hand out the same records.
#[test]
fn widened_bytes_read_alike() {
    let v = vectors::all()
        .into_iter()
        .find(|v| v.name == "blocks")
        .unwrap();
    let a = vectors::build(&v);
    let f = susz::read::File::open(&a.bytes).unwrap();
    let mut seqs: Vec<Vec<u8>> = vec![
        vec![0x80, 0x00],
        vec![0x80, 0x01],
        vec![0x81, 0x00],
        vec![0x82, 0x00],
        vec![0xff, 0x01],
        vec![0x80, 0x80, 0x00],
        vec![0x81, 0x80, 0x00],
        vec![0x80, 0x80, 0x01],
        vec![0xff, 0xff, 0x7f],
    ];
    for n in 4..=11 {
        let mut s = vec![0x80; n - 1];
        s.push(0x00);
        seqs.push(s.clone());
        s[0] = 0x81;
        seqs.push(s.clone());
        *s.last_mut().unwrap() = 0x01;
        seqs.push(s);
        let mut s = vec![0xff; n - 1];
        s.push(0x01);
        seqs.push(s);
    }
    let mut accepted = 0;
    for s in &f.sections {
        if s.id != susz::format::SEC_MAIN && s.id != susz::format::SEC_PROOFS {
            continue;
        }
        for i in s.offset..s.offset + s.length {
            for q in &seqs {
                let b = splice(&a.bytes, &f, i as usize, q);
                if let Err(e) = common::same_outcomes(&b) {
                    panic!("byte {i} replaced by {q:x?}: the single pass differs:\n{e}");
                }
                if matches!(susz::verify(&b), susz::Outcome::Accepted(_)) {
                    accepted += 1;
                    if let Err(e) = common::same_events(&b) {
                        panic!("byte {i} replaced by {q:x?}: {e}");
                    }
                }
            }
        }
    }
    assert!(accepted > 0);
}

// The file with byte `at` replaced by `with`: the section holding it grows,
// the later sections and the directory move.
fn splice(bytes: &[u8], f: &susz::read::File, at: usize, with: &[u8]) -> Vec<u8> {
    let grow = with.len() as u64 - 1;
    let mut out = bytes[..at].to_vec();
    out.extend_from_slice(with);
    out.extend_from_slice(&bytes[at + 1..]);
    let ts = f.trailer as usize + grow as usize;
    for (k, s) in f.sections.iter().enumerate() {
        let e = ts + 20 + 24 * k;
        let (mut off, mut len) = (s.offset, s.length);
        if (at as u64) < s.offset {
            off += grow;
        } else if (at as u64) < s.offset + s.length {
            len += grow;
        }
        out[e + 8..e + 16].copy_from_slice(&off.to_le_bytes());
        out[e + 16..e + 24].copy_from_slice(&len.to_le_bytes());
    }
    out
}
