// isReflexive left out (Lean since lean4#16595, whose InductiveVal has no
// such field; a kernel computes it). A type with the flags may come without
// it: such a block is kind 8, the file has FLAGS and NOREFL, readers give
// `None`, unpacking leaves the key out again, and both digests agree on the
// ndjson and the Susz file. Exports that carry it pack as before. The
// fixture is a test of lean-kernel-arena-beta's renovation directory
// exported by Lean pr-release-16595-55bd690 (ImpMutB: a mutual block of two
// types).

use std::path::PathBuf;
use susz::digest::{self, View};
use susz::format;
use susz::pack::{pack_to_vec, Decl, Fault, Head, IndFlags, IndType, Options, PackError, Packer};
use susz::read::{Decl as RDecl, Event, File};

const IMPMUTB: &str = include_str!("renovation/impmutb-norefl.ndjson");
const SBOOL: &str = include_str!("renovation/sbool-3.2.ndjson");

fn tmp(name: &str, text: &str) -> String {
    static N: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let p = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("refl-{}-{n}-{name}", std::process::id()));
    std::fs::write(&p, text).unwrap();
    p.to_string_lossy().into_owned()
}

fn pack(name: &str, text: &str) -> Result<Vec<u8>, PackError> {
    let p = tmp(name, text);
    let one = pack_to_vec(
        &p,
        &Options {
            index: true,
            threads: 1,
        },
    )
    .map(|r| r.0);
    let many = pack_to_vec(
        &p,
        &Options {
            index: true,
            threads: 4,
        },
    )
    .map(|r| r.0);
    match (&one, &many) {
        (Ok(a), Ok(b)) => assert_eq!(a, b, "{name}: threads change the bytes"),
        (Err(a), Err(b)) => assert_eq!(a.fault, b.fault, "{name}"),
        _ => panic!("{name}: one and four workers disagree"),
    }
    one
}

// (kind byte, each type's isReflexive)
fn blocks(bytes: &[u8]) -> Vec<(u8, Vec<Option<bool>>)> {
    let f = File::open(bytes).unwrap();
    let mut out = Vec::new();
    for ev in f.main() {
        if let Event::Decl { decl, .. } = ev.unwrap() {
            if let RDecl::Inductive(ind) = &decl {
                out.push((
                    decl.kind(),
                    ind.types.iter().map(|t| t.is_reflexive).collect(),
                ));
            }
        }
    }
    out
}

fn has(bytes: &[u8], id: u16) -> bool {
    File::open(bytes).unwrap().section(id).is_some()
}

fn unpacked(bytes: &[u8]) -> String {
    let mut out = Vec::new();
    susz::unpack::unpack(bytes, &mut out).unwrap();
    String::from_utf8(out).unwrap()
}

fn nd_digest(text: &str, view: View) -> Result<digest::Hash, digest::Error> {
    digest::ndjson_view(text.as_bytes(), view, false, &mut |_| Ok(())).map(|s| s.digest)
}

fn susz_digest(bytes: &[u8], view: View) -> digest::Hash {
    digest::susz_view(bytes, view, false, &mut |_| Ok(()))
        .unwrap()
        .digest
}

fn strip_reflexive(text: &str) -> String {
    text.replace("\"isReflexive\":false,", "")
        .replace("\"isReflexive\":true,", "")
}

// An export of the renovated Lean: kind 8, FLAGS and NOREFL, `None` read
// back, the same ndjson unpacked, digests equal.
#[test]
fn left_out_is_kind_8() {
    for (name, text) in [
        ("impmutb", IMPMUTB.to_string()),
        ("sbool", strip_reflexive(SBOOL)),
    ] {
        assert!(!text.contains("isReflexive"));
        let bytes = pack(name, &text).unwrap();
        assert!(matches!(susz::verify(&bytes), susz::Outcome::Accepted(_)));
        assert!(has(&bytes, format::SEC_FLAGS));
        assert!(has(&bytes, format::SEC_NOREFL));
        let b = blocks(&bytes);
        assert_eq!(b.len(), 1);
        assert_eq!(b[0].0, 8);
        assert!(b[0].1.iter().all(|r| r.is_none()));
        assert_eq!(unpacked(&bytes), text, "{name}: unpack");
        for view in [View::Exact, View::Kernel] {
            assert_eq!(nd_digest(&text, view).unwrap(), susz_digest(&bytes, view));
        }
    }
    let b = blocks(&pack("impmutb", IMPMUTB).unwrap());
    assert_eq!(b[0].1.len(), 2);
}

// "Not given" is a different declaration from false and from true.
#[test]
fn digests_see_it_left_out() {
    let none = strip_reflexive(SBOOL);
    let f = SBOOL.to_string();
    let t = SBOOL.replace("\"isReflexive\":false", "\"isReflexive\":true");
    for view in [View::Exact, View::Kernel] {
        let d: Vec<_> = [&none, &f, &t]
            .iter()
            .map(|x| nd_digest(x, view).unwrap())
            .collect();
        assert_ne!(d[0], d[1]);
        assert_ne!(d[0], d[2]);
        assert_ne!(d[1], d[2]);
    }
}

// Only a type with the flags may leave it out: without them it is a
// missing key (exit 1), as before.
#[test]
fn left_out_without_flags_is_refused() {
    let flags = r#""hasEta":false,"hasLargeElim":false,"hasProjections":false,"isImpredicative":false,"isK":false,"#;
    let text = strip_reflexive(SBOOL)
        .replace(flags, "")
        .replace("\"version\":\"3.2.0\"", "\"version\":\"3.1.0\"");
    assert!(!text.contains("hasEta"));
    let e = pack("noflags", &text).unwrap_err();
    assert_eq!(e.fault, Fault::Invalid, "{}", e.msg);
    assert!(matches!(
        nd_digest(&text, View::Exact),
        Err(digest::Error::Invalid { .. })
    ));
}

// An export carries it on every type or on none: within a block and
// across blocks, in either order, the packer and the digest refuse a mix.
#[test]
fn mixed_is_refused() {
    // in one block: ImpMutB's second type keeps a key
    let one = IMPMUTB.replacen(
        "\"isRec\":false,",
        "\"isRec\":false,\"isReflexive\":false,",
        1,
    );
    assert_ne!(one, IMPMUTB);
    assert_eq!(pack("mixed-block", &one).unwrap_err().fault, Fault::Invalid);
    assert!(matches!(
        nd_digest(&one, View::Exact),
        Err(digest::Error::Invalid { .. })
    ));
    // across blocks
    let head = "{\"meta\":{\"exporter\":{\"name\":\"t\",\"version\":\"0\"},\"format\":{\"version\":\"3.2.0\"}}}\n\
{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A\"}}\n\
{\"in\":2,\"str\":{\"pre\":0,\"str\":\"B\"}}\n\
{\"ie\":0,\"sort\":0}\n";
    let ind = |n: u64, refl: bool| {
        format!(
            "{{\"inductive\":{{\"ctors\":[],\"recs\":[],\"types\":[{{\"all\":[{n}],\"ctors\":[],\"hasEta\":false,\"hasLargeElim\":false,\"hasProjections\":false,\"isImpredicative\":false,\"isK\":false,\"isRec\":false,{}\"isUnsafe\":false,\"levelParams\":[],\"name\":{n},\"numIndices\":0,\"numNested\":0,\"numParams\":0,\"type\":0}}]}}}}\n",
            if refl { "\"isReflexive\":false," } else { "" }
        )
    };
    for r in [false, true] {
        let text = format!("{head}{}{}", ind(1, r), ind(2, r));
        let bytes = pack("same", &text).unwrap();
        assert_eq!(has(&bytes, format::SEC_NOREFL), !r);
        assert!(blocks(&bytes).iter().all(|b| b.0 == if r { 7 } else { 8 }));
        assert_eq!(unpacked(&bytes), text);
    }
    for first in [false, true] {
        let text = format!("{head}{}{}", ind(1, first), ind(2, !first));
        let e = pack("mixed", &text).unwrap_err();
        assert_eq!(e.fault, Fault::Invalid, "{}", e.msg);
        assert!(matches!(
            nd_digest(&text, View::Exact),
            Err(digest::Error::Invalid { .. })
        ));
    }
}

fn ty(name: u64, refl: Option<bool>, flags: Option<IndFlags>) -> IndType {
    IndType {
        head: Head {
            name,
            level_params: vec![],
            ty: 0,
        },
        is_unsafe: false,
        num_params: 0,
        num_indices: 0,
        all: vec![name],
        ctors: vec![],
        num_nested: 0,
        is_rec: false,
        is_reflexive: refl,
        flags,
    }
}

fn packer() -> Packer {
    let mut p = Packer::new();
    p.meta(r#"{"exporter":{"name":"t","version":"0"},"format":{"version":"3.2.0"}}"#)
        .unwrap();
    p.name_str(1, 0, "A").unwrap();
    p.name_str(2, 0, "B").unwrap();
    p.sort(0, 0).unwrap();
    p
}

// The record API: `None` with flags writes kind 8; `None` without flags,
// and a mix across blocks, are refused.
#[test]
fn packer_api() {
    let f = Some(IndFlags::default());
    let mut p = packer();
    p.decl(&Decl::Inductive {
        types: vec![ty(1, None, f)],
        ctors: vec![],
        recs: vec![],
    })
    .unwrap();
    let (bytes, _) = p.to_vec(&Options::default()).unwrap();
    assert_eq!(blocks(&bytes), vec![(8, vec![None])]);

    let mut p = Packer::new();
    p.meta(r#"{"exporter":{"name":"t","version":"0"},"format":{"version":"3.1.0"}}"#)
        .unwrap();
    p.name_str(1, 0, "A").unwrap();
    p.sort(0, 0).unwrap();
    let e = p
        .decl(&Decl::Inductive {
            types: vec![ty(1, None, None)],
            ctors: vec![],
            recs: vec![],
        })
        .unwrap_err();
    assert_eq!(e.fault, Fault::Invalid);

    let mut p = packer();
    for (n, r) in [(1, None), (2, Some(false))] {
        p.decl(&Decl::Inductive {
            types: vec![ty(n, r, f)],
            ctors: vec![],
            recs: vec![],
        })
        .unwrap();
    }
    assert_eq!(
        p.to_vec(&Options::default()).unwrap_err().fault,
        Fault::Invalid
    );
}

// A slice keeps a kind-8 block and NOREFL.
#[test]
fn slice_keeps_it_left_out() {
    let bytes = pack("impmutb", IMPMUTB).unwrap();
    let opts = susz::slice::SliceOptions {
        roots: vec!["ImpMutA".into()],
        prefixes: vec![],
        index: true,
        threads: 1,
        progress: false,
    };
    let (out, _) = susz::slice::slice_to_vec(&bytes, &opts).unwrap();
    assert!(has(&out, format::SEC_NOREFL));
    assert!(blocks(&out).iter().all(|b| b.0 == 8));
}
