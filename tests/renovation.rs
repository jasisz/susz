// The flags of lean4export 3.2 (lean4#16595): an inductive type carries
// isImpredicative, isK, hasProjections, hasEta and hasLargeElim, or nothing.
// Packing, reading, unpacking and the digests keep them, keep "no flags"
// apart from "every flag off", and refuse a 3.2 export whose types lack
// them. The fixtures are two tests of lean-kernel-arena's renovation
// directory: SBool (a type without large elimination, whose recursor has
// no rules) and LAnd (a proposition with projections, eta and large
// elimination).

use std::path::PathBuf;
use susz::digest::{self, View};
use susz::format;
use susz::pack::{pack_to_vec, Decl, Fault, Head, IndFlags, IndType, Options, PackError, Packer};
use susz::read::{Decl as RDecl, Event, File};

const SBOOL: &str = include_str!("renovation/sbool-3.2.ndjson");
const LAND: &str = include_str!("renovation/land-3.2.ndjson");
const FLAG_KEYS: &str = r#""hasEta":false,"hasLargeElim":false,"hasProjections":false,"isImpredicative":false,"isK":false,"#;

fn tmp(name: &str, text: &str) -> String {
    static N: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let p = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("renov-{}-{n}-{name}", std::process::id()));
    std::fs::write(&p, text).unwrap();
    p.to_string_lossy().into_owned()
}

fn pack(name: &str, text: &str) -> Result<Vec<u8>, PackError> {
    let opts = Options {
        index: true,
        threads: 1,
    };
    let p = tmp(name, text);
    let one = pack_to_vec(&p, &opts).map(|r| r.0);
    // several workers write the same bytes
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

fn to_31(text: &str) -> String {
    text.replace("\"version\":\"3.2.0\"", "\"version\":\"3.1.0\"")
}

fn strip_flags(text: &str) -> String {
    let s = text.replace(FLAG_KEYS, "");
    // LAnd's flags are not all off
    s.replace(
        r#""hasEta":true,"hasLargeElim":true,"hasProjections":true,"isImpredicative":false,"isK":false,"#,
        "",
    )
}

// The inductive blocks of a file: (kind byte, each type's flags, each
// recursor's number of rules).
fn blocks(bytes: &[u8]) -> Vec<(u8, Vec<Option<IndFlags>>, Vec<usize>)> {
    let f = File::open(bytes).unwrap();
    let mut out = Vec::new();
    for ev in f.main() {
        if let Event::Decl { decl, .. } = ev.unwrap() {
            if let RDecl::Inductive(ind) = &decl {
                out.push((
                    decl.kind(),
                    ind.types.iter().map(|t| t.flags).collect(),
                    ind.recs.iter().map(|r| r.rules.len()).collect(),
                ));
            }
        }
    }
    out
}

fn has_flags_section(bytes: &[u8]) -> bool {
    File::open(bytes)
        .unwrap()
        .section(format::SEC_FLAGS)
        .is_some()
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

// 3.2.0 with flags: kind 7, FLAGS, the flags read back, ndjson again byte
// for byte; a recursor without rules (eliminating only into Prop).
#[test]
fn flags_of_32_are_kept() {
    for (name, text, want) in [
        ("sbool", SBOOL, IndFlags::default()),
        (
            "land",
            LAND,
            IndFlags {
                has_projections: true,
                has_eta: true,
                has_large_elim: true,
                ..IndFlags::default()
            },
        ),
    ] {
        let bytes = pack(name, text).unwrap();
        assert!(matches!(susz::verify(&bytes), susz::Outcome::Accepted(_)));
        assert!(has_flags_section(&bytes));
        let b = blocks(&bytes);
        assert_eq!(b.len(), 1);
        assert_eq!(b[0].0, 7);
        assert_eq!(b[0].1, vec![Some(want)]);
        assert_eq!(unpacked(&bytes), text, "{name}: unpack");
        for view in [View::Exact, View::Kernel] {
            assert_eq!(nd_digest(text, view).unwrap(), susz_digest(&bytes, view));
        }
    }
    // SBool.rec eliminates only into Prop: no rules
    let b = blocks(&pack("sbool", SBOOL).unwrap());
    assert_eq!(b[0].2, vec![0]);
}

// 3.1.0 without flags: as before, kind 5 and no FLAGS.
#[test]
fn no_flags_under_31() {
    let text = strip_flags(&to_31(SBOOL));
    let bytes = pack("sbool-31", &text).unwrap();
    assert!(!has_flags_section(&bytes));
    let b = blocks(&bytes);
    assert_eq!((b[0].0, b[0].1.clone()), (5, vec![None]));
    assert_eq!(unpacked(&bytes), text);
    for view in [View::Exact, View::Kernel] {
        assert_eq!(nd_digest(&text, view).unwrap(), susz_digest(&bytes, view));
    }
}

// Flags are taken where they are, whatever the version says: 3.1.0 with
// flags packs as 3.2.0 does, but for SOURCE.
#[test]
fn flags_under_31_are_read() {
    let text = to_31(SBOOL);
    let bytes = pack("sbool-31-flags", &text).unwrap();
    assert!(has_flags_section(&bytes));
    assert_eq!(blocks(&bytes)[0].1, vec![Some(IndFlags::default())]);
    let f31 = File::open(&bytes).unwrap();
    let b32 = pack("sbool", SBOOL).unwrap();
    let f32 = File::open(&b32).unwrap();
    let main = |f: &File, b: &[u8]| {
        let s = f.section(format::SEC_MAIN).unwrap();
        b[s.offset as usize..(s.offset + s.length) as usize].to_vec()
    };
    assert_eq!(main(&f31, &bytes), main(&f32, &b32));
    assert_eq!(
        nd_digest(&text, View::Exact).unwrap(),
        nd_digest(SBOOL, View::Exact).unwrap()
    );
}

// 3.2.0 without flags is not a valid export: the packer and the digest
// refuse it (exit 1), it is not read by the old rules.
#[test]
fn no_flags_under_32_is_refused() {
    let text = strip_flags(SBOOL);
    let e = pack("sbool-32-noflags", &text).unwrap_err();
    assert_eq!(e.fault, Fault::Invalid, "{}", e.msg);
    assert!(matches!(
        nd_digest(&text, View::Exact),
        Err(digest::Error::Invalid { .. })
    ));
}

// Some of the five keys but not all: a missing key (exit 1).
#[test]
fn some_flags_are_refused() {
    let text = SBOOL.replace("\"hasEta\":false,", "");
    assert_eq!(pack("partial", &text).unwrap_err().fault, Fault::Invalid);
    assert!(matches!(
        nd_digest(&text, View::Exact),
        Err(digest::Error::Invalid { .. })
    ));
    // and under 3.1 too
    assert_eq!(
        pack("partial-31", &to_31(&text)).unwrap_err().fault,
        Fault::Invalid
    );
}

// "No flags" and "every flag off" are different declarations, and each
// flag counts, in both digests.
#[test]
fn digests_see_the_flags() {
    let off = to_31(SBOOL);
    let none = strip_flags(&off);
    for view in [View::Exact, View::Kernel] {
        let d_off = nd_digest(&off, view).unwrap();
        assert_ne!(d_off, nd_digest(&none, view).unwrap());
        for k in IndFlags::KEYS {
            let on = off.replace(&format!("\"{k}\":false"), &format!("\"{k}\":true"));
            assert_ne!(on, off);
            let d_on = nd_digest(&on, view).unwrap();
            assert_ne!(d_on, d_off, "{k}");
            assert_eq!(d_on, susz_digest(&pack("flip", &on).unwrap(), view));
        }
    }
}

fn head(name: u64) -> Head {
    Head {
        name,
        level_params: vec![],
        ty: 0,
    }
}

fn ty(name: u64, all: Vec<u64>, flags: Option<IndFlags>) -> IndType {
    IndType {
        head: head(name),
        is_unsafe: false,
        num_params: 0,
        num_indices: 0,
        all,
        ctors: vec![],
        num_nested: 0,
        is_rec: false,
        is_reflexive: false,
        flags,
    }
}

fn packer(version: &str) -> Packer {
    let mut p = Packer::new();
    p.meta(&format!(
        r#"{{"exporter":{{"name":"t","version":"0"}},"format":{{"version":"{version}"}}}}"#
    ))
    .unwrap();
    p.name_str(1, 0, "A").unwrap();
    p.name_str(2, 0, "B").unwrap();
    p.sort(0, 0).unwrap();
    p
}

// The record API carries the flags, and writes what pack writes from the
// same records as ndjson.
#[test]
fn packer_api_carries_flags() {
    let f = IndFlags {
        is_impredicative: true,
        ..IndFlags::default()
    };
    let mut p = packer("3.2.0");
    p.decl(&Decl::Inductive {
        types: vec![ty(1, vec![1], Some(f))],
        ctors: vec![],
        recs: vec![],
    })
    .unwrap();
    let (bytes, _) = p.to_vec(&Options::default()).unwrap();
    let nd = "{\"meta\":{\"exporter\":{\"name\":\"t\",\"version\":\"0\"},\"format\":{\"version\":\"3.2.0\"}}}\n\
{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A\"}}\n\
{\"in\":2,\"str\":{\"pre\":0,\"str\":\"B\"}}\n\
{\"ie\":0,\"sort\":0}\n\
{\"inductive\":{\"ctors\":[],\"recs\":[],\"types\":[{\"all\":[1],\"ctors\":[],\"hasEta\":false,\"hasLargeElim\":false,\"hasProjections\":false,\"isImpredicative\":true,\"isK\":false,\"isRec\":false,\"isReflexive\":false,\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"numIndices\":0,\"numNested\":0,\"numParams\":0,\"type\":0}]}}\n";
    assert_eq!(bytes, pack("api", nd).unwrap());
    assert_eq!(blocks(&bytes)[0].1, vec![Some(f)]);
    assert_eq!(unpacked(&bytes), nd);

    // under 3.2 a type without flags is refused
    let mut p = packer("3.2.0");
    let e = p
        .decl(&Decl::Inductive {
            types: vec![ty(1, vec![1], None)],
            ctors: vec![],
            recs: vec![],
        })
        .unwrap_err();
    assert_eq!(e.fault, Fault::Invalid);

    // the types of a block agree on carrying flags
    for v in ["3.1.0", "3.2.0"] {
        let mut p = packer(v);
        let e = p
            .decl(&Decl::Inductive {
                types: vec![ty(1, vec![1, 2], Some(f)), ty(2, vec![1, 2], None)],
                ctors: vec![],
                recs: vec![],
            })
            .unwrap_err();
        assert_eq!(e.fault, Fault::Invalid);
    }
}

// An export is flagged throughout or not at all: inductive types with and
// without flags in different blocks are refused (exit 1) by the packer, the
// record API and the digest, in either order.
#[test]
fn mixed_blocks_are_refused() {
    let head = "{\"meta\":{\"exporter\":{\"name\":\"t\",\"version\":\"0\"},\"format\":{\"version\":\"3.1.0\"}}}\n\
{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A\"}}\n\
{\"in\":2,\"str\":{\"pre\":0,\"str\":\"B\"}}\n\
{\"ie\":0,\"sort\":0}\n";
    let ind = |n: u64, flags: bool| {
        format!(
            "{{\"inductive\":{{\"ctors\":[],\"recs\":[],\"types\":[{{\"all\":[{n}],\"ctors\":[],{}\"isRec\":false,\"isReflexive\":false,\"isUnsafe\":false,\"levelParams\":[],\"name\":{n},\"numIndices\":0,\"numNested\":0,\"numParams\":0,\"type\":0}}]}}}}\n",
            if flags { FLAG_KEYS } else { "" }
        )
    };
    // both flagged, or neither: packed
    for f in [false, true] {
        let text = format!("{head}{}{}", ind(1, f), ind(2, f));
        let bytes = pack("same", &text).unwrap();
        assert_eq!(has_flags_section(&bytes), f);
        assert!(blocks(&bytes).iter().all(|b| b.0 == if f { 7 } else { 5 }));
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
        let f = IndFlags::default();
        let mut p = packer("3.1.0");
        for (n, x) in [(1, first), (2, !first)] {
            p.decl(&Decl::Inductive {
                types: vec![ty(n, vec![n], x.then_some(f))],
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
}

// Another major version of the format is still declined, and a version
// other than 3.1 and 3.2 still cannot be packed.
#[test]
fn other_versions_cannot_be_packed() {
    let text = SBOOL.replace("\"version\":\"3.2.0\"}", "\"version\":\"3.3.0\"}");
    assert_ne!(text, SBOOL);
    assert_eq!(pack("v33", &text).unwrap_err().fault, Fault::Cannot);
}

// A slice keeps the flags.
#[test]
fn slice_keeps_flags() {
    let bytes = pack("land", LAND).unwrap();
    let opts = susz::slice::SliceOptions {
        roots: vec!["LAnd".into()],
        prefixes: vec![],
        index: true,
        threads: 1,
        progress: false,
    };
    let (out, _) = susz::slice::slice_to_vec(&bytes, &opts).unwrap();
    assert_eq!(out, bytes);
    assert!(has_flags_section(&out));
    assert!(blocks(&out).iter().all(|b| b.0 == 7));
}
