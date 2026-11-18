// Slicing: every declaration as a root gives the input's bytes back; a
// slice is accepted, its INDEX verifies, every constant it names is declared
// in it, and slicing it again by the same roots changes nothing.
//
// init-prelude is in the repository and always runs; Init is #[ignore]
// (cargo test --release -- --ignored) and read from SUSZ_CORPORA (default
// ~/pestka-corpora), skipped when absent.

use std::io::Read;
use std::path::PathBuf;
use susz::pack::{pack_to_vec, Options};
use susz::read::{decode, BlockRef, Decl, Expr, File, Visit};
use susz::slice::{slice_to_vec, SliceError, SliceOptions};

fn tmp(name: &str) -> String {
    PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(name)
        .to_string_lossy()
        .into_owned()
}

// The committed init-prelude, packed once per test process.
fn init_prelude() -> Option<Vec<u8>> {
    static PACKED: std::sync::OnceLock<Option<Vec<u8>>> = std::sync::OnceLock::new();
    PACKED
        .get_or_init(|| {
            let gz = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("tests/corpus/init-prelude.ndjson.gz");
            let Ok(f) = std::fs::File::open(&gz) else {
                assert!(
                    !std::env::var("SUSZ_REQUIRE_CORPORA").is_ok_and(|v| v == "1"),
                    "{} is missing",
                    gz.display()
                );
                eprintln!("skipped: {} not found", gz.display());
                return None;
            };
            let mut text = Vec::new();
            flate2::read::GzDecoder::new(f)
                .read_to_end(&mut text)
                .unwrap();
            let nd = tmp(&format!("slice-prelude-{}.ndjson", std::process::id()));
            std::fs::write(&nd, &text).unwrap();
            let (b, _) = pack_to_vec(&nd, &Options::default()).unwrap();
            let _ = std::fs::remove_file(&nd);
            Some(b)
        })
        .clone()
}

fn opts(roots: &[&str], prefixes: &[&str], index: bool) -> SliceOptions {
    SliceOptions {
        roots: roots.iter().map(|s| s.to_string()).collect(),
        prefixes: prefixes.iter().map(|s| s.to_string()).collect(),
        index,
        threads: 1,
        progress: false,
    }
}

// The dotted names a file declares, and the names its constants and
// projections use that it does not declare (with `Nat` for a Nat literal,
// `String` for a string literal).
fn declared_and_dangling(bytes: &[u8]) -> (Vec<String>, Vec<String>) {
    #[derive(Default)]
    struct Uses(Vec<u32>, Vec<u32>, bool, bool);
    impl<'a> Visit<'a> for Uses {
        type Error = ();
        fn expr(&mut self, _: u32, e: &Expr<'a>) -> Result<(), ()> {
            self.block_expr(0, e)
        }
        fn block_expr(&mut self, _: u32, e: &Expr<'_>) -> Result<(), ()> {
            match e {
                Expr::Const(n, _) | Expr::Proj(n, ..) => self.0.push(*n),
                Expr::Nat(_) => self.2 = true,
                Expr::Str(_) => self.3 = true,
                _ => {}
            }
            Ok(())
        }
        fn open_block(&mut self, _: &BlockRef) -> bool {
            true
        }
        fn decl(&mut self, _: u32, _: u64, d: &Decl<'a>) -> Result<(), ()> {
            let mut f = |n: u32| self.1.push(n);
            match d {
                Decl::Inductive(ind) => {
                    ind.types.iter().for_each(|t| f(t.head.name));
                    ind.ctors.iter().for_each(|c| f(c.head.name));
                    ind.recs.iter().for_each(|r| f(r.head.name));
                }
                Decl::Axiom { head, .. }
                | Decl::Defn { head, .. }
                | Decl::Thm { head, .. }
                | Decl::Opaque { head, .. }
                | Decl::Quot { head, .. }
                | Decl::ThmBlock { head, .. } => f(head.name),
            }
            Ok(())
        }
    }
    let f = File::open(bytes).unwrap();
    let mut u = Uses::default();
    let st = decode(&f, &mut u).unwrap().state;
    let declared: Vec<String> = u.1.iter().map(|&n| st.name_display(bytes, n)).collect();
    let mut dangling: Vec<String> =
        u.0.iter()
            .filter(|&&n| st.canon_decl[st.name_canon[n as usize] as usize] == u32::MAX)
            .map(|&n| st.name_display(bytes, n))
            .collect();
    for (used, n) in [(u.2, "Nat"), (u.3, "String")] {
        if used && !declared.iter().any(|d| d == n) {
            dangling.push(n.to_string());
        }
    }
    dangling.sort();
    dangling.dedup();
    (declared, dangling)
}

fn check_slice(input: &[u8], roots: &[&str], tag: &str) -> Vec<u8> {
    let (out, st) = slice_to_vec(input, &opts(roots, &[], true)).unwrap();
    eprintln!("{tag}: {st}");
    match susz::verify(&out) {
        susz::Outcome::Accepted(_) => {}
        o => panic!("{tag}: {o:?}"),
    }
    let f = File::open(&out).unwrap();
    susz::index::verify_index(&f).unwrap();
    let (declared, dangling) = declared_and_dangling(&out);
    assert!(
        dangling.is_empty(),
        "{tag}: constants not declared in the slice: {dangling:?}"
    );
    for r in roots {
        assert!(declared.iter().any(|d| d == r), "{tag}: {r} is missing");
    }
    // a slice is closed: slicing it again by the same roots keeps everything
    let (again, st2) = slice_to_vec(&out, &opts(roots, &[], true)).unwrap();
    assert_eq!(st2.decls.0, st2.decls.1, "{tag}: the slice is not closed");
    assert!(again == out, "{tag}: slicing a slice changes it");
    // without INDEX: the same file but INDEX
    let (no_ix, _) = slice_to_vec(input, &opts(roots, &[], false)).unwrap();
    assert!(File::open(&no_ix)
        .unwrap()
        .section(susz::format::SEC_INDEX)
        .is_none());
    assert_eq!(
        susz::digest::of_susz(&no_ix).unwrap(),
        susz::digest::of_susz(&out).unwrap()
    );
    out
}

#[test]
fn slicing_everything_gives_the_same_bytes() {
    let Some(b) = init_prelude() else { return };
    for index in [true, false] {
        let input = if index {
            b.clone()
        } else {
            let (x, _) = slice_to_vec(&b, &opts(&[], &[""], false)).unwrap();
            x
        };
        let (out, st) = slice_to_vec(&input, &opts(&[], &[""], index)).unwrap();
        assert_eq!(st.decls.0, st.decls.1);
        assert!(out == input, "INDEX {index}: other bytes");
    }
}

#[test]
fn slices_of_init_prelude() {
    let Some(b) = init_prelude() else { return };
    // a theorem, a definition by recursion, a structure through its
    // constructor, the quotient, string and Nat literals
    for roots in [
        &["Nat.add"][..],
        &["Nat.le_refl"],
        &["Prod.mk"],
        &["Quot.lift"],
        &["Lean.Macro.throwUnsupported", "Nat.add"],
        &["Nat.decEq"],
    ] {
        let out = check_slice(&b, roots, &roots.join(","));
        assert!(out.len() < b.len());
    }
    // a constructor brings its inductive, the inductive its recursor
    let out = check_slice(&b, &["Nat.succ"], "Nat.succ");
    let (declared, _) = declared_and_dangling(&out);
    for n in ["Nat", "Nat.zero", "Nat.rec"] {
        assert!(declared.iter().any(|d| d == n), "{n} missing");
    }
    // a quotient brings all four
    let out = check_slice(&b, &["Quot.mk"], "Quot.mk");
    let (declared, _) = declared_and_dangling(&out);
    for n in ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"] {
        assert!(declared.iter().any(|d| d == n), "{n} missing");
    }
}

#[test]
fn prefixes_and_missing_roots() {
    let Some(b) = init_prelude() else { return };
    let (out, st) = slice_to_vec(&b, &opts(&[], &["Nat.add"], true)).unwrap();
    let (declared, dangling) = declared_and_dangling(&out);
    assert!(dangling.is_empty());
    assert!(st.roots >= 2);
    let f = File::open(&b).unwrap();
    let all = decode(&f, &mut Nothing).unwrap().state;
    // every declaration of the input under the prefix is kept
    for (c, &d) in all.canon_decl.iter().enumerate() {
        if d != u32::MAX {
            let s = all.canon.display(&b, c as u32);
            if s.starts_with("Nat.add") {
                assert!(declared.contains(&s), "{s} missing");
            }
        }
    }
    match slice_to_vec(&b, &opts(&["Nat.add", "No.Such.thing"], &[], true)) {
        Err(SliceError::NotFound(xs)) => assert_eq!(xs, vec!["No.Such.thing".to_string()]),
        r => panic!("{:?}", r.map(|x| x.1)),
    }
    match slice_to_vec(&b, &opts(&[], &["No.Such."], true)) {
        Err(SliceError::Empty) => {}
        r => panic!("{:?}", r.map(|x| x.1)),
    }
}

struct Nothing;
impl Visit<'_> for Nothing {
    type Error = ();
    fn open_block(&mut self, _: &BlockRef) -> bool {
        false
    }
}

#[test]
#[ignore]
fn slices_of_init() {
    let dir = std::env::var("SUSZ_CORPORA")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            PathBuf::from(std::env::var("HOME").unwrap_or_default()).join("pestka-corpora")
        });
    let p = dir.join("init.ndjson");
    if !p.exists() {
        eprintln!("skipped: {} not found", p.display());
        return;
    }
    let (b, _) = pack_to_vec(&p.to_string_lossy(), &Options::default()).unwrap();
    let (out, _) = slice_to_vec(&b, &opts(&[], &[""], true)).unwrap();
    assert!(out == b, "Init: slicing everything gives other bytes");
    for roots in [
        &["Nat.add_comm"][..],
        &["Lean.Syntax"],
        &["Lean.Macro.Context"],
        &["Quotient.sound"],
        &["Lean.Name.toString"],
        &["List.length_append", "Nat.gcd_comm"],
    ] {
        check_slice(&b, roots, &roots.join(","));
    }
}
