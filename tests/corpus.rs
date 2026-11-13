// Real exports: packing is deterministic (threads, INDEX on/off), the
// packed file is accepted, holds the export's declarations (digest against
// the ndjson, read independently), unpacks to an export that packs to the
// same bytes, and its INDEX verifies. Packer exit classes on broken inputs.
//
// init-prelude is in the repository (tests/corpus/, gzipped) and always
// runs. The larger corpora live outside it: SUSZ_CORPORA (default
// ~/pestka-corpora), and are skipped when absent. Init is #[ignore]:
// cargo test --release -- --ignored. With SUSZ_REQUIRE_CORPORA=1 (as in CI)
// a missing init-prelude fails instead of skipping.

mod common;

use std::io::Read;
use std::path::PathBuf;
use susz::pack::{pack_to_vec, Fault, Options};

fn required() -> bool {
    std::env::var("SUSZ_REQUIRE_CORPORA").is_ok_and(|v| v == "1")
}

// The committed init-prelude, unzipped once per test process.
fn init_prelude() -> Option<String> {
    static PATH: std::sync::OnceLock<Option<String>> = std::sync::OnceLock::new();
    PATH.get_or_init(|| {
        let gz =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/corpus/init-prelude.ndjson.gz");
        let Ok(f) = std::fs::File::open(&gz) else {
            assert!(!required(), "{} is missing", gz.display());
            eprintln!("skipped: {} not found", gz.display());
            return None;
        };
        let mut text = Vec::new();
        flate2::read::GzDecoder::new(f)
            .read_to_end(&mut text)
            .unwrap();
        let out = tmp(&format!("init-prelude-{}.ndjson", std::process::id()));
        std::fs::write(&out, &text).unwrap();
        Some(out)
    })
    .clone()
}

// A corpus from SUSZ_CORPORA; skipped when absent.
fn corpus(name: &str) -> Option<String> {
    let dir = std::env::var("SUSZ_CORPORA")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            PathBuf::from(std::env::var("HOME").unwrap_or_default()).join("pestka-corpora")
        });
    let p = dir.join(name);
    if p.exists() {
        Some(p.to_string_lossy().into_owned())
    } else {
        eprintln!("skipped: {} not found", p.display());
        None
    }
}

fn tmp(name: &str) -> String {
    PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(name)
        .to_string_lossy()
        .into_owned()
}

fn opts(index: bool, threads: usize) -> Options {
    Options { index, threads }
}

fn sections_except_index(b: &[u8]) -> Vec<(u16, Vec<u8>)> {
    let f = susz::read::File::open(b).unwrap();
    f.sections
        .iter()
        .filter(|s| s.id != susz::format::SEC_INDEX)
        .map(|s| (s.id, f.body(*s).to_vec()))
        .collect()
}

fn check_export(path: &str, tag: &str, threads: &[usize]) {
    let (with, st) = pack_to_vec(path, &opts(true, 1)).unwrap();
    eprintln!("{tag}: {st}");
    for &t in threads {
        let (b, _) = pack_to_vec(path, &opts(true, t)).unwrap();
        assert!(b == with, "{tag}: {t} threads give other bytes");
    }
    let (without, _) = pack_to_vec(path, &opts(false, 1)).unwrap();
    for &t in threads {
        let (b, _) = pack_to_vec(path, &opts(false, t)).unwrap();
        assert!(
            b == without,
            "{tag}: {t} threads give other bytes without INDEX"
        );
    }
    // the two settings differ only by INDEX
    assert_eq!(
        sections_except_index(&with),
        sections_except_index(&without)
    );
    assert!(susz::read::File::open(&without)
        .unwrap()
        .section(susz::format::SEC_INDEX)
        .is_none());
    // accepted, same digest as the export; the single pass agrees with the
    // two-pass check and hands out the records the iterators read
    for b in [&with, &without] {
        match susz::verify(b) {
            susz::Outcome::Accepted(_) => {}
            o => panic!("{tag}: {o:?}"),
        }
        common::same_outcomes(b).unwrap_or_else(|e| panic!("{tag}: {e}"));
        common::same_events(b).unwrap_or_else(|e| panic!("{tag}: {e}"));
    }
    let d = susz::digest::of_susz(&with).unwrap();
    assert_eq!(d, susz::digest::of_susz(&without).unwrap());
    assert_eq!(
        d,
        susz::digest::of_ndjson(path).unwrap(),
        "{tag}: the packed file does not hold the export's declarations"
    );
    // INDEX
    let f = susz::read::File::open(&with).unwrap();
    susz::index::verify_index(&f).unwrap();
    let ix = susz::index::parse(&f).unwrap();
    assert!(ix.expanded());
    let scan = susz::index::parse_capped(&f, 0).unwrap();
    let mut many = susz::index::Lookup::new(&f).unwrap();
    let step = (ix.len() / 50).max(1);
    for j in (0..ix.len()).step_by(step).take(60) {
        let (k, d) = (ix.key(j), ix.decl(j));
        assert_eq!(scan.find(&k), Some(d));
        assert_eq!(susz::index::lookup(&f, &k).unwrap().decl, d);
        assert_eq!(many.find(&k).unwrap().decl, d);
    }
    // unpack, pack again: the same bytes
    let nd = tmp(&format!("{tag}.unpacked.ndjson"));
    let mut w = std::io::BufWriter::new(std::fs::File::create(&nd).unwrap());
    susz::unpack::unpack(&with, &mut w).unwrap();
    drop(w);
    let (again, _) = pack_to_vec(&nd, &opts(true, 1)).unwrap();
    assert!(
        again == with,
        "{tag}: unpack + pack does not give the same bytes"
    );
    assert_eq!(susz::digest::of_ndjson(&nd).unwrap(), d);
    let _ = std::fs::remove_file(&nd);
}

#[test]
fn init_prelude_packs() {
    if let Some(p) = init_prelude() {
        check_export(&p, "init-prelude", &[2, 4, 8]);
    }
}

#[test]
#[ignore]
fn init() {
    if let Some(p) = corpus("init.ndjson") {
        check_export(&p, "init", &[4]);
    }
}

// Exit classes: a broken export is Invalid (exit 1), an export the packer
// does not understand is Cannot (exit 2).
#[test]
fn broken_inputs() {
    let Some(p) = init_prelude() else {
        return;
    };
    let text = std::fs::read_to_string(&p).unwrap();
    let lines: Vec<&str> = text.lines().collect();
    let find = |pre: &str| lines.iter().position(|l| l.starts_with(pre)).unwrap();
    let with = |i: usize, new: &str| -> String {
        let mut ls: Vec<String> = lines.iter().map(|s| s.to_string()).collect();
        ls[i] = new.to_string();
        ls.join("\n") + "\n"
    };
    let app = find("{\"app\":");
    let thm = find("{\"thm\":");
    let quot = find("{\"quot\":");
    let cases: Vec<(&str, String, Fault)> = vec![
        (
            "malformed-json",
            with(app, "{\"app\":{\"arg\":1,"),
            Fault::Invalid,
        ),
        (
            "dangling-expr",
            with(app, "{\"app\":{\"arg\":99999999,\"fn\":0},\"ie\":5}"),
            Fault::Invalid,
        ),
        (
            "duplicate-expr-id",
            with(
                app,
                &lines[app].replace(&format!("\"ie\":{}", app_ie(lines[app])), "\"ie\":0"),
            ),
            Fault::Invalid,
        ),
        (
            "truncated",
            lines[..thm].join("\n") + "\n" + &lines[thm][..lines[thm].len() / 2],
            Fault::Invalid,
        ),
        (
            "unknown-kind",
            with(app, &lines[app].replace("\"app\"", "\"apq\"")),
            Fault::Cannot,
        ),
        (
            "unknown-field",
            with(
                thm,
                &lines[thm].replace("{\"thm\":{", "{\"thm\":{\"extra\":1,"),
            ),
            Fault::Cannot,
        ),
        (
            "unknown-decl-kind",
            with(thm, &lines[thm].replace("{\"thm\":", "{\"lemma\":")),
            Fault::Cannot,
        ),
        (
            "format-2",
            with(
                0,
                &lines[0].replace(
                    "\"format\":{\"version\":\"3.1.0\"}",
                    "\"format\":{\"version\":\"2.0.0\"}",
                ),
            ),
            Fault::Cannot,
        ),
        (
            "declared-twice",
            {
                let mut ls: Vec<String> = lines.iter().map(|s| s.to_string()).collect();
                ls.push(lines[quot].to_string());
                ls.join("\n") + "\n"
            },
            Fault::Invalid,
        ),
        (
            "negative-nat",
            text.clone() + "{\"ie\":999999,\"natVal\":\"-1\"}\n",
            Fault::Invalid,
        ),
        ("empty", String::new(), Fault::Invalid),
    ];
    for (name, body, want) in cases {
        let path = tmp(&format!("broken-{name}.ndjson"));
        std::fs::write(&path, body).unwrap();
        match pack_to_vec(&path, &opts(true, 1)) {
            Ok(_) => panic!("{name}: packed"),
            Err(e) => assert_eq!(e.fault, want, "{name}: {e}"),
        }
        // the parallel read gives the same class
        if let Err(e) = pack_to_vec(&path, &opts(true, 4)) {
            assert_eq!(e.fault, want, "{name} (4 threads): {e}");
        }
        let _ = std::fs::remove_file(&path);
    }
}

fn app_ie(l: &str) -> u64 {
    let i = l.rfind("\"ie\":").unwrap() + 5;
    l[i..].trim_end_matches('}').parse().unwrap()
}

// mdata is not written: references go to the wrapped expression.
#[test]
fn mdata_is_dropped() {
    let a = "{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}\n\
{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A\"}}\n\
{\"ie\":0,\"sort\":0}\n\
{\"ie\":1,\"mdata\":{\"data\":{\"x\":1},\"expr\":0}}\n\
{\"ie\":2,\"mdata\":{\"data\":{},\"expr\":1}}\n\
{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":2}}\n";
    let b = "{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}\n\
{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A\"}}\n\
{\"ie\":0,\"sort\":0}\n\
{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}\n";
    let (pa, pb) = (tmp("mdata-a.ndjson"), tmp("mdata-b.ndjson"));
    std::fs::write(&pa, a).unwrap();
    std::fs::write(&pb, b).unwrap();
    let (x, _) = pack_to_vec(&pa, &opts(true, 1)).unwrap();
    let (y, _) = pack_to_vec(&pb, &opts(true, 1)).unwrap();
    assert!(x == y);
    assert_eq!(
        susz::digest::of_ndjson(&pa).unwrap(),
        susz::digest::of_susz(&x).unwrap()
    );
}

// Lines in lean4export's canonical form are read by position, any other
// through the JSON parser: an export written otherwise (other spacing or key
// order, escapes, leading zeros, long names) packs to the same bytes.
#[test]
fn fast_and_slow_paths_agree() {
    let head = "{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}\n";
    // names of every length up to 24, some not ASCII, crossing word bounds
    let mut names: Vec<String> = Vec::new();
    for n in 1..=24usize {
        let s: String = (0..n).map(|i| (b'a' + (i % 26) as u8) as char).collect();
        names.push(s);
    }
    names.push("é".into());
    names.push("xℕ".into());
    names.push("αβγδεζηθικ".into());
    names.push("a\"b".into());
    names.push("back\\slash".into());
    names.push("new\nline".into());
    let json_str = |s: &str| -> String {
        let mut o = String::from("\"");
        for c in s.chars() {
            match c {
                '"' => o.push_str("\\\""),
                '\\' => o.push_str("\\\\"),
                '\n' => o.push_str("\\n"),
                c => o.push(c),
            }
        }
        o.push('"');
        o
    };
    // every character as \uXXXX (surrogate pairs above the BMP)
    let json_u = |s: &str| -> String {
        let mut o = String::from("\"");
        for c in s.chars() {
            let mut b = [0u16; 2];
            for u in c.encode_utf16(&mut b) {
                o.push_str(&format!("\\u{:04x}", u));
            }
        }
        o.push('"');
        o
    };
    let mut canon = String::from(head);
    let mut other = String::from(head);
    for (i, s) in names.iter().enumerate() {
        let id = i + 1;
        canon.push_str(&format!(
            "{{\"in\":{id},\"str\":{{\"pre\":0,\"str\":{}}}}}\n",
            json_str(s)
        ));
        other.push_str(&format!(
            "{{ \"str\" : {{\"str\":{},\"pre\":0}}, \"in\":{id} }}\n",
            json_u(s)
        ));
    }
    let nn = names.len();
    let mut ce = Vec::new();
    let mut oe = Vec::new();
    ce.push("{\"ie\":0,\"sort\":0}".to_string());
    oe.push("{\"sort\":0,\"ie\":0}".to_string());
    let bis = ["default", "implicit", "instImplicit", "strictImplicit"];
    let mut e = 1usize;
    for round in 0..40usize {
        let n = round % nn + 1;
        let bi = bis[round % 4];
        // an application
        ce.push(format!(
            "{{\"app\":{{\"arg\":{},\"fn\":{}}},\"ie\":{e}}}",
            e - 1,
            e / 2
        ));
        oe.push(match round % 3 {
            0 => format!(
                "{{\"app\":{{\"fn\":{},\"arg\":{}}},\"ie\":{e}}}",
                e / 2,
                e - 1
            ),
            1 => format!(
                "{{\"app\": {{\"arg\":{:020},\"fn\":{}}},\"ie\":{e}}}",
                e - 1,
                e / 2
            ),
            _ => format!(
                "{{\"ie\":{e},\"app\":{{\"arg\":{},\"fn\":{:019}}}}}",
                e - 1,
                e / 2
            ),
        });
        e += 1;
        // a pi and a lambda
        ce.push(format!(
            "{{\"forallE\":{{\"binderInfo\":\"{bi}\",\"body\":{},\"name\":{n},\"type\":{}}},\"ie\":{e}}}",
            e - 1,
            e / 3
        ));
        oe.push(format!(
            "{{\"ie\":{e},\"forallE\":{{\"name\":{n},\"binderInfo\":\"{bi}\",\"type\":{},\"body\":{}}}}}",
            e / 3,
            e - 1
        ));
        e += 1;
        ce.push(format!(
            "{{\"ie\":{e},\"lam\":{{\"binderInfo\":\"{bi}\",\"body\":{},\"name\":{n},\"type\":{}}}}}",
            e - 1,
            e - 2
        ));
        oe.push(format!(
            "{{\"ie\":{:03},\"lam\":{{\"binderInfo\":\"{bi}\",\"body\":{},\"name\":{n},\"type\":{}}}}}",
            e,
            e - 1,
            e - 2
        ));
        e += 1;
    }
    for (c, o) in ce.iter().zip(&oe) {
        canon.push_str(c);
        canon.push('\n');
        other.push_str(o);
        other.push('\n');
    }
    let last = e - 1;
    for (i, _) in names.iter().enumerate() {
        let d = format!(
            "{{\"axiom\":{{\"isUnsafe\":false,\"levelParams\":[],\"name\":{},\"type\":{last}}}}}\n",
            i + 1
        );
        canon.push_str(&d);
        other.push_str(&d);
    }
    let (pa, pb) = (tmp("paths-canon.ndjson"), tmp("paths-other.ndjson"));
    std::fs::write(&pa, &canon).unwrap();
    std::fs::write(&pb, &other).unwrap();
    for t in [1, 4] {
        let (x, _) = pack_to_vec(&pa, &opts(true, t)).unwrap();
        let (y, _) = pack_to_vec(&pb, &opts(true, t)).unwrap();
        assert!(x == y, "{t} threads: the two writings pack differently");
    }
    let _ = std::fs::remove_file(&pa);
    let _ = std::fs::remove_file(&pb);
}
