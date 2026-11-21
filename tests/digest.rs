// The digest (spec 9.3): a Susz file and its export give the same digest,
// declaration by declaration; every change to a declaration changes it, and
// what the format does not keep (ids, line order, mdata, nondep) does not.
// The Susz side reads with the reader, the ndjson side with a parser of its
// own; the packer writes the Susz files compared.

use std::io::Read;
use std::path::PathBuf;
use susz::digest::{self, Hash};
use susz::pack::{pack_to_vec, Options};

// tests run in parallel: each file name once
fn tmp(name: &str) -> String {
    static N: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("digest-{}-{n}-{name}", std::process::id()))
        .to_string_lossy()
        .into_owned()
}

// (file digest, [(declaration digest, kind, name)])
type Each = (Hash, Vec<(Hash, u8, String)>);

fn each_nd(text: &[u8]) -> Each {
    let mut v = Vec::new();
    let s = digest::ndjson(text, true, &mut |e| {
        v.push((e.digest, e.kind, e.name.to_string()));
        Ok(())
    })
    .unwrap_or_else(|e| panic!("ndjson: {e}"));
    (s.digest, v)
}

fn each_susz(bytes: &[u8]) -> Each {
    let mut v = Vec::new();
    let s = digest::susz(bytes, true, &mut |e| {
        v.push((e.digest, e.kind, e.name.to_string()));
        Ok(())
    })
    .unwrap_or_else(|e| panic!("susz: {e}"));
    (s.digest, v)
}

fn pack(tag: &str, text: &str, index: bool) -> Vec<u8> {
    let p = tmp(&format!("{tag}.ndjson"));
    std::fs::write(&p, text).unwrap();
    let (b, _) = pack_to_vec(&p, &Options { index, threads: 1 })
        .unwrap_or_else(|e| panic!("{tag}: pack: {e}"));
    let _ = std::fs::remove_file(&p);
    b
}

// Both sides agree on an export, declaration by declaration, with and
// without INDEX; the file digest is SHA-256 over the declaration digests.
fn agree(tag: &str, text: &str) -> Each {
    let nd = each_nd(text.as_bytes());
    for index in [true, false] {
        let s = each_susz(&pack(tag, text, index));
        assert_eq!(s.1.len(), nd.1.len(), "{tag}: declaration count");
        for (i, (a, b)) in s.1.iter().zip(&nd.1).enumerate() {
            assert!(a == b, "{tag}: declaration {i} ({}) differs", b.2);
        }
        assert_eq!(s.0, nd.0, "{tag}");
    }
    use sha2::Digest;
    let mut h = sha2::Sha256::new();
    for d in &nd.1 {
        h.update(d.0);
    }
    assert_eq!(<[u8; 32]>::from(h.finalize()), nd.0, "{tag}: file digest");
    nd
}

const HEAD: &str = "{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}\n";

// A small export with one of each kind of record: names (string and
// number), levels (succ, max, imax, param), every expression kind, every
// declaration kind, a theorem whose proof goes to a block.
fn base() -> Vec<String> {
    let mut l: Vec<&str> = vec![
        r#"{"in":1,"str":{"pre":0,"str":"A"}}"#,
        r#"{"in":2,"str":{"pre":0,"str":"T"}}"#,
        r#"{"in":3,"num":{"pre":1,"i":7}}"#,
        r#"{"in":4,"str":{"pre":0,"str":"u"}}"#,
        r#"{"in":5,"str":{"pre":0,"str":"x"}}"#,
        r#"{"in":6,"str":{"pre":0,"str":"D"}}"#,
        r#"{"in":7,"str":{"pre":0,"str":"Q"}}"#,
        r#"{"in":8,"str":{"pre":0,"str":"O"}}"#,
        r#"{"in":9,"str":{"pre":0,"str":"I"}}"#,
        r#"{"in":10,"str":{"pre":9,"str":"mk"}}"#,
        r#"{"in":11,"str":{"pre":9,"str":"rec"}}"#,
        r#"{"in":12,"str":{"pre":0,"str":"T2"}}"#,
        r#"{"il":1,"succ":0}"#,
        r#"{"il":2,"param":4}"#,
        r#"{"il":3,"max":[1,2]}"#,
        r#"{"il":4,"imax":[2,1]}"#,
        r#"{"ie":0,"sort":0}"#,
        r#"{"ie":1,"sort":3}"#,
        r#"{"ie":2,"const":{"name":1,"us":[]}}"#,
        r#"{"ie":3,"bvar":0}"#,
        r#"{"ie":4,"forallE":{"binderInfo":"default","body":0,"name":5,"type":0}}"#,
        r#"{"ie":5,"lam":{"binderInfo":"implicit","body":3,"name":5,"type":2}}"#,
        r#"{"ie":6,"natVal":"5"}"#,
        r#"{"ie":7,"strVal":"s\né"}"#,
        r#"{"ie":8,"letE":{"body":3,"name":5,"nondep":false,"type":2,"value":6}}"#,
        r#"{"ie":9,"proj":{"idx":0,"struct":6,"typeName":1}}"#,
        r#"{"ie":10,"app":{"arg":7,"fn":5}}"#,
        r#"{"ie":11,"const":{"name":3,"us":[4,2]}}"#,
        r#"{"ie":12,"forallE":{"binderInfo":"default","body":1,"name":5,"type":11}}"#,
        r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":1,"type":0}}"#,
        r#"{"axiom":{"isUnsafe":false,"levelParams":[4],"name":3,"type":12}}"#,
        r#"{"ie":13,"app":{"arg":6,"fn":10}}"#,
        r#"{"ie":14,"const":{"name":1,"us":[]}}"#,
        r#"{"thm":{"all":[2],"levelParams":[],"name":2,"type":0,"value":13}}"#,
        r#"{"def":{"all":[6],"hints":{"regular":3},"levelParams":[],"name":6,"safety":"safe","type":4,"value":8}}"#,
        r#"{"opaque":{"all":[8],"isUnsafe":false,"levelParams":[],"name":8,"type":0,"value":9}}"#,
        r#"{"quot":{"kind":"type","levelParams":[],"name":7,"type":0}}"#,
        r#"{"ie":15,"const":{"name":9,"us":[]}}"#,
        r#"{"inductive":{"ctors":[{"cidx":0,"induct":9,"isUnsafe":false,"levelParams":[],"name":10,"numFields":0,"numParams":0,"type":15}],"recs":[{"all":[9],"isUnsafe":false,"k":true,"levelParams":[],"name":11,"numIndices":0,"numMinors":1,"numMotives":1,"numParams":0,"rules":[{"ctor":10,"nfields":0,"rhs":3}],"type":0}],"types":[{"all":[9],"ctors":[10],"isRec":false,"isReflexive":false,"isUnsafe":false,"levelParams":[],"name":9,"numIndices":0,"numNested":0,"numParams":0,"type":0}]}}"#,
        r#"{"thm":{"all":[12],"levelParams":[],"name":12,"type":0,"value":14}}"#,
    ];
    l.insert(0, HEAD.trim_end());
    l.into_iter().map(String::from).collect()
}

fn text(lines: &[String]) -> String {
    lines.join("\n") + "\n"
}

fn find(lines: &[String], pre: &str) -> usize {
    lines
        .iter()
        .position(|l| l.starts_with(pre))
        .unwrap_or_else(|| panic!("no line {pre}"))
}

#[test]
fn both_sides_agree_on_the_base() {
    let (_, ds) = agree("base", &text(&base()));
    let kinds: Vec<&str> = ds.iter().map(|d| digest::KINDS[d.1 as usize]).collect();
    assert_eq!(
        kinds,
        [
            "axiom",
            "axiom",
            "thm",
            "def",
            "opaque",
            "quot",
            "inductive",
            "thm"
        ]
    );
    let names: Vec<&str> = ds.iter().map(|d| d.2.as_str()).collect();
    assert_eq!(names, ["A", "A.7", "T", "D", "O", "Q", "I", "T2"]);
}

// Each change to what a declaration says changes the file digest and that
// declaration's digest (only that one's), on both sides alike.
#[test]
fn changes_change_the_digest() {
    let b = base();
    let (d0, e0) = agree("base", &text(&b));
    let edit = |pre: &str, from: &str, to: &str| -> Vec<String> {
        let mut l = b.clone();
        let i = find(&l, pre);
        assert!(l[i].contains(from), "{pre}: {from}");
        l[i] = l[i].replacen(from, to, 1);
        l
    };
    let cases: Vec<(&str, Vec<String>, &str)> = vec![
        ("natVal", edit(r#"{"ie":6,"#, "\"5\"", "\"6\""), "T"),
        (
            "binderInfo",
            edit(r#"{"ie":5,"#, "\"implicit\"", "\"strictImplicit\""),
            "T",
        ),
        (
            "binderInfo-pi",
            edit(r#"{"ie":4,"#, "\"default\"", "\"instImplicit\""),
            "D",
        ),
        ("bvar", edit(r#"{"ie":3,"#, "\"bvar\":0", "\"bvar\":1"), "T"),
        ("name-str", edit(r#"{"in":5,"#, "\"x\"", "\"y\""), "T"),
        ("name-num", edit(r#"{"in":3,"#, "\"i\":7", "\"i\":8"), "A.7"),
        ("level-succ", edit(r#"{"il":3,"#, "[1,2]", "[2,1]"), "A.7"),
        ("level-imax", edit(r#"{"il":4,"#, "imax", "max"), "A.7"),
        ("str", edit(r#"{"ie":7,"#, "s\\n", "s\\r"), "T"),
        (
            "proj-idx",
            edit(r#"{"ie":9,"#, "\"idx\":0", "\"idx\":1"),
            "O",
        ),
        (
            "hints",
            edit(r#"{"def":"#, "{\"regular\":3}", "{\"regular\":4}"),
            "D",
        ),
        (
            "hints-abbrev",
            edit(r#"{"def":"#, "{\"regular\":3}", "\"abbrev\""),
            "D",
        ),
        ("safety", edit(r#"{"def":"#, "\"safe\"", "\"partial\""), "D"),
        (
            "unsafe",
            edit(r#"{"opaque":"#, "\"isUnsafe\":false", "\"isUnsafe\":true"),
            "O",
        ),
        ("quot", edit(r#"{"quot":"#, "\"type\"", "\"ind\""), "Q"),
        (
            "rec-k",
            edit(r#"{"inductive":"#, "\"k\":true", "\"k\":false"),
            "I",
        ),
        (
            "rule-nfields",
            edit(r#"{"inductive":"#, "\"nfields\":0", "\"nfields\":1"),
            "I",
        ),
        (
            "levelParams",
            edit(
                r#"{"axiom":{"isUnsafe":false,"levelParams":[4]"#,
                "[4]",
                "[4,4]",
            ),
            "A.7",
        ),
        (
            "const-levels",
            edit(r#"{"ie":11,"#, "[4,2]", "[2,4]"),
            "A.7",
        ),
    ];
    for (tag, l, who) in cases {
        let (d, e) = agree(tag, &text(&l));
        assert_ne!(d, d0, "{tag}: the file digest did not change");
        // by the names before the change
        let changed: Vec<&str> = e
            .iter()
            .zip(&e0)
            .filter(|(a, b)| a.0 != b.0)
            .map(|(_, b)| b.2.as_str())
            .collect();
        assert!(
            changed.contains(&who),
            "{tag}: {who} did not change ({changed:?})"
        );
    }
    // the binder name x is in A.7, T and D: it changes those alone
    let (_, e) = agree("name-x", &text(&edit(r#"{"in":5,"#, "\"x\"", "\"z\"")));
    let changed: Vec<&str> = e
        .iter()
        .zip(&e0)
        .filter(|(a, b)| a.0 != b.0)
        .map(|(a, _)| a.2.as_str())
        .collect();
    assert_eq!(changed, ["A.7", "T", "D"]);
}

// Swapping two declarations changes the file digest, not theirs.
#[test]
fn declaration_order_counts() {
    let b = base();
    let (d0, e0) = agree("base", &text(&b));
    let mut l = b.clone();
    let (i, j) = (find(&l, r#"{"opaque":"#), find(&l, r#"{"quot":"#));
    l.swap(i, j);
    let (d, e) = agree("swapped", &text(&l));
    assert_ne!(d, d0);
    let mut x: Vec<Hash> = e.iter().map(|d| d.0).collect();
    let mut y: Vec<Hash> = e0.iter().map(|d| d.0).collect();
    assert_ne!(x, y);
    x.sort();
    y.sort();
    assert_eq!(x, y);
}

// Ids, the order of independent lines, mdata and nondep do not count.
#[test]
fn what_is_not_kept_does_not_count() {
    let b = base();
    let (d0, _) = agree("base", &text(&b));
    // every id shifted: names +100, levels +50, expressions +1000
    let shift = |l: &str| -> String {
        let mut out = String::new();
        let mut rest = l;
        // keys whose values (or arrays of values) are ids, by space
        let keys: &[(&str, u64)] = &[
            ("\"in\":", 100),
            ("\"pre\":", 100),
            ("\"name\":", 100),
            ("\"param\":", 100),
            ("\"typeName\":", 100),
            ("\"induct\":", 100),
            ("\"ctor\":", 100),
            ("\"all\":", 100),
            ("\"ctors\":", 100),
            ("\"levelParams\":", 100),
            ("\"il\":", 50),
            ("\"succ\":", 50),
            ("\"max\":", 50),
            ("\"imax\":", 50),
            ("\"sort\":", 50),
            ("\"us\":", 50),
            ("\"ie\":", 1000),
            ("\"fn\":", 1000),
            ("\"arg\":", 1000),
            ("\"body\":", 1000),
            ("\"type\":", 1000),
            ("\"value\":", 1000),
            ("\"struct\":", 1000),
            ("\"rhs\":", 1000),
            ("\"expr\":", 1000),
        ];
        'outer: while !rest.is_empty() {
            for (k, d) in keys {
                if let Some(r) = rest.strip_prefix(k) {
                    out.push_str(k);
                    let arr = r.starts_with('[');
                    let mut r = if arr { &r[1..] } else { r };
                    if arr {
                        out.push('[');
                    }
                    loop {
                        let n = r.bytes().take_while(u8::is_ascii_digit).count();
                        if n == 0 {
                            break;
                        }
                        let v: u64 = r[..n].parse().unwrap();
                        // 0 is the anonymous name and level zero
                        let zero_fixed = (*d == 100 || *d == 50) && v == 0;
                        out.push_str(&(if zero_fixed { 0 } else { v + d }).to_string());
                        r = &r[n..];
                        if arr && r.starts_with(',') {
                            out.push(',');
                            r = &r[1..];
                        } else {
                            break;
                        }
                    }
                    rest = r;
                    continue 'outer;
                }
            }
            let c = rest.chars().next().unwrap();
            out.push(c);
            rest = &rest[c.len_utf8()..];
        }
        out
    };
    let mut l: Vec<String> = b.iter().map(|x| shift(x)).collect();
    l[0] = HEAD.trim_end().to_string();
    let t = text(&l);
    assert_ne!(t, text(&b));
    assert_eq!(agree("shifted", &t).0, d0, "renumbered ids");
    // two independent expression lines swapped
    let mut l = b.clone();
    let (i, j) = (find(&l, r#"{"ie":6,"#), find(&l, r#"{"ie":7,"#));
    l.swap(i, j);
    assert_eq!(agree("lines", &text(&l)).0, d0, "independent lines swapped");
    // an mdata wrapper around the theorem's value, and around a binder type
    let mut l = b.clone();
    let i = find(&l, r#"{"thm":{"all":[2]"#);
    l.insert(
        i,
        r#"{"ie":100,"mdata":{"data":{"k":{"v":[1,"x",true,null]}},"expr":13}}"#.into(),
    );
    l[i + 1] = l[i + 1].replace("\"value\":13", "\"value\":100");
    let k = find(&l, r#"{"ie":5,"#);
    l.insert(k, r#"{"ie":101,"mdata":{"data":{},"expr":2}}"#.into());
    l[k + 1] = l[k + 1].replace("\"type\":2", "\"type\":101");
    assert_eq!(agree("mdata", &text(&l)).0, d0, "mdata");
    // letE's nondep
    let mut l = b.clone();
    let i = find(&l, r#"{"ie":8,"#);
    l[i] = l[i].replace("\"nondep\":false", "\"nondep\":true");
    assert_eq!(agree("nondep", &text(&l)).0, d0, "nondep");
    // spacing, key order, escapes, leading zeros
    let mut l = b.clone();
    let i = find(&l, r#"{"in":5,"#);
    l[i] = r#"{ "str" : { "str" : "x", "pre" : 000 }, "in" : 5 }"#.into();
    assert_eq!(agree("written", &text(&l)).0, d0, "another writing");
}

// Nat literals: the ndjson side hashes the decimal text, the Susz side
// converts its bytes back to decimal; they agree on 0, on leading zeros, on
// limb edges, and on a literal of a million digits.
#[test]
fn nat_literals_agree() {
    let mut lits: Vec<String> = ["0", "000", "1", "255", "256", "65535", "4294967296"]
        .iter()
        .map(|s| s.to_string())
        .collect();
    lits.push("18446744073709551615".into());
    lits.push("18446744073709551616".into());
    lits.push("00340282366920938463463374607431768211456".into());
    // a million digits, not a power of anything
    let mut big = String::with_capacity(1_000_000);
    let mut x: u64 = 0x9E37_79B9_7F4A_7C15;
    big.push('7');
    for _ in 1..1_000_000 {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        big.push((b'0' + (x % 10) as u8) as char);
    }
    lits.push(big.clone());
    lits.push(format!("000{big}"));
    let mut seen = std::collections::HashSet::new();
    for (k, lit) in lits.iter().enumerate() {
        let t = format!(
            "{HEAD}{{\"in\":1,\"str\":{{\"pre\":0,\"str\":\"A\"}}}}\n\
             {{\"ie\":0,\"natVal\":\"{lit}\"}}\n\
             {{\"axiom\":{{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}}}\n"
        );
        let d = agree(&format!("nat-{k}"), &t).0;
        seen.insert((lit.trim_start_matches('0').to_string(), d));
    }
    // equal values give equal digests, others other ones
    let values: std::collections::HashSet<&String> = seen.iter().map(|x| &x.0).collect();
    let digests: std::collections::HashSet<&Hash> = seen.iter().map(|x| &x.1).collect();
    assert_eq!(seen.len(), values.len());
    assert_eq!(digests.len(), values.len());
}

// Every accept vector: the Susz file read directly, and its unpacked
// ndjson read by the ndjson reader, give the same declaration digests.
#[test]
fn vectors_agree_with_their_unpacked_exports() {
    let mut n = 0;
    for v in susz::vectors::all() {
        if !matches!(
            v.want,
            susz::vectors::Want::Accept | susz::vectors::Want::BadIndex(_)
        ) {
            continue;
        }
        let a = susz::vectors::build(&v);
        let mut out = Vec::new();
        susz::unpack::unpack(&a.bytes, &mut out).unwrap();
        let mut t = String::from_utf8(out).unwrap();
        // the vectors' meta has no format version: the header line of a
        // 3.1 export instead
        let nl = t.find('\n').unwrap();
        t.replace_range(..=nl, HEAD);
        let s = each_susz(&a.bytes);
        let nd = each_nd(t.as_bytes());
        assert!(s == nd, "{}: the digests differ", v.name);
        assert_eq!(
            digest::of_susz(&a.bytes).unwrap(),
            nd.0,
            "{}: of_susz",
            v.name
        );
        n += 1;
    }
    assert!(n >= 10, "{n} vectors");
}

fn init_prelude() -> Option<String> {
    let gz = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/corpus/init-prelude.ndjson.gz");
    let f = std::fs::File::open(gz).ok()?;
    let mut text = String::new();
    flate2::read::GzDecoder::new(f)
        .read_to_string(&mut text)
        .unwrap();
    Some(text)
}

// init-prelude: packed with and without INDEX, unpacked again; every
// declaration's digest agrees on all of them.
#[test]
fn init_prelude_agrees() {
    let Some(t) = init_prelude() else {
        assert!(
            std::env::var("SUSZ_REQUIRE_CORPORA").map_or(true, |v| v != "1"),
            "init-prelude is missing"
        );
        return;
    };
    let nd = agree("init-prelude", &t);
    assert!(nd.1.len() > 1000);
    let b = pack("init-prelude-u", &t, true);
    let mut out = Vec::new();
    susz::unpack::unpack(&b, &mut out).unwrap();
    assert!(each_nd(&out) == nd, "the unpacked export differs");
    assert!(nd.1.iter().all(|d| !d.2.is_empty()));
}

// Broken inputs are errors, never a digest.
#[test]
fn broken_inputs_are_errors() {
    let t = text(&base());
    let mut b = pack("broken", &t, true);
    // a byte of the last declaration record changed: malformed or other
    // declarations, never a panic
    assert!(digest::of_susz(&b[..b.len() - 1]).is_err());
    let n = b.len();
    b[n - 30] ^= 0xff;
    let _ = digest::of_susz(&b);
    for (from, to, want) in [
        ("\"sort\":0}", "\"sort\":0,\"x\":1}", "cannot digest"),
        ("\"bvar\":0", "\"bvar\":-1", "not a valid export"),
        (
            "\"natVal\":\"5\"",
            "\"natVal\":\"5x\"",
            "not a valid export",
        ),
        ("\"natVal\":\"5\"", "\"natVal\":5", "not a valid export"),
        ("{\"thm\":", "{\"theorem\":", "cannot digest"),
        ("\"value\":13", "\"value\":99", "not a valid export"),
        (
            "\"isUnsafe\":false,\"levelParams\":[],\"name\":1",
            "\"isUnsafe\":0,\"levelParams\":[],\"name\":1",
            "not a valid export",
        ),
    ] {
        assert!(t.contains(from), "{from}");
        let e = digest::ndjson(t.replacen(from, to, 1).as_bytes(), false, &mut |_| Ok(()))
            .map(|_| ())
            .unwrap_err()
            .to_string();
        assert!(e.starts_with(want), "{from} -> {to}: {e}");
    }
}
