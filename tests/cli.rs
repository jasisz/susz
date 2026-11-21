// The command's exit codes, and that it never leaves a partial output.

use std::path::{Path, PathBuf};
use std::process::Command;

fn bin() -> Command {
    Command::new(env!("CARGO_BIN_EXE_susz"))
}

fn tmp(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!("cli-{name}"))
}

fn no_leftovers(out: &Path) {
    assert!(!out.exists(), "{} was written", out.display());
    let dir = out.parent().unwrap();
    let stem = out.file_name().unwrap().to_string_lossy().to_string();
    for e in std::fs::read_dir(dir).unwrap() {
        let n = e.unwrap().file_name().to_string_lossy().to_string();
        assert!(
            !n.starts_with(&format!("{stem}.tmp-")),
            "temporary {n} left"
        );
    }
}

const GOOD: &str = "{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}\n\
{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A\"}}\n\
{\"ie\":0,\"sort\":0}\n\
{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}\n";

fn pack(name: &str, input: &str) -> (i32, PathBuf) {
    let inp = tmp(&format!("{name}.ndjson"));
    std::fs::write(&inp, input).unwrap();
    let out = tmp(&format!("{name}.susz"));
    let _ = std::fs::remove_file(&out);
    let st = bin().arg("pack").arg(&inp).arg(&out).output().unwrap();
    (st.status.code().unwrap_or(-1), out)
}

#[test]
fn pack_exit_codes() {
    let (c, out) = pack("good", GOOD);
    assert_eq!(c, 0);
    assert!(out.exists());
    let st = bin().arg("verify").arg(&out).output().unwrap();
    assert_eq!(st.status.code(), Some(0));

    let (c, out) = pack("malformed", &GOOD.replace("\"sort\":0}", "\"sort\":"));
    assert_eq!(c, 1);
    no_leftovers(&out);
    let (c, out) = pack("dangling", &GOOD.replace("\"type\":0", "\"type\":7"));
    assert_eq!(c, 1);
    no_leftovers(&out);
    let (c, out) = pack("unknown-kind", &GOOD.replace("\"sort\"", "\"sorts\""));
    assert_eq!(c, 2);
    no_leftovers(&out);
    let (c, out) = pack(
        "unknown-field",
        &GOOD.replace("\"isUnsafe\":false,", "\"isUnsafe\":false,\"x\":1,"),
    );
    assert_eq!(c, 2);
    no_leftovers(&out);
    let (c, out) = pack(
        "big-num",
        &GOOD.replace(
            "{\"ie\":0,\"sort\":0}",
            "{\"ie\":0,\"sort\":0}\n{\"bvar\":18446744073709551616,\"ie\":1}",
        ),
    );
    assert_eq!(c, 2);
    no_leftovers(&out);

    let out = tmp("missing.susz");
    let st = bin()
        .arg("pack")
        .arg(tmp("does-not-exist.ndjson"))
        .arg(&out)
        .output()
        .unwrap();
    assert_eq!(st.status.code(), Some(2));
    no_leftovers(&out);
    let st = bin().arg("pack").output().unwrap();
    assert_eq!(st.status.code(), Some(2));
}

#[test]
fn panic_exits_2_and_removes_output() {
    let out = tmp("panic.susz.tmp-x");
    let st = bin().arg("__panic-test").arg(&out).output().unwrap();
    assert_eq!(
        st.status.code(),
        Some(2),
        "{}",
        String::from_utf8_lossy(&st.stderr)
    );
    assert!(!out.exists());
}

#[test]
fn verify_exit_codes() {
    let v = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/vectors");
    for (f, code) in [
        ("accept/blocks.susz", 0),
        ("reject/rule-p-later.susz", 1),
        ("decline/major-2.susz", 2),
    ] {
        let st = bin().arg("verify").arg(v.join(f)).output().unwrap();
        assert_eq!(
            st.status.code(),
            Some(code),
            "{f}: {}",
            String::from_utf8_lossy(&st.stdout)
        );
    }
}

// An export whose theorem names a constant declared after it: a declaration
// failure, not a malformed file. The packer writes it, verify reports the
// declaration failure, and unpack gives the export back.
#[test]
fn rule_p_is_a_declaration_failure() {
    let input = "{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}\n\
{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A\"}}\n\
{\"in\":2,\"str\":{\"pre\":0,\"str\":\"T\"}}\n\
{\"ie\":0,\"sort\":0}\n\
{\"const\":{\"name\":1,\"us\":[]},\"ie\":1}\n\
{\"thm\":{\"all\":[2],\"levelParams\":[],\"name\":2,\"type\":0,\"value\":1}}\n\
{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}\n";
    let (c, out) = pack("rule-p", input);
    assert_eq!(c, 0);
    let st = bin().arg("verify").arg(&out).output().unwrap();
    let text = String::from_utf8_lossy(&st.stdout);
    assert_eq!(st.status.code(), Some(1), "{text}");
    assert!(
        text.starts_with("rejected: declaration failure: ") && text.contains("(rule-p)"),
        "{text}"
    );
    let nd = tmp("rule-p.unpacked.ndjson");
    let st = bin().arg("unpack").arg(&out).arg(&nd).output().unwrap();
    assert_eq!(
        st.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&st.stderr)
    );
    assert_eq!(
        susz::digest::of_ndjson(nd.to_str().unwrap()).unwrap(),
        susz::digest::of_ndjson(tmp("rule-p.ndjson").to_str().unwrap()).unwrap()
    );
}

// `unpack FILE -` writes to stdout the same bytes `unpack FILE OUT` writes to
// OUT.
#[test]
fn unpack_to_stdout() {
    let (c, out) = pack("stdout", GOOD);
    assert_eq!(c, 0);
    let nd = tmp("stdout.unpacked.ndjson");
    let st = bin().arg("unpack").arg(&out).arg(&nd).output().unwrap();
    assert_eq!(st.status.code(), Some(0));
    let st = bin().arg("unpack").arg(&out).arg("-").output().unwrap();
    assert_eq!(st.status.code(), Some(0));
    assert!(!st.stdout.is_empty());
    assert_eq!(st.stdout, std::fs::read(&nd).unwrap());
    assert!(!Path::new("-").exists());

    let v = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/vectors");
    for (f, code) in [
        ("reject/back-distance-past-start.susz", 1),
        ("decline/major-2.susz", 2),
    ] {
        let st = bin()
            .arg("unpack")
            .arg(v.join(f))
            .arg("-")
            .output()
            .unwrap();
        assert_eq!(st.status.code(), Some(code), "{f}");
    }
}

// A declaration of the anonymous name cannot be written: exit 1.
#[test]
fn anonymous_declaration_is_refused() {
    let (c, out) = pack("anonymous", &GOOD.replace("\"name\":1,", "\"name\":0,"));
    assert_eq!(c, 1);
    no_leftovers(&out);
}

// A mapped input truncated under the command: SIGBUS becomes exit 2, and
// the partial output is removed.
#[cfg(all(feature = "mmap", any(target_os = "linux", target_os = "macos")))]
#[test]
fn truncated_mapped_input_exits_2_and_removes_output() {
    let input = tmp("sigbus.susz");
    std::fs::write(&input, vec![7u8; 1 << 20]).unwrap();
    let out = tmp("sigbus.ndjson.tmp-x");
    let st = bin()
        .arg("__sigbus-test")
        .arg(&input)
        .arg(&out)
        .output()
        .unwrap();
    let err = String::from_utf8_lossy(&st.stderr);
    assert_eq!(st.status.code(), Some(2), "{err}");
    assert!(err.contains("truncated or could not be read"), "{err}");
    assert!(!out.exists());
}

// Axioms A, B and U, a theorem T : A := B, and C : A a definition whose
// type is A, so its value is never looked at: T uses A and B, nothing uses U.
const AXIOMS: &str = "{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}\n\
{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A\"}}\n\
{\"in\":2,\"str\":{\"pre\":0,\"str\":\"B\"}}\n\
{\"in\":3,\"str\":{\"pre\":0,\"str\":\"T\"}}\n\
{\"in\":4,\"str\":{\"pre\":0,\"str\":\"U\"}}\n\
{\"in\":5,\"str\":{\"pre\":4,\"str\":\"x\"}}\n\
{\"ie\":0,\"sort\":0}\n\
{\"const\":{\"name\":1,\"us\":[]},\"ie\":1}\n\
{\"const\":{\"name\":2,\"us\":[]},\"ie\":2}\n\
{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}\n\
{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":2,\"type\":1}}\n\
{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":5,\"type\":0}}\n\
{\"thm\":{\"all\":[3],\"levelParams\":[],\"name\":3,\"type\":1,\"value\":2}}\n\
{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":4,\"type\":0}}\n";

fn axioms(file: &Path, args: &[&str]) -> (i32, String, String) {
    let st = bin().arg("axioms").arg(file).args(args).output().unwrap();
    (
        st.status.code().unwrap_or(-1),
        String::from_utf8(st.stdout).unwrap(),
        String::from_utf8_lossy(&st.stderr).into_owned(),
    )
}

#[test]
fn axioms_used_and_unused() {
    let (c, f) = pack("axioms", AXIOMS);
    assert_eq!(c, 0);
    // a theorem: the axioms of its type and its proof, sorted
    let (c, out, err) = axioms(&f, &["--root", "T"]);
    assert_eq!(c, 0, "{err}");
    assert_eq!(out, "A\nB\n");
    // an axiom as a root is its own dependency
    let (c, out, _) = axioms(&f, &["--root", "U", "--quiet"]);
    assert_eq!(c, 0);
    assert_eq!(out, "U\n");
    // an axiom of an axiom's type
    let (c, out, _) = axioms(&f, &["--root", "B", "--threads", "2"]);
    assert_eq!(c, 0);
    assert_eq!(out, "A\nB\n");
    // no root: every axiom of the file
    let (c, out, _) = axioms(&f, &[]);
    assert_eq!(c, 0);
    assert_eq!(out, "A\nB\nU\nU.x\n");
    // by prefix, and from a roots file
    let (c, out, _) = axioms(&f, &["--prefix", "U."]);
    assert_eq!(c, 0);
    assert_eq!(out, "U.x\n");
    let roots = tmp("axioms.roots");
    std::fs::write(&roots, "T\n\nU.x\n").unwrap();
    let (c, out, _) = axioms(&f, &["--roots-file", roots.to_str().unwrap()]);
    assert_eq!(c, 0);
    assert_eq!(out, "A\nB\nU.x\n");
    // nothing written next to the input
    let dir = f.parent().unwrap();
    for e in std::fs::read_dir(dir).unwrap() {
        let n = e.unwrap().file_name().to_string_lossy().to_string();
        assert!(!n.starts_with("cli-axioms.susz."), "{n} written");
    }
}

#[test]
fn axioms_all() {
    let (c, f) = pack("axioms-all", AXIOMS);
    assert_eq!(c, 0);
    let (c, out, err) = axioms(&f, &["--root", "T", "--all"]);
    assert_eq!(c, 0, "{err}");
    assert_eq!(out, "used A\nused B\nunused U\nunused U.x\n");
    let (c, out, _) = axioms(&f, &["--all"]);
    assert_eq!(c, 0);
    assert_eq!(out, "used A\nused B\nused U\nused U.x\n");
    // a theorem without axioms: nothing used, still listed
    let (c, f) = pack("axioms-none", GOOD);
    assert_eq!(c, 0);
    let (c, out, _) = axioms(&f, &["--all"]);
    assert_eq!(c, 0);
    assert_eq!(out, "used A\n");
}

#[test]
fn axioms_exit_codes() {
    let (c, f) = pack("axioms-codes", AXIOMS);
    assert_eq!(c, 0);
    // a missing root: exit 1, nothing on stdout
    let (c, out, err) = axioms(&f, &["--root", "T", "--root", "No.Such"]);
    assert_eq!(c, 1);
    assert_eq!(out, "");
    assert!(err.contains("no declaration named No.Such"), "{err}");
    let (c, out, _) = axioms(&f, &["--prefix", "No.Such"]);
    assert_eq!(c, 1);
    assert_eq!(out, "");
    let v = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/vectors");
    for (file, code) in [
        ("accept/blocks.susz", 0),
        ("reject/back-distance-past-start.susz", 1),
        ("decline/major-2.susz", 2),
    ] {
        let (c, _, err) = axioms(&v.join(file), &[]);
        assert_eq!(c, code, "{file}: {err}");
    }
    let (c, _, _) = axioms(&tmp("does-not-exist.susz"), &[]);
    assert_eq!(c, 2);
    // no file, two files, an unknown option
    for args in [&[][..], &["x.susz", "y.susz"], &["x.susz", "--nope"]] {
        let st = bin().arg("axioms").args(args).output().unwrap();
        assert_eq!(st.status.code(), Some(2), "{args:?}");
    }
}

// `digest`: the same output for an export and its Susz file, on a path or
// on stdin; comparing gives 0 same, 1 different (naming the declaration),
// 2 for a file it cannot read.
#[test]
fn digest_exit_codes() {
    use std::io::Write;
    let two = GOOD.to_string()
        + "{\"in\":2,\"str\":{\"pre\":0,\"str\":\"B\"}}\n\
{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":2,\"type\":0}}\n";
    let (c, out) = pack("digest", &two);
    assert_eq!(c, 0);
    let nd = tmp("digest.ndjson");
    let run = |args: &[&std::ffi::OsStr], stdin: Option<&[u8]>| {
        let mut cmd = bin();
        cmd.arg("digest").args(args);
        cmd.stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped());
        let mut ch = cmd.spawn().unwrap();
        let mut i = ch.stdin.take().unwrap();
        if let Some(b) = stdin {
            i.write_all(b).unwrap();
        }
        drop(i);
        let o = ch.wait_with_output().unwrap();
        (
            o.status.code().unwrap_or(-1),
            String::from_utf8(o.stdout).unwrap(),
        )
    };
    let (c1, a) = run(&[out.as_os_str()], None);
    let (c2, b) = run(&[nd.as_os_str()], None);
    let (c3, s) = run(&["-".as_ref()], Some(two.as_bytes()));
    let (c4, z) = run(&["-".as_ref()], Some(&std::fs::read(&out).unwrap()));
    assert_eq!((c1, c2, c3, c4), (0, 0, 0, 0));
    assert_eq!(a, b);
    assert_eq!(a, s);
    assert_eq!(a, z);
    let lines: Vec<&str> = a.lines().collect();
    assert_eq!(lines.len(), 2, "{a}");
    assert_eq!(lines[0].len(), 64);
    assert_eq!(
        lines[1],
        "2 declarations: 2 axiom, 0 def, 0 thm, 0 opaque, 0 quot, 0 inductive"
    );
    // --each: one line a declaration, then the same two lines
    let (c, e) = run(&["--each".as_ref(), out.as_os_str()], None);
    assert_eq!(c, 0);
    let (_, e2) = run(&["--each".as_ref(), nd.as_os_str()], None);
    assert_eq!(e, e2);
    let el: Vec<&str> = e.lines().collect();
    assert_eq!(el.len(), 4);
    assert!(
        el[0].ends_with(" axiom A") && el[1].ends_with(" axiom B"),
        "{e}"
    );
    assert_eq!(el[0].len(), 64 + " axiom A".len());
    assert_eq!(&el[2..], &lines[..]);
    // the same
    let (c, t) = run(&[out.as_os_str(), nd.as_os_str()], None);
    assert_eq!(c, 0, "{t}");
    assert!(t.starts_with("same: "), "{t}");
    // B's type changed: B differs, A does not
    let other = tmp("digest-other.ndjson");
    std::fs::write(
        &other,
        two.replace("\"name\":2,\"type\":0", "\"name\":2,\"type\":1")
            .replace(
                "{\"ie\":0,\"sort\":0}\n",
                "{\"ie\":0,\"sort\":0}\n{\"ie\":1,\"bvar\":0}\n",
            ),
    )
    .unwrap();
    let (c, t) = run(&[out.as_os_str(), other.as_os_str()], None);
    assert_eq!(c, 1, "{t}");
    assert!(
        t.contains("1 declarations differ: 1 changed, 0 only in A, 0 only in B")
            && t.contains("  changed B (A #2, B #2)"),
        "{t}"
    );
    // the two declarations swapped: the same ones, in another order
    let swapped = tmp("digest-swapped.ndjson");
    let mut ls: Vec<&str> = two.lines().collect();
    let n = ls.len();
    let a1 = ls.iter().position(|l| l.starts_with("{\"axiom\"")).unwrap();
    // B's name record comes first
    ls.swap(a1, n - 1);
    let (i, j) = (a1, n - 2);
    ls.swap(i, j);
    std::fs::write(&swapped, ls.join("\n") + "\n").unwrap();
    let (c, t) = run(&[out.as_os_str(), swapped.as_os_str()], None);
    assert_eq!(c, 1, "{t}");
    assert!(
        t.contains("the same declarations in another order: the first difference is declaration #1: A A, B B"),
        "{t}"
    );
    // unreadable, malformed, unknown kind: 2
    let missing = tmp("digest-missing.ndjson");
    let _ = std::fs::remove_file(&missing);
    assert_eq!(run(&[missing.as_os_str()], None).0, 2);
    let bad = tmp("digest-bad.ndjson");
    std::fs::write(&bad, GOOD.replace("\"sort\"", "\"sorts\"")).unwrap();
    assert_eq!(run(&[bad.as_os_str()], None).0, 2);
    assert_eq!(run(&[out.as_os_str(), bad.as_os_str()], None).0, 2);
    let mut b = std::fs::read(&out).unwrap();
    let k = b.len() - 3;
    b[k] ^= 0x55;
    let broken = tmp("digest-broken.susz");
    std::fs::write(&broken, &b).unwrap();
    assert_eq!(run(&[broken.as_os_str()], None).0, 2);
    // usage
    assert_eq!(run(&[], None).0, 2);
    assert_eq!(
        run(&["--each".as_ref(), out.as_os_str(), nd.as_os_str()], None).0,
        2
    );
    assert_eq!(run(&["-".as_ref(), "-".as_ref()], None).0, 2);
}

// `digest --kernel`: the kernel digest, marked `(kernel)`; two exports that
// differ only in a binder's name and binder info are the same to it, and
// not to the exact digest.
#[test]
fn digest_kernel() {
    let one = |name: &str, bi: &str| {
        format!(
            "{{\"meta\":{{\"format\":{{\"version\":\"3.1.0\"}}}}}}\n\
{{\"in\":1,\"str\":{{\"pre\":0,\"str\":\"A\"}}}}\n\
{{\"in\":2,\"str\":{{\"pre\":0,\"str\":\"{name}\"}}}}\n\
{{\"ie\":0,\"sort\":0}}\n\
{{\"ie\":1,\"forallE\":{{\"binderInfo\":\"{bi}\",\"body\":0,\"name\":2,\"type\":0}}}}\n\
{{\"axiom\":{{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":1}}}}\n"
        )
    };
    let (c, a) = pack("digest-k-a", &one("x", "default"));
    assert_eq!(c, 0);
    let b = tmp("digest-k-b.ndjson");
    std::fs::write(&b, one("y", "implicit")).unwrap();
    let run = |args: &[&std::ffi::OsStr]| {
        let o = bin().arg("digest").args(args).output().unwrap();
        (
            o.status.code().unwrap_or(-1),
            String::from_utf8(o.stdout).unwrap(),
        )
    };
    let k: &std::ffi::OsStr = "--kernel".as_ref();
    let e: &std::ffi::OsStr = "--each".as_ref();
    // one file: the digest line says (kernel); the flag goes anywhere
    let (c, x) = run(&[a.as_os_str()]);
    assert_eq!(c, 0);
    let (c, ka) = run(&[k, a.as_os_str()]);
    assert_eq!(c, 0);
    assert_eq!(run(&[a.as_os_str(), k]), (0, ka.clone()));
    let (xl, kl): (Vec<&str>, Vec<&str>) = (x.lines().collect(), ka.lines().collect());
    assert_eq!(kl.len(), 2, "{ka}");
    assert_eq!(xl[0].len(), 64);
    assert_eq!(kl[0].len(), 64 + " (kernel)".len());
    assert!(kl[0].ends_with(" (kernel)"), "{ka}");
    assert_ne!(&kl[0][..64], xl[0]);
    assert_eq!(kl[1], xl[1]);
    // the other export: another exact digest, the same kernel digest
    let (_, xb) = run(&[b.as_os_str()]);
    assert_ne!(xb, x);
    assert_eq!(run(&[b.as_os_str(), k]), (0, ka.clone()));
    // --each
    let (c, ea) = run(&[e, k, a.as_os_str()]);
    assert_eq!(c, 0);
    assert_eq!(run(&[k, e, b.as_os_str()]), (0, ea.clone()));
    let el: Vec<&str> = ea.lines().collect();
    assert_eq!(el.len(), 3);
    assert!(el[0].ends_with(" axiom A"), "{ea}");
    assert_eq!(&el[1..], &kl[..]);
    let (_, ex) = run(&[e, a.as_os_str()]);
    assert_ne!(ex.lines().next(), el.first().copied());
    // two files
    let (c, t) = run(&[a.as_os_str(), b.as_os_str()]);
    assert_eq!(c, 1, "{t}");
    assert!(t.starts_with("different: A "), "{t}");
    assert!(t.contains("  changed A (A #1, B #1)"), "{t}");
    let (c, t) = run(&[k, a.as_os_str(), b.as_os_str()]);
    assert_eq!(c, 0, "{t}");
    assert_eq!(
        t,
        format!("same (kernel): {}\n{}\n", &kl[0][..64], kl[1]),
        "{t}"
    );
    // a real difference: Type, not Prop
    let other = tmp("digest-k-other.ndjson");
    std::fs::write(
        &other,
        one("y", "implicit").replace(
            "{\"ie\":0,\"sort\":0}",
            "{\"il\":1,\"succ\":0}\n{\"ie\":0,\"sort\":1}",
        ),
    )
    .unwrap();
    let (c, t) = run(&[a.as_os_str(), other.as_os_str(), k]);
    assert_eq!(c, 1, "{t}");
    let tl: Vec<&str> = t.lines().collect();
    assert!(tl[0].starts_with("different (kernel): A "), "{t}");
    assert!(tl[1].starts_with("                    B "), "{t}");
    assert_eq!(tl[0].find(" A ").unwrap(), tl[1].find(" B ").unwrap());
    assert!(t.contains("  changed A (A #1, B #1)"), "{t}");
    // usage: --each with two files, an unknown option
    assert_eq!(run(&[k, e, a.as_os_str(), b.as_os_str()]).0, 2);
    assert_eq!(run(&["--kernels".as_ref(), a.as_os_str()]).0, 2);
}
