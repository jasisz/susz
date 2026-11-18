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
        let st = bin().arg("unpack").arg(v.join(f)).arg("-").output().unwrap();
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
