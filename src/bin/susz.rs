// The `susz` command: pack, verify, unpack, slice, axioms, digest.

use std::process::exit;
use susz::pack::{self, Fault, Options};
use susz::read::Outcome;

const USAGE: &str = "usage:
  susz pack IN.ndjson OUT.susz [--no-index] [--threads N]
  susz verify FILE.susz [--index]
  susz unpack FILE.susz OUT.ndjson|-
  susz slice IN.susz OUT.susz [--root NAME]... [--roots-file FILE] [--prefix NS]...
             [--no-index] [--threads N] [--quiet]
  susz axioms FILE.susz [--root NAME]... [--roots-file FILE] [--prefix NS]...
              [--all] [--threads N] [--quiet]
  susz digest FILE [--each]
  susz digest A B

pack uses all cores unless --threads N is given; the output is the same.
pack exits 0 when OUT is written, 1 when IN is not a valid export,
2 when it cannot be packed (a limit, an unknown record or field, I/O,
an internal error). verify exits 0 accepted, 1 rejected (the file is
malformed, or a declaration fails a rule a reader checks without types,
such as rule P), 2 declined or unreadable. unpack exits 0 written, 1 rejected, 2 declined or I/O.
unpack to - writes the ndjson to stdout as it goes; on an error it stops,
and what was already written stays written.

slice keeps the named declarations (--root, or one name per line of
--roots-file), every declaration whose name starts with a --prefix string,
and everything they depend on, in their order. It exits 0 written,
1 IN rejected or a root not found, 2 declined, I/O or an internal error.

axioms prints, one per line and sorted, the axiom declarations in the
closure slice would keep for the same roots; with no root or prefix, every
axiom FILE declares. With --all it prints every axiom FILE declares, each
after `used ` or `unused `. It writes no file; --threads is accepted as
slice takes it and changes nothing. It exits 0 listed, 1 FILE rejected,
a root not found or no declaration matched, 2 declined or unreadable.

digest prints the digest of the declarations FILE holds (spec 9.3), then a
line with their number by kind. FILE is a Susz file (told by its magic) or
an ndjson export; - reads either from stdin (zstd -d < x.zst | susz digest -).
The digest hashes names, levels and expressions by structure: a Susz file
and the export it was packed from give the same digest, and so do two
exports that differ only in ids, layout, mdata or letE's nondep. With
--each it first prints one line per declaration, in file order:
DIGEST KIND NAME. With two files it compares them, and names the first
declarations that differ. It exits 0 printed (or the same), 1 different,
2 when a file is malformed, not a valid export, declined, unreadable or I/O.";

extern "C" {
    fn _exit(code: i32) -> !;
}

fn main() {
    // A panic is an internal error: exit 2 (the release build aborts on
    // panic; the hook runs first), and never leave a partial output.
    std::panic::set_hook(Box::new(|info| {
        susz::cleanup::remove();
        eprintln!("susz: internal error: {info}");
        unsafe { _exit(2) }
    }));
    let args: Vec<String> = std::env::args().skip(1).collect();
    let Some(cmd) = args.first() else { usage() };
    match cmd.as_str() {
        "pack" => cmd_pack(&args[1..]),
        "verify" => cmd_verify(&args[1..]),
        "unpack" => cmd_unpack(&args[1..]),
        "slice" => cmd_slice(&args[1..]),
        "axioms" => cmd_axioms(&args[1..]),
        "digest" => cmd_digest(&args[1..]),
        "--version" | "-V" => println!(
            "susz {} (Susz {})",
            env!("CARGO_PKG_VERSION"),
            susz::format::MAJOR
        ),
        "--help" | "-h" | "help" => println!("{USAGE}"),
        // for the tests of the panic path: a temporary output, then a panic
        "__panic-test" if args.len() == 2 => {
            std::fs::write(&args[1], b"partial").unwrap();
            susz::cleanup::register(&args[1]);
            panic!("panic test");
        }
        // for the tests of the SIGBUS path: map a file, truncate it, touch
        // a lost page
        #[cfg(feature = "mmap")]
        "__sigbus-test" if args.len() == 3 => {
            std::fs::write(&args[2], b"partial").unwrap();
            sigbus::output(Some(&args[2]));
            let bytes = read_file(&args[1]);
            std::fs::File::options()
                .write(true)
                .open(&args[1])
                .unwrap()
                .set_len(0)
                .unwrap();
            let last = unsafe { std::ptr::read_volatile(&bytes[bytes.len() - 1]) };
            println!("still here: {last} (mapped: {})", bytes.is_mapped());
        }
        _ => usage(),
    }
}

fn usage() -> ! {
    eprintln!("{USAGE}");
    exit(2)
}

fn cmd_pack(args: &[String]) {
    // all cores unless --threads says otherwise
    let mut opts = Options {
        threads: pack::all_cores(),
        ..Options::default()
    };
    let mut files = Vec::new();
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--no-index" => opts.index = false,
            "--threads" => {
                i += 1;
                opts.threads = args
                    .get(i)
                    .and_then(|x| x.parse().ok())
                    .filter(|&n| n >= 1)
                    .unwrap_or_else(|| usage());
            }
            a if a.starts_with("--threads=") => {
                opts.threads = a["--threads=".len()..]
                    .parse()
                    .ok()
                    .filter(|&n| n >= 1)
                    .unwrap_or_else(|| usage());
            }
            a if a.starts_with('-') => usage(),
            a => files.push(a.to_string()),
        }
        i += 1;
    }
    if files.len() != 2 {
        usage();
    }
    match pack::pack_file(&files[0], &files[1], &opts) {
        Ok(st) => eprintln!("{st}"),
        Err(e) => {
            match e.fault {
                Fault::Invalid => eprintln!("susz: {}: not a valid export: {e}", files[0]),
                Fault::Cannot => eprintln!("susz: {}: cannot pack: {e}", files[0]),
            }
            exit(if e.fault == Fault::Invalid { 1 } else { 2 });
        }
    }
}

// The input file's bytes. With the `mmap` feature the file is mapped
// read-only. It is input the command does not own: if something truncates it
// while it is mapped, the next access to a lost page raises SIGBUS, and
// `sigbus` turns that into exit 2 with any partial output removed.
#[cfg(feature = "mmap")]
fn read_file(path: &str) -> susz::Mapped {
    sigbus::install(path);
    // SAFETY: a change to the file while it is mapped either shows up as
    // bytes the reader checks like any others, or raises SIGBUS (above).
    unsafe { susz::open_mmap(path) }.unwrap_or_else(|e| {
        eprintln!("susz: cannot read {path}: {e}");
        exit(2)
    })
}

#[cfg(not(feature = "mmap"))]
fn read_file(path: &str) -> Vec<u8> {
    std::fs::read(path).unwrap_or_else(|e| {
        eprintln!("susz: cannot read {path}: {e}");
        exit(2)
    })
}

// SIGBUS while a file is mapped: the file was truncated under us, or a page
// could not be read in. Report it, remove the partial output, exit 2. Only
// async-signal-safe calls in the handler: write, unlink, _exit.
#[cfg(all(feature = "mmap", any(target_os = "linux", target_os = "macos")))]
mod sigbus {
    use std::ffi::{c_char, c_void, CString};
    use std::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};

    #[cfg(target_os = "linux")]
    const SIGBUS: i32 = 7;
    #[cfg(target_os = "macos")]
    const SIGBUS: i32 = 10;

    extern "C" {
        fn signal(sig: i32, handler: extern "C" fn(i32)) -> usize;
        fn write(fd: i32, buf: *const c_void, n: usize) -> isize;
        fn unlink(path: *const c_char) -> i32;
        fn _exit(code: i32) -> !;
    }

    static MSG: AtomicPtr<u8> = AtomicPtr::new(std::ptr::null_mut());
    static MSG_LEN: AtomicUsize = AtomicUsize::new(0);
    static TMP: AtomicPtr<c_char> = AtomicPtr::new(std::ptr::null_mut());

    extern "C" fn on_sigbus(_: i32) {
        unsafe {
            let m = MSG.load(Ordering::SeqCst);
            if !m.is_null() {
                write(2, m as *const c_void, MSG_LEN.load(Ordering::SeqCst));
            }
            let t = TMP.load(Ordering::SeqCst);
            if !t.is_null() {
                unlink(t);
            }
            _exit(2)
        }
    }

    pub fn install(path: &str) {
        let msg: &'static [u8] = Box::leak(
            format!("susz: {path} was truncated or could not be read while mapped\n")
                .into_bytes()
                .into_boxed_slice(),
        );
        MSG_LEN.store(msg.len(), Ordering::SeqCst);
        MSG.store(msg.as_ptr() as *mut u8, Ordering::SeqCst);
        unsafe {
            signal(SIGBUS, on_sigbus);
        }
    }

    /// The partial output to remove on SIGBUS (`None`: nothing to remove).
    pub fn output(path: Option<&str>) {
        let p = path
            .and_then(|p| CString::new(p).ok())
            .map_or(std::ptr::null_mut(), CString::into_raw);
        // the previous path is leaked: the handler may be reading it
        TMP.store(p, Ordering::SeqCst);
    }
}

#[cfg(all(feature = "mmap", not(any(target_os = "linux", target_os = "macos"))))]
mod sigbus {
    pub fn install(_: &str) {}
    pub fn output(_: Option<&str>) {}
}

#[cfg(not(feature = "mmap"))]
mod sigbus {
    pub fn output(_: Option<&str>) {}
}

fn cmd_verify(args: &[String]) {
    let mut index = false;
    let mut files = Vec::new();
    for a in args {
        match a.as_str() {
            "--index" => index = true,
            a if a.starts_with('-') => usage(),
            a => files.push(a.to_string()),
        }
    }
    if files.len() != 1 {
        usage();
    }
    let bytes = read_file(&files[0]);
    match susz::verify(&bytes) {
        Outcome::Accepted(s) => {
            println!(
                "accepted: {} names, {} levels, {} MAIN expressions, {} declarations; {} proof blocks ({} expressions); frontier {} names, {} levels, {} expressions",
                s.counts[0] - 1,
                s.counts[1] - 1,
                s.counts[2],
                s.counts[3],
                s.blocks,
                s.block_exprs,
                s.frontier[0],
                s.frontier[1],
                s.frontier[2]
            );
            if index {
                let f = susz::read::File::open(&bytes).unwrap();
                match susz::index::verify_index(&f) {
                    Ok(()) => println!("INDEX: ok"),
                    Err(e) => println!("INDEX: {e}"),
                }
            }
        }
        Outcome::Rejected(e) if e.class.is_declaration_failure() => {
            // the export's own failure: a packer writes such a file
            println!("rejected: declaration failure: {e}");
            exit(1);
        }
        Outcome::Rejected(e) => {
            println!("rejected: malformed: {e}");
            exit(1);
        }
        Outcome::Declined(e) => {
            println!("declined: {e}");
            exit(2);
        }
    }
}

fn cmd_unpack(args: &[String]) {
    if args.len() != 2 {
        usage();
    }
    let bytes = read_file(&args[0]);
    let out = &args[1];
    if out == "-" {
        // to stdout, as it is produced: nothing to clean up on failure
        let res = (|| -> Result<(), susz::unpack::UnpackError> {
            let mut w = std::io::BufWriter::with_capacity(1 << 20, std::io::stdout().lock());
            susz::unpack::unpack(&bytes, &mut w)?;
            use std::io::Write;
            w.flush()?;
            Ok(())
        })();
        if let Err(e) = res {
            unpack_failed(e);
        }
        return;
    }
    let tmp = format!("{out}.tmp-{}", std::process::id());
    susz::cleanup::register(&tmp);
    sigbus::output(Some(&tmp));
    let res = (|| -> Result<(), susz::unpack::UnpackError> {
        let f = std::fs::File::create(&tmp)?;
        let mut w = std::io::BufWriter::with_capacity(1 << 20, f);
        susz::unpack::unpack(&bytes, &mut w)?;
        use std::io::Write;
        w.flush()?;
        drop(w);
        std::fs::rename(&tmp, out)?;
        Ok(())
    })();
    sigbus::output(None);
    susz::cleanup::unregister();
    if let Err(e) = res {
        let _ = std::fs::remove_file(&tmp);
        unpack_failed(e);
    }
}

fn unpack_failed(e: susz::unpack::UnpackError) -> ! {
    eprintln!("susz: {e}");
    let code = match &e {
        susz::unpack::UnpackError::File(f) if !f.class.declines() => 1,
        _ => 2,
    };
    exit(code)
}

fn cmd_slice(args: &[String]) {
    let mut opts = susz::slice::SliceOptions {
        index: true,
        threads: 1,
        progress: true,
        ..Default::default()
    };
    let mut files = Vec::new();
    let mut i = 0;
    let value = |i: &mut usize| -> String {
        *i += 1;
        args.get(*i).cloned().unwrap_or_else(|| usage())
    };
    while i < args.len() {
        match args[i].as_str() {
            "--root" => opts.roots.push(value(&mut i)),
            "--prefix" => opts.prefixes.push(value(&mut i)),
            "--roots-file" => {
                let p = value(&mut i);
                let text = std::fs::read_to_string(&p).unwrap_or_else(|e| {
                    eprintln!("susz: cannot read {p}: {e}");
                    exit(2)
                });
                opts.roots.extend(
                    text.lines()
                        .map(str::trim)
                        .filter(|l| !l.is_empty())
                        .map(String::from),
                );
            }
            "--no-index" => opts.index = false,
            "--quiet" => opts.progress = false,
            "--threads" => {
                opts.threads = value(&mut i)
                    .parse()
                    .ok()
                    .filter(|&n| n >= 1)
                    .unwrap_or_else(|| usage())
            }
            a if a.starts_with('-') => usage(),
            a => files.push(a.to_string()),
        }
        i += 1;
    }
    if files.len() != 2 {
        usage();
    }
    let bytes = read_file(&files[0]);
    let out = &files[1];
    let tmp = format!("{out}.tmp-{}", std::process::id());
    sigbus::output(Some(&tmp));
    let res = susz::slice::slice_file(&bytes, out, &opts);
    sigbus::output(None);
    match res {
        Ok(st) => eprintln!("{st}"),
        Err(e) => {
            use susz::slice::SliceError;
            let code = match &e {
                SliceError::File(f) if f.class.declines() => 2,
                SliceError::File(_) | SliceError::NotFound(_) | SliceError::Empty => 1,
                SliceError::Pack(_) => 2,
            };
            eprintln!("susz: {}: {e}", files[0]);
            exit(code);
        }
    }
}

fn cmd_axioms(args: &[String]) {
    let mut opts = susz::axioms::AxiomsOptions {
        progress: true,
        ..Default::default()
    };
    let mut all = false;
    let mut files = Vec::new();
    let mut i = 0;
    let value = |i: &mut usize| -> String {
        *i += 1;
        args.get(*i).cloned().unwrap_or_else(|| usage())
    };
    while i < args.len() {
        match args[i].as_str() {
            "--root" => opts.roots.push(value(&mut i)),
            "--prefix" => opts.prefixes.push(value(&mut i)),
            "--roots-file" => {
                let p = value(&mut i);
                let text = std::fs::read_to_string(&p).unwrap_or_else(|e| {
                    eprintln!("susz: cannot read {p}: {e}");
                    exit(2)
                });
                opts.roots.extend(
                    text.lines()
                        .map(str::trim)
                        .filter(|l| !l.is_empty())
                        .map(String::from),
                );
            }
            "--all" => all = true,
            "--quiet" => opts.progress = false,
            // as slice takes it; the closure runs on one thread
            "--threads" => {
                value(&mut i)
                    .parse::<usize>()
                    .ok()
                    .filter(|&n| n >= 1)
                    .unwrap_or_else(|| usage());
            }
            a if a.starts_with('-') => usage(),
            a => files.push(a.to_string()),
        }
        i += 1;
    }
    if files.len() != 1 {
        usage();
    }
    let bytes = read_file(&files[0]);
    match susz::axioms::axioms(&bytes, &opts) {
        Ok(ax) => {
            use std::io::Write;
            let mut w = std::io::BufWriter::new(std::io::stdout().lock());
            let res = if all {
                let mut xs: Vec<(&str, &str)> = ax
                    .used
                    .iter()
                    .map(|n| (n.as_str(), "used"))
                    .chain(ax.unused.iter().map(|n| (n.as_str(), "unused")))
                    .collect();
                xs.sort_unstable();
                xs.iter()
                    .try_for_each(|(n, m)| writeln!(w, "{m} {n}"))
                    .and_then(|()| w.flush())
            } else {
                ax.used
                    .iter()
                    .try_for_each(|n| writeln!(w, "{n}"))
                    .and_then(|()| w.flush())
            };
            if let Err(e) = res {
                eprintln!("susz: cannot write the list: {e}");
                exit(2);
            }
        }
        Err(e) => {
            use susz::axioms::AxiomsError;
            let code = match &e {
                AxiomsError::File(f) if f.class.declines() => 2,
                AxiomsError::File(_) | AxiomsError::NotFound(_) | AxiomsError::Empty => 1,
            };
            eprintln!("susz: {}: {e}", files[0]);
            exit(code);
        }
    }
}

// One declaration as `digest` keeps it to compare two files.
struct Got {
    sum: susz::digest::Summary,
    digests: Vec<susz::digest::Hash>,
    names: Vec<String>,
}

// The digest of FILE: Susz if it starts with the magic, ndjson otherwise; -
// is stdin. `each` sees every declaration; `names` asks for their names.
fn digest_of(
    path: &str,
    names: bool,
    each: &mut susz::digest::Each<'_>,
) -> Result<(susz::digest::Summary, bool), susz::digest::Error> {
    use std::io::{BufReader, Read};
    let magic = susz::format::MAGIC;
    // the first bytes, up to the magic's length
    let head = |r: &mut dyn Read| -> std::io::Result<Vec<u8>> {
        let mut b = Vec::with_capacity(magic.len());
        r.take(magic.len() as u64).read_to_end(&mut b)?;
        Ok(b)
    };
    if path == "-" {
        let mut stdin = std::io::stdin().lock();
        let first = head(&mut stdin)?;
        if first == magic {
            let mut bytes = first;
            stdin.read_to_end(&mut bytes)?;
            return susz::digest::susz(&bytes, names, each).map(|s| (s, true));
        }
        let r = BufReader::with_capacity(1 << 20, std::io::Cursor::new(first).chain(stdin));
        return susz::digest::ndjson(r, names, each).map(|s| (s, false));
    }
    let mut f = std::fs::File::open(path)?;
    if head(&mut f)? == magic {
        drop(f);
        let bytes = read_file(path);
        return susz::digest::susz(&bytes, names, each).map(|s| (s, true));
    }
    use std::io::Seek;
    f.rewind()?;
    susz::digest::ndjson(BufReader::with_capacity(1 << 20, f), names, each).map(|s| (s, false))
}

fn digest_failed(path: &str, e: susz::digest::Error) -> ! {
    let p = if path == "-" { "stdin" } else { path };
    eprintln!("susz: {p}: {e}");
    exit(2)
}

// What was read, on stderr: the counts differ between the forms of one
// export (proof blocks, mdata), the declarations do not.
fn digest_counts(path: &str, s: &susz::digest::Summary, susz_form: bool) {
    let p = if path == "-" { "stdin" } else { path };
    if susz_form {
        eprintln!(
            "{p}: Susz, {} names, {} levels, {} expressions ({} in proof blocks)",
            s.names, s.levels, s.exprs, s.extra
        );
    } else {
        eprintln!(
            "{p}: ndjson, {} names, {} levels, {} expressions ({} mdata)",
            s.names, s.levels, s.exprs, s.extra
        );
    }
}

fn cmd_digest(args: &[String]) {
    use std::io::Write;
    use susz::digest::{hex, printable, KINDS};
    let mut each = false;
    let mut files = Vec::new();
    for a in args {
        match a.as_str() {
            "--each" => each = true,
            "-" => files.push(a.clone()),
            a if a.starts_with('-') => usage(),
            a => files.push(a.to_string()),
        }
    }
    let stdin_twice = files.len() == 2 && files[0] == "-" && files[1] == "-";
    if files.is_empty() || files.len() > 2 || (each && files.len() == 2) || stdin_twice {
        usage();
    }
    let out = std::io::stdout();
    if files.len() == 1 {
        let path = &files[0];
        let mut w = std::io::BufWriter::with_capacity(1 << 16, out.lock());
        let mut line = |e: susz::digest::Entry<'_>| -> std::io::Result<()> {
            writeln!(
                w,
                "{} {} {}",
                hex(&e.digest),
                KINDS[e.kind as usize],
                printable(e.name)
            )
        };
        let res = if each {
            digest_of(path, true, &mut line)
        } else {
            digest_of(path, false, &mut |_| Ok(()))
        };
        drop(line);
        let (s, form) = res.unwrap_or_else(|e| digest_failed(path, e));
        digest_counts(path, &s, form);
        let res = writeln!(w, "{}", hex(&s.digest))
            .and_then(|()| writeln!(w, "{}", s.declarations_line()))
            .and_then(|()| w.flush());
        if let Err(e) = res {
            eprintln!("susz: cannot write the digest: {e}");
            exit(2);
        }
        return;
    }
    // two files, one after the other: only one file's tables at a time
    let mut got = Vec::new();
    for path in &files {
        let mut digests = Vec::new();
        let mut names = Vec::new();
        let (s, form) = digest_of(path, true, &mut |e| {
            digests.push(e.digest);
            names.push(e.name.to_string());
            Ok(())
        })
        .unwrap_or_else(|e| digest_failed(path, e));
        digest_counts(path, &s, form);
        got.push(Got {
            sum: s,
            digests,
            names,
        });
    }
    let (a, b) = (&got[0], &got[1]);
    let mut w = std::io::BufWriter::new(out.lock());
    let res = digest_compare(&mut w, a, b).and_then(|same| {
        w.flush()?;
        Ok(same)
    });
    match res {
        Ok(true) => {}
        Ok(false) => exit(1),
        Err(e) => {
            eprintln!("susz: cannot write the comparison: {e}");
            exit(2);
        }
    }
}

// How many differing declarations are named.
const SHOWN: usize = 10;

// Writes the comparison; true when the two files hold the same declarations
// in the same order.
fn digest_compare(w: &mut impl std::io::Write, a: &Got, b: &Got) -> std::io::Result<bool> {
    use std::collections::HashMap;
    use susz::digest::{hex, printable};
    if a.sum.digest == b.sum.digest {
        writeln!(w, "same: {}", hex(&a.sum.digest))?;
        writeln!(w, "{}", a.sum.declarations_line())?;
        return Ok(true);
    }
    writeln!(w, "different: A {}", hex(&a.sum.digest))?;
    writeln!(w, "           B {}", hex(&b.sum.digest))?;
    writeln!(w, "A: {}", a.sum.declarations_line())?;
    writeln!(w, "B: {}", b.sum.declarations_line())?;
    // each side's declarations that the other one does not hold (as a
    // multiset of digests), in file order; and those it does
    let unmatched = |x: &Got, y: &Got| -> (Vec<usize>, Vec<usize>) {
        let mut have: HashMap<&susz::digest::Hash, u32> = HashMap::new();
        for d in &y.digests {
            *have.entry(d).or_default() += 1;
        }
        let (mut un, mut kept) = (Vec::new(), Vec::new());
        for (i, d) in x.digests.iter().enumerate() {
            match have.get_mut(d) {
                Some(c) if *c > 0 => {
                    *c -= 1;
                    kept.push(i);
                }
                _ => un.push(i),
            }
        }
        (un, kept)
    };
    let (ua, ka) = unmatched(a, b);
    let (ub, kb) = unmatched(b, a);
    let kept_order_differs = ka
        .iter()
        .zip(&kb)
        .any(|(&i, &j)| a.digests[i] != b.digests[j]);
    if ua.is_empty() && ub.is_empty() {
        let i = (0..a.digests.len())
            .find(|&i| a.digests[i] != b.digests[i])
            .unwrap_or(0);
        writeln!(
            w,
            "the same declarations in another order: the first difference is declaration #{}: A {}, B {}",
            i + 1,
            printable(&a.names[i]),
            printable(&b.names[i])
        )?;
        return Ok(false);
    }
    // by name: changed (on both sides), only in A, only in B
    let in_b: HashMap<&str, usize> = ub.iter().map(|&j| (b.names[j].as_str(), j)).collect();
    let in_a: HashMap<&str, usize> = ua.iter().map(|&i| (a.names[i].as_str(), i)).collect();
    let mut lines = Vec::new();
    let (mut changed, mut only_a, mut only_b) = (0u64, 0u64, 0u64);
    for &i in &ua {
        let n = a.names[i].as_str();
        match in_b.get(n) {
            Some(&j) => {
                changed += 1;
                lines.push(format!(
                    "  changed {} (A #{}, B #{})",
                    printable(n),
                    i + 1,
                    j + 1
                ));
            }
            None => {
                only_a += 1;
                lines.push(format!("  only in A: {} (#{})", printable(n), i + 1));
            }
        }
    }
    for &j in &ub {
        let n = b.names[j].as_str();
        if !in_a.contains_key(n) {
            only_b += 1;
            lines.push(format!("  only in B: {} (#{})", printable(n), j + 1));
        }
    }
    writeln!(
        w,
        "{} declarations differ: {changed} changed, {only_a} only in A, {only_b} only in B",
        changed + only_a + only_b
    )?;
    for l in lines.iter().take(SHOWN) {
        writeln!(w, "{l}")?;
    }
    if lines.len() > SHOWN {
        writeln!(w, "  and {} more", lines.len() - SHOWN)?;
    }
    if kept_order_differs {
        writeln!(
            w,
            "the declarations both files hold are in another order too"
        )?;
    }
    Ok(false)
}
