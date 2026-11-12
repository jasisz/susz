// The `susz` command: pack, verify, unpack.

use std::process::exit;
use susz::pack::{self, Fault, Options};
use susz::read::Outcome;

const USAGE: &str = "usage:
  susz pack IN.ndjson OUT.susz [--no-index] [--threads N]
  susz verify FILE.susz [--index]
  susz unpack FILE.susz OUT.ndjson

pack exits 0 when OUT is written, 1 when IN is not a valid export,
2 when it cannot be packed (a limit, an unknown record or field, I/O,
an internal error). verify exits 0 accepted, 1 rejected (the file is
malformed, or a declaration fails a rule a reader checks without types,
such as rule P), 2 declined or unreadable. unpack exits 0 written, 1 rejected, 2 declined or I/O.";

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
        _ => usage(),
    }
}

fn usage() -> ! {
    eprintln!("{USAGE}");
    exit(2)
}

fn cmd_pack(args: &[String]) {
    let mut opts = Options::default();
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

fn read_file(path: &str) -> Vec<u8> {
    std::fs::read(path).unwrap_or_else(|e| {
        eprintln!("susz: cannot read {path}: {e}");
        exit(2)
    })
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
    let tmp = format!("{out}.tmp-{}", std::process::id());
    susz::cleanup::register(&tmp);
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
    susz::cleanup::unregister();
    if let Err(e) = res {
        let _ = std::fs::remove_file(&tmp);
        eprintln!("susz: {e}");
        let code = match &e {
            susz::unpack::UnpackError::File(f) if !f.class.declines() => 1,
            _ => 2,
        };
        exit(code);
    }
}
