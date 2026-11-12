// INDEX with keys that share ever longer prefixes (a, a.a, a.a.a, ...):
// their expanded size grows with the square of the INDEX size. The reader
// keeps expanded keys only up to a cap linear in INDEX's length, and scans
// the front-coded table past it, with the same answers.

use std::path::PathBuf;
use susz::index::{self, Lookup};
use susz::pack::{pack_to_vec, Options};

fn chain(n: usize) -> String {
    let mut s = String::from("{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}\n");
    for i in 1..=n {
        s += &format!(
            "{{\"in\":{i},\"str\":{{\"pre\":{},\"str\":\"a\"}}}}\n",
            i - 1
        );
    }
    s += "{\"ie\":0,\"sort\":0}\n";
    for i in 1..=n {
        s += &format!(
            "{{\"axiom\":{{\"isUnsafe\":false,\"levelParams\":[],\"name\":{i},\"type\":0}}}}\n"
        );
    }
    s
}

#[test]
fn growing_shared_prefixes() {
    let n = 400;
    let path = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("index-chain.ndjson");
    std::fs::write(&path, chain(n)).unwrap();
    let (bytes, _) = pack_to_vec(path.to_str().unwrap(), &Options::default()).unwrap();
    let f = susz::read::File::open(&bytes).unwrap();
    let len = f.section(susz::format::SEC_INDEX).unwrap().length;
    // 3 bytes per component: the keys expand to about 3 n^2 / 2 bytes
    let expanded: u64 = (1..=n as u64).map(|i| 3 * i).sum();
    assert!(expanded > len * index::KEY_BYTES_PER_INDEX_BYTE);

    let capped = index::parse(&f).unwrap();
    assert!(
        !capped.expanded(),
        "the default cap keeps the expanded keys"
    );
    let small = index::parse_capped(&f, 64).unwrap();
    assert!(!small.expanded());
    let full = index::parse_capped(&f, u64::MAX).unwrap();
    assert!(full.expanded());

    index::verify_index(&f).unwrap();
    let mut many = Lookup::new(&f).unwrap();
    for j in 0..n {
        let k = full.key(j);
        assert_eq!(k.len(), 3 * (j + 1));
        assert_eq!(capped.key(j), k);
        let d = full.decl(j);
        assert_eq!(d, j as u32);
        assert_eq!(capped.find(&k), Some(d));
        assert_eq!(small.find(&k), Some(d));
        assert_eq!(full.find(&k), Some(d));
        assert_eq!(many.find(&k).unwrap().decl, d);
    }
    // keys between and around the table are not found, by either search
    for k in [
        index::key_of_dotted("b"),
        index::key_of_dotted("a.b"),
        index::key_of_dotted("a.a.0"),
        vec![1, 1, b'a', 1],
        vec![],
    ] {
        assert_eq!(capped.find(&k), None);
        assert_eq!(full.find(&k), None);
    }
    let mut longer = full.key(n - 1);
    longer.extend_from_slice(&[1, 1, b'a']);
    assert_eq!(capped.find(&longer), None);
    assert_eq!(full.find(&longer), None);
}
