// Writes the test vectors to tests/vectors/{accept,reject,decline,index}/:
// NAME.asm (the source), NAME.susz (the bytes), NAME.expect.
//
//   cargo run --example gen-vectors

use std::path::Path;

fn main() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/vectors");
    for d in ["accept", "reject", "decline", "index"] {
        let p = root.join(d);
        let _ = std::fs::remove_dir_all(&p);
        std::fs::create_dir_all(&p).unwrap();
    }
    let all = susz::vectors::all();
    for v in &all {
        let a = susz::vectors::build(v);
        let dir = root.join(v.dir());
        std::fs::write(dir.join(format!("{}.asm", v.name)), &v.src).unwrap();
        std::fs::write(dir.join(format!("{}.susz", v.name)), &a.bytes).unwrap();
        std::fs::write(
            dir.join(format!("{}.expect", v.name)),
            susz::vectors::expect_text(v, &a),
        )
        .unwrap();
    }
    eprintln!("{} vectors written to {}", all.len(), root.display());
}
