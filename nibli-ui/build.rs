// Bind tab-local review snapshots to the actual workspace sources in the bundle.
// This is a content identifier, not a proof certificate or a release signature.
use sha2::{Digest, Sha256};
use std::{fs, path::Path};

fn hash_tree(root: &Path, path: &Path, hash: &mut Sha256) {
    if path.is_dir() {
        println!("cargo:rerun-if-changed={}", path.display());
        let mut entries: Vec<_> = fs::read_dir(path)
            .expect("read source directory")
            .map(|entry| entry.expect("read source entry").path())
            .collect();
        entries.sort();
        for entry in entries {
            let name = entry
                .file_name()
                .and_then(|s| s.to_str())
                .unwrap_or_default();
            if matches!(name, "target" | "dist" | ".git") {
                continue;
            }
            hash_tree(root, &entry, hash);
        }
    } else if path.is_file() {
        println!("cargo:rerun-if-changed={}", path.display());
        let name = path
            .strip_prefix(root)
            .expect("workspace source")
            .to_string_lossy();
        let bytes = fs::read(path).expect("read source file");
        hash.update((name.len() as u64).to_le_bytes());
        hash.update(name.as_bytes());
        hash.update((bytes.len() as u64).to_le_bytes());
        hash.update(bytes);
    }
}

fn main() {
    let manifest = std::env::var("CARGO_MANIFEST_DIR").expect("manifest directory");
    let root = Path::new(&manifest).parent().expect("workspace");
    let mut hash = Sha256::new();
    for name in [
        "Cargo.toml",
        "Cargo.lock",
        "nibli-types",
        "nibli-protocol",
        "nibli-lexicon",
        "nibli-kr",
        "nibli-semantics",
        "nibli-reason",
        "nibli-session",
        "nibli-render",
        "nibli-formalize",
        "nibli-ui",
    ] {
        hash_tree(root, &root.join(name), &mut hash);
    }
    println!("cargo:rustc-env=NIBLI_BUILD_ID={:x}", hash.finalize());
}
