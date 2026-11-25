//! The .olean reader on arbitrary bytes. The input is written as the module
//! `FuzzRoot` in a fresh directory and loaded with no toolchain, so only
//! imports that are themselves in that directory resolve (the seeds are
//! modules with no imports). Loading must give an environment or an error,
//! never panic.
#![no_main]

use std::path::PathBuf;
use std::sync::OnceLock;

use libfuzzer_sys::fuzz_target;
use nitrolean::olean::{Options, load};

fn dir() -> &'static PathBuf {
    static DIR: OnceLock<PathBuf> = OnceLock::new();
    DIR.get_or_init(|| {
        let d = std::env::temp_dir().join(format!("nitrolean-fuzz-olean-{}", std::process::id()));
        std::fs::create_dir_all(&d).expect("temp dir");
        d
    })
}

fuzz_target!(|data: &[u8]| {
    let path = dir().join("FuzzRoot.olean");
    if std::fs::write(&path, data).is_err() {
        return;
    }
    let opts = Options {
        search_path: vec![dir().clone()],
        threads: 1,
        no_toolchain: true,
        modules: Vec::new(),
    };
    let _ = load(path.to_str().expect("utf-8 temp path"), &opts);
});
