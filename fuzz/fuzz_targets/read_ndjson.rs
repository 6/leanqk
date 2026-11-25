//! The NDJSON export reader on arbitrary bytes: it must return an environment
//! or an error, never panic.
#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let _ = nitrolean::reader::read(data);
});
