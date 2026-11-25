//! The checker on small exports that decode: reading and then checking every
//! declaration must end in a verdict, never a panic or a hang.
#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if data.len() > 64 * 1024 {
        return;
    }
    if let Ok((env, _)) = nitrolean::reader::read(data) {
        let _ = nitrolean::check::check_env(&env);
    }
});
