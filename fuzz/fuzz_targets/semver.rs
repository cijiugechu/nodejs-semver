#![no_main]

use nodejs_semver::{Version, Range};

libfuzzer_sys::fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) {
        if s.chars().all(|s| !s.is_control()) {
            let _ = Version::parse(&s);
            let _ = Range::parse(&s);
        }
    }
});
