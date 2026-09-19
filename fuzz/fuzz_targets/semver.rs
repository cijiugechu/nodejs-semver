#![no_main]

use nodejs_semver::{Range, Version};

libfuzzer_sys::fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) {
        let _ = Version::parse(s);
        let _ = Range::parse(s);
    }
});
