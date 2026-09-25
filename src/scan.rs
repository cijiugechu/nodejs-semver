//! Scanning primitives shared by every version and range parser.

use crate::{Identifier, Identifiers, MAX_SAFE_INTEGER};

/// Whitespace as matched by JavaScript's `\s`, which node-semver uses to trim
/// and split its input. Every parser must use this definition.
pub(crate) fn is_whitespace(ch: char) -> bool {
    matches!(ch, '\t'..='\r' | ' ' | '\u{A0}' | '\u{1680}' | '\u{2000}'..='\u{200A}')
        || matches!(
            ch,
            '\u{2028}' | '\u{2029}' | '\u{202F}' | '\u{205F}' | '\u{3000}' | '\u{FEFF}'
        )
}

/// Cheap pre-check for hot paths: only these first bytes can start whitespace.
#[inline(always)]
pub(crate) fn may_start_whitespace(byte: u8) -> bool {
    byte <= b' ' || byte >= 0x80
}

/// Byte length of the whitespace character starting at byte `i`, or 0.
///
/// Matches the UTF-8 encodings of [`is_whitespace`] directly so hot scanning
/// loops stay free of calls and char decoding.
#[inline(always)]
pub(crate) fn whitespace_len(input: &str, i: usize) -> usize {
    let bytes = input.as_bytes();
    match bytes.get(i) {
        Some(b'\t'..=b'\r' | b' ') => 1,
        Some(0x80..) => match &bytes[i..] {
            [0xC2, 0xA0, ..] => 2,
            [0xE1, 0x9A, 0x80, ..]
            | [0xE2, 0x80, 0x80..=0x8A | 0xA8 | 0xA9 | 0xAF, ..]
            | [0xE2, 0x81, 0x9F, ..]
            | [0xE3, 0x80, 0x80, ..]
            | [0xEF, 0xBB, 0xBF, ..] => 3,
            _ => 0,
        },
        _ => 0,
    }
}

#[inline(always)]
pub(crate) fn skip_whitespace(input: &str, mut i: usize) -> usize {
    loop {
        match whitespace_len(input, i) {
            0 => return i,
            len => i += len,
        }
    }
}

pub(crate) fn trim(input: &str) -> &str {
    input.trim_matches(is_whitespace)
}

#[inline]
pub(crate) fn number(bytes: &[u8], start: usize) -> Option<(u64, usize)> {
    let mut i = start;
    let mut value = 0u64;

    while let Some(ch @ b'0'..=b'9') = bytes.get(i).copied() {
        value = value.checked_mul(10)?.checked_add(u64::from(ch - b'0'))?;
        if value > MAX_SAFE_INTEGER {
            return None;
        }
        i += 1;
    }

    (i > start).then_some((value, i))
}

#[inline]
pub(crate) fn identifiers(input: &str, start: usize) -> Option<(Identifiers, usize)> {
    let bytes = input.as_bytes();
    let mut i = start;
    let mut identifiers = Identifiers::Empty;

    loop {
        let ident_start = i;
        while matches!(
            bytes.get(i),
            Some(b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-')
        ) {
            i += 1;
        }

        if i == ident_start {
            return None;
        }

        let ident = &input[ident_start..i];
        if ident.bytes().all(|ch| ch.is_ascii_digit()) {
            identifiers.push(match ident.parse::<u64>() {
                Ok(value) => Identifier::Numeric(value),
                Err(_) => Identifier::AlphaNumeric(ident.to_string()),
            });
        } else {
            identifiers.push(Identifier::AlphaNumeric(ident.to_string()));
        }

        if bytes.get(i) != Some(&b'.') {
            return Some((identifiers, i));
        }

        i += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn whitespace_matches_javascript() {
        for ch in [
            '\t', '\n', '\u{0B}', '\u{0C}', '\r', ' ', '\u{A0}', '\u{1680}', '\u{2000}',
            '\u{200A}', '\u{2028}', '\u{2029}', '\u{202F}', '\u{205F}', '\u{3000}', '\u{FEFF}',
        ] {
            assert!(is_whitespace(ch), "{ch:?}");
        }
        // Rust's `char::is_whitespace` includes NEL, JavaScript's `\s` does not.
        for ch in ['\u{85}', '\u{200B}', 'Ł', 'x', '|'] {
            assert!(!is_whitespace(ch), "{ch:?}");
        }
        assert_eq!(skip_whitespace(" \u{A0}\t\u{3000}1", 0), 7);
    }

    #[test]
    fn whitespace_len_agrees_with_is_whitespace_for_every_char() {
        let mut buf = [0; 4];
        for ch in (0..=u32::from(char::MAX)).filter_map(char::from_u32) {
            let encoded = ch.encode_utf8(&mut buf);
            let expected = if is_whitespace(ch) { ch.len_utf8() } else { 0 };
            assert_eq!(whitespace_len(encoded, 0), expected, "{ch:?}");
            // Positions inside a multi-byte character are never whitespace.
            for i in 1..encoded.len() {
                assert_eq!(whitespace_len(encoded, i), 0, "{ch:?} at {i}");
            }
        }
    }
}
