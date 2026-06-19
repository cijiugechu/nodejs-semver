use crate::{Identifier, Identifiers, Version, MAX_SAFE_INTEGER};

pub(crate) fn parse(input: &str) -> Option<Version> {
    let bytes = input.as_bytes();
    let mut i = 0;

    if matches!(bytes.get(i), Some(b'v' | b'V')) {
        i += 1;
    }
    while matches!(
        bytes.get(i),
        Some(b' ' | b'\t' | b'\n' | b'\r' | 0x0B | 0x0C)
    ) {
        i += 1;
    }

    let (major, next) = parse_core_number(bytes, i)?;
    i = next;
    if bytes.get(i) != Some(&b'.') {
        return None;
    }
    i += 1;

    let (minor, next) = parse_core_number(bytes, i)?;
    i = next;
    if bytes.get(i) != Some(&b'.') {
        return None;
    }
    i += 1;

    let (patch, next) = parse_core_number(bytes, i)?;
    i = next;

    match bytes.get(i).copied() {
        None => Some(Version::new_empty(major, minor, patch)),
        Some(b' ' | b'\t' | b'\n' | b'\r' | 0x0B | 0x0C) => {
            Some(Version::new_empty(major, minor, patch))
        }
        Some(b'+') => {
            let (parsed_build, _) = parse_identifiers(input, i + 1)?;
            Some(Version::new_with_identifiers(
                major,
                minor,
                patch,
                Identifiers::Empty,
                parsed_build,
            ))
        }
        Some(b'-') => {
            let (parsed_pre, next) = parse_identifiers(input, i + 1)?;
            i = next;

            if bytes.get(i) == Some(&b'+') {
                let (parsed_build, _) = parse_identifiers(input, i + 1)?;
                Some(Version::new_with_identifiers(
                    major,
                    minor,
                    patch,
                    parsed_pre,
                    parsed_build,
                ))
            } else {
                Some(Version::new_with_identifiers(
                    major,
                    minor,
                    patch,
                    parsed_pre,
                    Identifiers::Empty,
                ))
            }
        }
        Some(ch) if ch.is_ascii_alphanumeric() => {
            let (parsed_pre, next) = parse_identifiers(input, i)?;
            i = next;

            if bytes.get(i) == Some(&b'+') {
                let (parsed_build, _) = parse_identifiers(input, i + 1)?;
                Some(Version::new_with_identifiers(
                    major,
                    minor,
                    patch,
                    parsed_pre,
                    parsed_build,
                ))
            } else {
                Some(Version::new_with_identifiers(
                    major,
                    minor,
                    patch,
                    parsed_pre,
                    Identifiers::Empty,
                ))
            }
        }
        _ => None,
    }
}

fn parse_core_number(bytes: &[u8], start: usize) -> Option<(u64, usize)> {
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

fn parse_identifiers(input: &str, start: usize) -> Option<(Identifiers, usize)> {
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
