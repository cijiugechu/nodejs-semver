use crate::scan::{identifiers, may_start_whitespace, number, skip_whitespace, whitespace_len};
use crate::{Identifiers, Version};

pub(crate) fn parse(input: &str) -> Option<Version> {
    let bytes = input.as_bytes();
    let mut i = usize::from(matches!(bytes.first(), Some(b'v' | b'V')));
    if bytes.get(i).copied().is_some_and(may_start_whitespace) {
        i = skip_whitespace(input, i);
    }

    let (major, next) = number(bytes, i)?;
    i = next;
    if bytes.get(i) != Some(&b'.') {
        return None;
    }
    i += 1;

    let (minor, next) = number(bytes, i)?;
    i = next;
    if bytes.get(i) != Some(&b'.') {
        return None;
    }
    i += 1;

    let (patch, next) = number(bytes, i)?;
    i = next;

    let (pre_release, i) = match bytes.get(i).copied() {
        None => return Some(Version::new_empty(major, minor, patch)),
        Some(b'+') => {
            let (build, _) = identifiers(input, i + 1)?;
            return Some(Version::new_with_identifiers(
                major,
                minor,
                patch,
                Identifiers::Empty,
                build,
            ));
        }
        Some(b'-') => identifiers(input, i + 1)?,
        Some(ch) if ch.is_ascii_alphanumeric() => identifiers(input, i)?,
        Some(ch) if may_start_whitespace(ch) && whitespace_len(input, i) > 0 => {
            return Some(Version::new_empty(major, minor, patch));
        }
        _ => return None,
    };

    let build = if bytes.get(i) == Some(&b'+') {
        identifiers(input, i + 1)?.0
    } else {
        Identifiers::Empty
    };

    Some(Version::new_with_identifiers(
        major,
        minor,
        patch,
        pre_release,
        build,
    ))
}
