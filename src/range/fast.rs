use super::{Bound, BoundSet, Operation, Predicate, Range};
use crate::{Identifier, Identifiers, Version, MAX_SAFE_INTEGER};

pub(super) fn parse(input: &str) -> Option<Range> {
    let bytes = input.as_bytes();
    let first = bytes.first().copied();

    if first == Some(b'^') {
        return parse_caret(input).or_else(|| parse_or_if_present(input));
    }

    if matches!(first, Some(b'>' | b'<' | b'=')) {
        return parse_comparator_set(input).or_else(|| parse_or_if_present(input));
    }

    if let Some(range) = parse_exact_version(bytes)
        .and_then(|version| BoundSet::exact(version).map(|bound_set| Range(vec![bound_set])))
    {
        return Some(range);
    }

    if matches!(first, Some(b'x' | b'X' | b'*')) {
        return parse_partial_wildcard(input).or_else(|| parse_or_if_present(input));
    }

    if matches!(first, Some(b'v' | b'V' | b'0'..=b'9')) {
        if let Some(range) = parse_hyphen(input) {
            return Some(range);
        }

        return parse_partial_wildcard(input).or_else(|| parse_or_if_present(input));
    }

    None
}

fn parse_or_if_present(input: &str) -> Option<Range> {
    input.contains("||").then(|| parse_or(input)).flatten()
}

fn parse_or(input: &str) -> Option<Range> {
    let mut sets = Vec::new();

    for part in input.split("||") {
        let part = part.trim();
        if part.is_empty() {
            return None;
        }

        let Range(mut part_sets) = parse(part)?;
        sets.append(&mut part_sets);
    }

    (!sets.is_empty()).then_some(Range(sets))
}

fn parse_hyphen(input: &str) -> Option<Range> {
    if input.as_bytes().contains(&b'+') {
        return None;
    }

    let bytes = input.as_bytes();
    let (lower, mut i) = parse_partial(input, 0)?;

    i = skip_spaces1(bytes, i)?;
    if bytes.get(i) != Some(&b'-') {
        return None;
    }
    i += 1;
    i = skip_spaces1(bytes, i)?;

    let (upper, i) = parse_partial(input, i)?;
    if i != bytes.len() {
        return None;
    }

    BoundSet::new(
        Bound::Lower(Predicate::Including(partial_to_version(lower))),
        Bound::Upper(hyphen_upper(upper)),
    )
    .map(|bound| Range(vec![bound]))
}

fn hyphen_upper(partial: Partial) -> Predicate {
    match partial {
        Partial {
            major: None,
            minor: None,
            patch: None,
            ..
        } => Predicate::Excluding(Version::from((0, 0, 0, 0))),
        Partial {
            major: Some(major),
            minor: None,
            patch: None,
            ..
        } => Predicate::Excluding(Version::from((major + 1, 0, 0, 0))),
        Partial {
            major: Some(major),
            minor: Some(minor),
            patch: None,
            ..
        } => Predicate::Excluding(Version::from((major, minor + 1, 0, 0))),
        partial => Predicate::Including(partial_to_version(partial)),
    }
}

fn parse_comparator_set(input: &str) -> Option<Range> {
    if input.as_bytes().contains(&b'+') {
        return None;
    }

    let bytes = input.as_bytes();
    let mut i = 0;
    let mut current: Option<BoundSet> = None;

    loop {
        let (bound_set, next) = parse_comparator(input, i)?;
        current = Some(if let Some(current) = current {
            current.intersect(&bound_set)?
        } else {
            bound_set
        });
        i = next;

        if i == bytes.len() {
            break;
        }

        if !is_space(bytes.get(i).copied()) {
            return None;
        }
        while is_space(bytes.get(i).copied()) {
            i += 1;
        }
        if i == bytes.len() {
            return None;
        }
    }

    current.map(|bound| Range(vec![bound]))
}

fn parse_comparator(input: &str, start: usize) -> Option<(BoundSet, usize)> {
    let bytes = input.as_bytes();
    let (operation, mut i) = parse_operation(bytes, start)?;

    while is_space(bytes.get(i).copied()) {
        i += 1;
    }

    let (partial, i) = parse_partial(input, i)?;
    primitive_range(operation, partial).map(|bound| (bound, i))
}

fn parse_operation(bytes: &[u8], start: usize) -> Option<(Operation, usize)> {
    match (bytes.get(start).copied()?, bytes.get(start + 1).copied()) {
        (b'>', Some(b'=')) => Some((Operation::GreaterThanEquals, start + 2)),
        (b'>', _) => Some((Operation::GreaterThan, start + 1)),
        (b'=', _) => Some((Operation::Exact, start + 1)),
        (b'<', Some(b'=')) => Some((Operation::LessThanEquals, start + 2)),
        (b'<', _) => Some((Operation::LessThan, start + 1)),
        _ => None,
    }
}

fn primitive_range(operation: Operation, partial: Partial) -> Option<BoundSet> {
    use Operation::*;

    match (operation, partial) {
        (GreaterThanEquals, partial) => {
            BoundSet::at_least(Predicate::Including(partial_to_version(partial)))
        }
        (
            GreaterThan,
            Partial {
                major: Some(major),
                minor: Some(minor),
                patch: None,
                ..
            },
        ) => BoundSet::at_least(Predicate::Including(Version::from((major, minor + 1, 0)))),
        (
            GreaterThan,
            Partial {
                major: Some(major),
                minor: None,
                patch: None,
                ..
            },
        ) => BoundSet::at_least(Predicate::Including(Version::from((major + 1, 0, 0)))),
        (GreaterThan, partial) => {
            BoundSet::at_least(Predicate::Excluding(partial_to_version(partial)))
        }
        (
            LessThan,
            Partial {
                major: Some(major),
                minor: Some(minor),
                patch: None,
                ..
            },
        ) => BoundSet::at_most(Predicate::Excluding(Version::from((major, minor, 0, 0)))),
        (LessThan, partial) => BoundSet::at_most(Predicate::Excluding(partial_to_version(partial))),
        (
            LessThanEquals,
            Partial {
                major,
                minor: None,
                patch: None,
                ..
            },
        ) => BoundSet::at_most(Predicate::Including(Version::from((
            major.unwrap_or(0),
            MAX_SAFE_INTEGER,
            MAX_SAFE_INTEGER,
        )))),
        (
            LessThanEquals,
            Partial {
                major,
                minor,
                patch: None,
                ..
            },
        ) => BoundSet::at_most(Predicate::Including(Version::from((
            major.unwrap_or(0),
            minor.unwrap_or(0),
            MAX_SAFE_INTEGER,
        )))),
        (LessThanEquals, partial) => {
            BoundSet::at_most(Predicate::Including(partial_to_version(partial)))
        }
        (
            Exact,
            Partial {
                major: Some(major),
                minor: Some(minor),
                patch: Some(patch),
                pre_release,
            },
        ) => BoundSet::exact(Version::new_with_identifiers(
            major,
            minor,
            patch,
            pre_release,
            Identifiers::Empty,
        )),
        (
            Exact,
            Partial {
                major: Some(major),
                minor: Some(minor),
                ..
            },
        ) => BoundSet::new(
            Bound::Lower(Predicate::Including(Version::from((major, minor, 0)))),
            Bound::Upper(Predicate::Excluding(Version::from((
                major,
                minor + 1,
                0,
                0,
            )))),
        ),
        (
            Exact,
            Partial {
                major: Some(major), ..
            },
        ) => BoundSet::new(
            Bound::Lower(Predicate::Including(Version::from((major, 0, 0)))),
            Bound::Upper(Predicate::Excluding(Version::from((major + 1, 0, 0, 0)))),
        ),
        _ => None,
    }
}

fn partial_to_version(partial: Partial) -> Version {
    Version::new_with_identifiers(
        partial.major.unwrap_or(0),
        partial.minor.unwrap_or(0),
        partial.patch.unwrap_or(0),
        partial.pre_release,
        Identifiers::Empty,
    )
}

fn parse_caret(input: &str) -> Option<Range> {
    let bytes = input.as_bytes();
    let mut i = 1;

    while matches!(
        bytes.get(i),
        Some(b' ' | b'\t' | b'\n' | b'\r' | 0x0B | 0x0C)
    ) {
        i += 1;
    }

    let (partial, i) = parse_partial(input, i)?;
    if i != bytes.len() {
        return None;
    }

    caret_range(partial).map(|bound| Range(vec![bound]))
}

fn parse_partial_wildcard(input: &str) -> Option<Range> {
    let (partial, i) = parse_partial(input, 0)?;
    if i != input.len() {
        return None;
    }

    partial_wildcard_range(partial).map(|bound| Range(vec![bound]))
}

fn partial_wildcard_range(partial: Partial) -> Option<BoundSet> {
    match partial {
        Partial { major: None, .. } => {
            BoundSet::at_least(Predicate::Including(Version::from((0, 0, 0))))
        }
        Partial {
            major: Some(major),
            minor: None,
            ..
        } => BoundSet::new(
            Bound::Lower(Predicate::Including(Version::from((major, 0, 0)))),
            Bound::Upper(Predicate::Excluding(Version::from((major + 1, 0, 0, 0)))),
        ),
        Partial {
            major: Some(major),
            minor: Some(minor),
            patch: None,
            ..
        } => BoundSet::new(
            Bound::Lower(Predicate::Including(Version::from((major, minor, 0)))),
            Bound::Upper(Predicate::Excluding(Version::from((
                major,
                minor + 1,
                0,
                0,
            )))),
        ),
        _ => None,
    }
}

fn caret_range(partial: Partial) -> Option<BoundSet> {
    match partial {
        Partial {
            major: Some(0),
            minor: None,
            patch: None,
            ..
        } => BoundSet::at_most(Predicate::Excluding(Version::from((1, 0, 0, 0)))),
        Partial {
            major: Some(0),
            minor: Some(minor),
            patch: None,
            ..
        } => BoundSet::new(
            Bound::Lower(Predicate::Including(Version::from((0, minor, 0)))),
            Bound::Upper(Predicate::Excluding(Version::from((0, minor + 1, 0, 0)))),
        ),
        Partial {
            major: Some(major),
            minor: None,
            patch: None,
            ..
        } => BoundSet::new(
            Bound::Lower(Predicate::Including(Version::from((major, 0, 0)))),
            Bound::Upper(Predicate::Excluding(Version::from((major + 1, 0, 0, 0)))),
        ),
        Partial {
            major: Some(major),
            minor: Some(minor),
            patch: None,
            ..
        } => BoundSet::new(
            Bound::Lower(Predicate::Including(Version::from((major, minor, 0)))),
            Bound::Upper(Predicate::Excluding(Version::from((major + 1, 0, 0, 0)))),
        ),
        Partial {
            major: Some(major),
            minor: Some(minor),
            patch: Some(patch),
            pre_release,
        } => BoundSet::new(
            Bound::Lower(Predicate::Including(Version::new_with_identifiers(
                major,
                minor,
                patch,
                pre_release,
                Identifiers::Empty,
            ))),
            Bound::Upper(Predicate::Excluding(match (major, minor, patch) {
                (0, 0, n) => Version::from((0, 0, n + 1, 0)),
                (0, n, _) => Version::from((0, n + 1, 0, 0)),
                (n, _, _) => Version::from((n + 1, 0, 0, 0)),
            })),
        ),
        _ => None,
    }
}

fn parse_exact_version(bytes: &[u8]) -> Option<Version> {
    let (major, mut i) = parse_number(bytes, 0)?;
    if bytes.get(i) != Some(&b'.') {
        return None;
    }
    i += 1;

    let (minor, next) = parse_number(bytes, i)?;
    i = next;
    if bytes.get(i) != Some(&b'.') {
        return None;
    }
    i += 1;

    let (patch, i) = parse_number(bytes, i)?;
    if i != bytes.len() {
        return None;
    }

    Some(Version::from((major, minor, patch)))
}

fn parse_number(bytes: &[u8], start: usize) -> Option<(u64, usize)> {
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

fn is_space(ch: Option<u8>) -> bool {
    matches!(ch, Some(b' ' | b'\t' | b'\n' | b'\r' | 0x0B | 0x0C))
}

fn skip_spaces1(bytes: &[u8], start: usize) -> Option<usize> {
    if !is_space(bytes.get(start).copied()) {
        return None;
    }

    let mut i = start + 1;
    while is_space(bytes.get(i).copied()) {
        i += 1;
    }

    Some(i)
}

#[derive(Debug)]
struct Partial {
    major: Option<u64>,
    minor: Option<u64>,
    patch: Option<u64>,
    pre_release: Identifiers,
}

fn parse_partial(input: &str, start: usize) -> Option<(Partial, usize)> {
    let bytes = input.as_bytes();
    let mut i = start;

    if bytes.get(i) == Some(&b'v') {
        i += 1;
    }

    while matches!(
        bytes.get(i),
        Some(b' ' | b'\t' | b'\n' | b'\r' | 0x0B | 0x0C)
    ) {
        i += 1;
    }

    let (major, next) = parse_component(bytes, i)?;
    i = next;

    let mut minor = None;
    let mut patch = None;
    let mut pre_release = Identifiers::Empty;

    if bytes.get(i) == Some(&b'.') {
        let (parsed_minor, next) = parse_component(bytes, i + 1)?;
        minor = parsed_minor;
        i = next;

        if bytes.get(i) == Some(&b'.') {
            let (parsed_patch, next) = parse_component(bytes, i + 1)?;
            patch = parsed_patch;
            i = next;

            if patch.is_some() {
                if bytes.get(i) == Some(&b'-') {
                    let (parsed_pre, next) = parse_identifiers(input, i + 1)?;
                    pre_release = parsed_pre;
                    i = next;
                }

                if bytes.get(i) == Some(&b'+') {
                    let (_, next) = parse_identifiers(input, i + 1)?;
                    i = next;
                }
            }
        }
    }

    Some((
        Partial {
            major,
            minor,
            patch,
            pre_release,
        },
        i,
    ))
}

fn parse_component(bytes: &[u8], start: usize) -> Option<(Option<u64>, usize)> {
    match bytes.get(start).copied()? {
        b'x' | b'X' | b'*' => Some((None, start + 1)),
        b'0'..=b'9' => parse_number(bytes, start).map(|(value, i)| (Some(value), i)),
        _ => None,
    }
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
