use super::{Bound, BoundSet, Operation, Predicate, Range};
use crate::scan::{self, identifiers, number, skip_whitespace};
use crate::{Identifiers, MAX_SAFE_INTEGER, Version};

pub(super) fn parse(input: &str) -> Option<Range> {
    let bytes = input.as_bytes();
    let first = bytes.first().copied();

    if first == Some(b'^') {
        return parse_caret(input).or_else(|| parse_or_if_present(input));
    }

    if first == Some(b'~') {
        return parse_tilde(input).or_else(|| parse_or_if_present(input));
    }

    if matches!(first, Some(b'>' | b'<' | b'=')) {
        return parse_comparator_set(input).or_else(|| parse_or_if_present(input));
    }

    if let Some(range) = parse_exact_version(bytes)
        .and_then(|version| BoundSet::exact(version).map(Range::from_bound_set))
    {
        return Some(range);
    }

    if matches!(first, Some(b'x' | b'X' | b'*')) {
        return parse_partial_wildcard(input).or_else(|| parse_or_if_present(input));
    }

    if matches!(first, Some(b'v' | b'V' | b'0'..=b'9')) {
        if bytes.contains(&b'-') {
            if let Some(range) = parse_hyphen(input) {
                return Some(range);
            }
        }

        return parse_partial_wildcard(input).or_else(|| parse_or_if_present(input));
    }

    None
}

fn parse_or_if_present(input: &str) -> Option<Range> {
    (input.as_bytes().contains(&b'|') && input.contains("||"))
        .then(|| parse_or(input))
        .flatten()
}

fn parse_or(input: &str) -> Option<Range> {
    let mut sets = Vec::new();

    for part in input.split("||") {
        let part = scan::trim(part);
        if part.is_empty() {
            return None;
        }

        parse(part)?.append_bound_sets_to(&mut sets);
    }

    Range::from_bound_sets(sets)
}

fn parse_hyphen(input: &str) -> Option<Range> {
    let bytes = input.as_bytes();
    let (lower, i) = parse_partial_without_build(input, 0)?;
    let i = skip_whitespace1(input, i)?;
    if bytes.get(i) != Some(&b'-') {
        return None;
    }
    let i = skip_whitespace1(input, i + 1)?;

    let (upper, i) = parse_partial_without_build(input, i)?;
    if i != bytes.len() {
        return None;
    }

    BoundSet::new(
        Bound::Lower(Predicate::Including(partial_to_version(lower))),
        Bound::Upper(hyphen_upper(upper)),
    )
    .map(Range::from_bound_set)
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
    let bytes = input.as_bytes();
    let mut i = 0;
    let mut current: Option<BoundSet> = None;

    loop {
        let (bound_set, next) = parse_comparator(input, i)?;
        let set = match current {
            Some(current) => current.intersect(&bound_set)?,
            None => bound_set,
        };

        if next == bytes.len() {
            return Some(Range::from_bound_set(set));
        }

        i = skip_whitespace(input, next);
        // Keep the comparators parsed so far instead of re-parsing them in `parse_or`.
        if bytes[i..].starts_with(b"||") {
            let mut sets = vec![set];
            parse_or(&input[i + 2..])?.append_bound_sets_to(&mut sets);
            return Range::from_bound_sets(sets);
        }
        if i == next || i == bytes.len() {
            return None;
        }
        current = Some(set);
    }
}

fn parse_comparator(input: &str, start: usize) -> Option<(BoundSet, usize)> {
    let (operation, i) = parse_operation(input.as_bytes(), start)?;
    let i = skip_whitespace(input, i);
    let (partial, i) = parse_partial_without_build(input, i)?;
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
                ..
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
    let i = skip_whitespace(input, 1);
    let (partial, i) = parse_partial_loose(input, i)?;
    if i != input.len() {
        return None;
    }

    caret_range(partial).map(Range::from_bound_set)
}

fn parse_tilde(input: &str) -> Option<Range> {
    let mut i = skip_whitespace(input, 1);
    if input.as_bytes().get(i) == Some(&b'>') {
        i = skip_whitespace(input, i + 1);
    }

    let (partial, i) = parse_partial_loose(input, i)?;
    if i != input.len() {
        return None;
    }

    tilde_range(partial).map(Range::from_bound_set)
}

fn parse_partial_wildcard(input: &str) -> Option<Range> {
    let (partial, i) = parse_partial(input, 0)?;
    if i != input.len() {
        return None;
    }

    partial_wildcard_range(partial).map(Range::from_bound_set)
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

fn tilde_range(partial: Partial) -> Option<BoundSet> {
    match partial {
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
            patch,
            pre_release,
            ..
        } => BoundSet::new(
            Bound::Lower(Predicate::Including(Version::new_with_identifiers(
                major,
                minor,
                patch.unwrap_or(0),
                pre_release,
                Identifiers::Empty,
            ))),
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
            ..
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
    let (major, mut i) = number(bytes, 0)?;
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

    let (patch, i) = number(bytes, i)?;
    if i != bytes.len() {
        return None;
    }

    Some(Version::from((major, minor, patch)))
}

fn skip_whitespace1(input: &str, start: usize) -> Option<usize> {
    let i = skip_whitespace(input, start);
    (i > start).then_some(i)
}

#[derive(Debug)]
struct Partial {
    major: Option<u64>,
    minor: Option<u64>,
    patch: Option<u64>,
    pre_release: Identifiers,
    has_build: bool,
}

fn parse_partial(input: &str, start: usize) -> Option<(Partial, usize)> {
    parse_partial_inner(input, start, false)
}

fn parse_partial_loose(input: &str, start: usize) -> Option<(Partial, usize)> {
    parse_partial_inner(input, start, true)
}

// Comparators and hyphen bounds keep build metadata, which only the loose
// parser does, so leave such inputs to it.
fn parse_partial_without_build(input: &str, start: usize) -> Option<(Partial, usize)> {
    parse_partial_loose(input, start).filter(|(partial, _)| !partial.has_build)
}

fn parse_partial_inner(
    input: &str,
    start: usize,
    allow_loose_suffix: bool,
) -> Option<(Partial, usize)> {
    let bytes = input.as_bytes();
    let mut i = start;

    if bytes.get(i) == Some(&b'v') {
        i += 1;
    }
    i = skip_whitespace(input, i);

    let (major, next) = parse_component(bytes, i)?;
    i = next;

    let mut minor = None;
    let mut patch = None;
    let mut pre_release = Identifiers::Empty;
    let mut has_build = false;

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
                    let (parsed_pre, next) = identifiers(input, i + 1)?;
                    pre_release = parsed_pre;
                    i = next;
                } else if allow_loose_suffix
                    && bytes.get(i).is_some_and(|ch| ch.is_ascii_alphanumeric())
                {
                    let (parsed_pre, next) = identifiers(input, i)?;
                    pre_release = parsed_pre;
                    i = next;
                }

                if bytes.get(i) == Some(&b'+') {
                    let (_, next) = identifiers(input, i + 1)?;
                    i = next;
                    has_build = true;
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
            has_build,
        },
        i,
    ))
}

fn parse_component(bytes: &[u8], start: usize) -> Option<(Option<u64>, usize)> {
    match bytes.get(start).copied()? {
        b'x' | b'X' | b'*' => Some((None, start + 1)),
        b'0'..=b'9' => number(bytes, start).map(|(value, i)| (Some(value), i)),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_tilde_ranges() {
        let cases = [
            ("~1", ">=1.0.0 <2.0.0-0"),
            ("~1.2", ">=1.2.0 <1.3.0-0"),
            ("~1.2.3", ">=1.2.3 <1.3.0-0"),
            ("~1.2.3-beta", ">=1.2.3-beta <1.3.0-0"),
            ("~>3.2.1", ">=3.2.1 <3.3.0-0"),
            ("~> 1", ">=1.0.0 <2.0.0-0"),
            ("~ > 1.2.3", ">=1.2.3 <1.3.0-0"),
        ];

        for (input, expected) in cases {
            assert_eq!(parse(input).unwrap().to_string(), expected);
        }
    }

    #[test]
    fn parses_loose_prerelease_suffixes() {
        let cases = [
            ("~1.2.3beta", ">=1.2.3-beta <1.3.0-0"),
            ("^1.0.0alpha", ">=1.0.0-alpha <2.0.0-0"),
        ];

        for (input, expected) in cases {
            assert_eq!(parse(input).unwrap().to_string(), expected);
        }

        assert!(parse("1.2.3beta").is_none());
    }
}
