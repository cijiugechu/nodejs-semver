//! Loose range parsing for inputs outside the optimized paths.

/*
Grammar from https://github.com/npm/node-semver#range-grammar

range-set  ::= range ( logical-or range ) *
logical-or ::= ( ' ' ) * '||' ( ' ' ) *
range      ::= hyphen | simple ( ' ' simple ) * | ''
hyphen     ::= partial ' - ' partial
simple     ::= primitive | partial | tilde | caret
primitive  ::= ( '<' | '>' | '>=' | '<=' | '=' ) partial
partial    ::= xr ( '.' xr ( '.' xr qualifier ? )? )?
xr         ::= 'x' | 'X' | '*' | nr
nr         ::= '0' | ['1'-'9'] ( ['0'-'9'] ) *
tilde      ::= '~' partial
caret      ::= '^' partial
qualifier  ::= ( '-' pre )? ( '+' build )?
pre        ::= parts
build      ::= parts
parts      ::= part ( '.' part ) *
part       ::= nr | [-0-9A-Za-z]+


Loose mode (all LHS are invalid in strict mode):
* 01.02.03 -> 1.2.3
* 1.2.3alpha -> 1.2.3-alpha
* v 1.2.3 -> 1.2.3 (v1.2.3 is actually a valid "plain" version)
* =1.2.3 -> 1.2.3 (already a valid range)
* - 10 -> >=10.0.0 <11.0.0
* 1.2.3 foo 4.5.6 -> 1.2.3 4.5.6
* 1.2.3.4 -> invalid range
* foo -> invalid range
* 1.2beta4 -> invalid range

*/

use smallvec::SmallVec;

use super::{Bound, BoundSet, Operation, Predicate, Range};
use crate::{Identifier, MAX_SAFE_INTEGER, Version, parse::Cursor, scan};

// Expects input without leading whitespace, so every `simple` starts on a token.
pub(super) fn parse(input: &str) -> Option<Range> {
    let mut cursor = Cursor::new(input);
    let mut sets = SmallVec::new();
    loop {
        let mut current: Option<BoundSet> = None;
        loop {
            if let Some(bound) = simple(&mut cursor) {
                current = Some(match current {
                    Some(last) => last.intersect(&bound).unwrap_or_else(|| {
                        // Preserve loose parsing's treatment of disjoint bounds.
                        sets.push(last);
                        bound
                    }),
                    None => bound,
                });
            }
            if !cursor.spaces() {
                break;
            }
        }
        sets.extend(current);
        if !cursor.eat("||") {
            break;
        }
        cursor.spaces();
    }
    (!sets.is_empty()).then(|| Range(sets))
}

fn boundary(input: &str) -> bool {
    input.is_empty() || scan::whitespace_len(input, 0) > 0 || input.starts_with("||")
}

fn simple(cursor: &mut Cursor<'_>) -> Option<BoundSet> {
    // A recognized expression can yield no bounds; that is distinct from a
    // failed parse, which must rewind before trying the next grammar branch.
    if let Some((bound, rest)) = hyphen_or_plain(*cursor) {
        *cursor = rest;
        return bound;
    }
    for parser in [primitive, tilde, caret] {
        let mut candidate = *cursor;
        if let Some(bound) = parser(&mut candidate) {
            if boundary(candidate.remaining) {
                *cursor = candidate;
                return bound;
            }
        }
    }
    // Ignore malformed tokens, stopping before a conjunction or OR separator.
    while !boundary(cursor.remaining) {
        let len = cursor.remaining.chars().next().unwrap().len_utf8();
        cursor.remaining = &cursor.remaining[len..];
    }
    None
}

fn primitive(cursor: &mut Cursor<'_>) -> Option<Option<BoundSet>> {
    use Operation::*;
    let operation = if cursor.eat(">=") {
        GreaterThanEquals
    } else if cursor.eat(">") {
        GreaterThan
    } else if cursor.eat("=") {
        Exact
    } else if cursor.eat("<=") {
        LessThanEquals
    } else if cursor.eat("<") {
        LessThan
    } else {
        return None;
    };
    cursor.spaces();
    let parsed = (operation, token_partial(cursor)?);
    Some(match parsed {
        (GreaterThanEquals, partial) => BoundSet::at_least(Predicate::Including(partial.into())),
        (
            GreaterThan,
            Partial {
                major: Some(major),
                minor: Some(minor),
                patch: None,
                ..
            },
        ) => BoundSet::at_least(Predicate::Including((major, minor + 1, 0).into())),
        (
            GreaterThan,
            Partial {
                major: Some(major),
                minor: None,
                patch: None,
                ..
            },
        ) => BoundSet::at_least(Predicate::Including((major + 1, 0, 0).into())),
        (GreaterThan, partial) => BoundSet::at_least(Predicate::Excluding(partial.into())),
        (
            LessThan,
            Partial {
                major: Some(major),
                minor: Some(minor),
                patch: None,
                ..
            },
        ) => BoundSet::at_most(Predicate::Excluding((major, minor, 0, 0).into())),
        (
            LessThan,
            Partial {
                major,
                minor,
                patch,
                pre_release,
                build,
                ..
            },
        ) => BoundSet::at_most(Predicate::Excluding(Version::new(
            major.unwrap_or(0),
            minor.unwrap_or(0),
            patch.unwrap_or(0),
            pre_release,
            build,
        ))),
        (
            LessThanEquals,
            Partial {
                major,
                minor: None,
                patch: None,
                ..
            },
        ) => BoundSet::at_most(Predicate::Including(
            (major.unwrap_or(0), MAX_SAFE_INTEGER, MAX_SAFE_INTEGER).into(),
        )),
        (
            LessThanEquals,
            Partial {
                major,
                minor,
                patch: None,
                ..
            },
        ) => BoundSet::at_most(Predicate::Including(
            (major.unwrap_or(0), minor.unwrap_or(0), MAX_SAFE_INTEGER).into(),
        )),
        (LessThanEquals, partial) => BoundSet::at_most(Predicate::Including(partial.into())),
        (
            Exact,
            Partial {
                major: Some(major),
                minor: Some(minor),
                patch: Some(patch),
                pre_release,
                ..
            },
        ) => BoundSet::exact(Version::new(major, minor, patch, pre_release, vec![])),
        (
            Exact,
            Partial {
                major: Some(major),
                minor: Some(minor),
                ..
            },
        ) => BoundSet::new(
            Bound::Lower(Predicate::Including((major, minor, 0).into())),
            Bound::Upper(Predicate::Excluding((major, minor + 1, 0, 0).into())),
        ),
        (
            Exact,
            Partial {
                major: Some(major), ..
            },
        ) => BoundSet::new(
            Bound::Lower(Predicate::Including((major, 0, 0).into())),
            Bound::Upper(Predicate::Excluding((major + 1, 0, 0, 0).into())),
        ),
        _ => None,
    })
}

// `hyphen` and `plain` both start with a partial version: parse it once and
// prefer the hyphen form, as the grammar order requires.
fn hyphen_or_plain(cursor: Cursor<'_>) -> Option<(Option<BoundSet>, Cursor<'_>)> {
    let mut after_lower = cursor;
    let lower = partial_version(&mut after_lower)?;
    let mut rest = after_lower;
    match hyphen_upper(&mut rest).filter(|_| boundary(rest.remaining)) {
        Some(upper) => Some((
            BoundSet::new(
                Bound::Lower(Predicate::Including(lower.into())),
                Bound::Upper(upper),
            ),
            rest,
        )),
        None => boundary(after_lower.remaining).then(|| (plain(lower), after_lower)),
    }
}

fn plain(partial: Partial) -> Option<BoundSet> {
    match partial {
        Partial { major: None, .. } => BoundSet::at_least(Predicate::Including((0, 0, 0).into())),
        Partial {
            major: Some(major),
            minor: None,
            ..
        } => BoundSet::new(
            Bound::Lower(Predicate::Including((major, 0, 0).into())),
            Bound::Upper(Predicate::Excluding((major + 1, 0, 0, 0).into())),
        ),
        Partial {
            major: Some(major),
            minor: Some(minor),
            patch: None,
            ..
        } => BoundSet::new(
            Bound::Lower(Predicate::Including((major, minor, 0).into())),
            Bound::Upper(Predicate::Excluding((major, minor + 1, 0, 0).into())),
        ),
        partial => BoundSet::exact(partial.into()),
    }
}

#[derive(Debug, Clone)]
struct Partial {
    major: Option<u64>,
    minor: Option<u64>,
    patch: Option<u64>,
    pre_release: Vec<Identifier>,
    build: Vec<Identifier>,
}

impl From<Partial> for Version {
    fn from(partial: Partial) -> Self {
        Version::new(
            partial.major.unwrap_or(0),
            partial.minor.unwrap_or(0),
            partial.patch.unwrap_or(0),
            partial.pre_release,
            partial.build,
        )
    }
}

fn partial_version(cursor: &mut Cursor<'_>) -> Option<Partial> {
    cursor.eat("v");
    cursor.spaces();
    let major = component(cursor)?;
    let minor = dotted_component(cursor);
    let patch = dotted_component(cursor);
    let (pre_release, build) = if patch.is_some() {
        cursor.extras()
    } else {
        (Vec::new(), Vec::new())
    };
    Some(Partial {
        major,
        minor: minor.flatten(),
        patch: patch.flatten(),
        pre_release,
        build,
    })
}

// A partial that must end its token. Checking the boundary before building
// bounds avoids constructing a candidate that `simple` would reject anyway.
fn token_partial(cursor: &mut Cursor<'_>) -> Option<Partial> {
    let partial = partial_version(cursor)?;
    boundary(cursor.remaining).then_some(partial)
}

fn dotted_component(cursor: &mut Cursor<'_>) -> Option<Option<u64>> {
    let mut next = *cursor;
    if !next.eat(".") {
        return None;
    }
    let component = component(&mut next)?;
    *cursor = next;
    Some(component)
}

fn component(cursor: &mut Cursor<'_>) -> Option<Option<u64>> {
    if cursor.eat("x") || cursor.eat("X") || cursor.eat("*") {
        Some(None)
    } else {
        cursor.number().map(Some)
    }
}

fn tilde(cursor: &mut Cursor<'_>) -> Option<Option<BoundSet>> {
    if !cursor.eat("~") {
        return None;
    }
    cursor.spaces();
    let gt = cursor.eat(">").then_some(());
    cursor.spaces();
    let parsed = (gt, token_partial(cursor)?);
    // As in the fast parser, a wildcard minor ignores the patch.
    Some(match parsed {
        (
            Some(_gt),
            Partial {
                major: Some(major),
                minor: None,
                ..
            },
        ) => BoundSet::new(
            Bound::Lower(Predicate::Including((major, 0, 0).into())),
            Bound::Upper(Predicate::Excluding((major + 1, 0, 0, 0).into())),
        ),
        (
            Some(_gt),
            Partial {
                major: Some(major),
                minor: Some(minor),
                patch,
                pre_release,
                ..
            },
        ) => BoundSet::new(
            Bound::Lower(Predicate::Including(Version::new(
                major,
                minor,
                patch.unwrap_or(0),
                pre_release,
                vec![],
            ))),
            Bound::Upper(Predicate::Excluding((major, minor + 1, 0, 0).into())),
        ),
        (
            None,
            Partial {
                major: Some(major),
                minor: Some(minor),
                patch: Some(patch),
                pre_release,
                ..
            },
        ) => BoundSet::new(
            Bound::Lower(Predicate::Including(Version::new(
                major,
                minor,
                patch,
                pre_release,
                vec![],
            ))),
            Bound::Upper(Predicate::Excluding((major, minor + 1, 0, 0).into())),
        ),
        (
            None,
            Partial {
                major: Some(major),
                minor: Some(minor),
                patch: None,
                ..
            },
        ) => BoundSet::new(
            Bound::Lower(Predicate::Including((major, minor, 0).into())),
            Bound::Upper(Predicate::Excluding((major, minor + 1, 0, 0).into())),
        ),
        (
            None,
            Partial {
                major: Some(major),
                minor: None,
                ..
            },
        ) => BoundSet::new(
            Bound::Lower(Predicate::Including((major, 0, 0).into())),
            Bound::Upper(Predicate::Excluding((major + 1, 0, 0, 0).into())),
        ),
        _ => None,
    })
}

fn caret(cursor: &mut Cursor<'_>) -> Option<Option<BoundSet>> {
    if !cursor.eat("^") {
        return None;
    }
    cursor.spaces();
    let parsed = token_partial(cursor)?;
    Some(match parsed {
        Partial {
            major: Some(0),
            minor: None,
            patch: None,
            ..
        } => BoundSet::at_most(Predicate::Excluding((1, 0, 0, 0).into())),
        Partial {
            major: Some(0),
            minor: Some(minor),
            patch: None,
            ..
        } => BoundSet::new(
            Bound::Lower(Predicate::Including((0, minor, 0).into())),
            Bound::Upper(Predicate::Excluding((0, minor + 1, 0, 0).into())),
        ),
        Partial {
            major: Some(major),
            minor: None,
            patch: None,
            ..
        } => BoundSet::new(
            Bound::Lower(Predicate::Including((major, 0, 0).into())),
            Bound::Upper(Predicate::Excluding((major + 1, 0, 0, 0).into())),
        ),
        Partial {
            major: Some(major),
            minor: Some(minor),
            patch: None,
            ..
        } => BoundSet::new(
            Bound::Lower(Predicate::Including((major, minor, 0).into())),
            Bound::Upper(Predicate::Excluding((major + 1, 0, 0, 0).into())),
        ),
        Partial {
            major: Some(major),
            minor: Some(minor),
            patch: Some(patch),
            pre_release,
            ..
        } => BoundSet::new(
            Bound::Lower(Predicate::Including(Version::new(
                major,
                minor,
                patch,
                pre_release,
                vec![],
            ))),
            Bound::Upper(Predicate::Excluding(match (major, minor, patch) {
                (0, 0, n) => Version::from((0, 0, n + 1, 0)),
                (0, n, _) => Version::from((0, n + 1, 0, 0)),
                (n, _, _) => Version::from((n + 1, 0, 0, 0)),
            })),
        ),
        _ => None,
    })
}

fn hyphen_upper(cursor: &mut Cursor<'_>) -> Option<Predicate> {
    if !cursor.spaces() || !cursor.eat("-") || !cursor.spaces() {
        return None;
    }
    Some(match partial_version(cursor)? {
        Partial {
            major: None,
            minor: None,
            patch: None,
            ..
        } => Predicate::Excluding((0, 0, 0, 0).into()),
        Partial {
            major: Some(major),
            minor: None,
            patch: None,
            ..
        } => Predicate::Excluding((major + 1, 0, 0, 0).into()),
        Partial {
            major: Some(major),
            minor: Some(minor),
            patch: None,
            ..
        } => Predicate::Excluding((major, minor + 1, 0, 0).into()),
        partial => Predicate::Including(partial.into()),
    })
}
