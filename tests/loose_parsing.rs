use nodejs_semver::{Identifier, MAX_LENGTH, MAX_SAFE_INTEGER, Range, SemverError, Version};
use serde::Deserialize;

#[derive(Deserialize)]
struct Case {
    input: String,
    version: Option<String>,
    range: Option<String>,
}

#[test]
fn preserves_loose_parsing_results() {
    // Captured from the public API before replacing the winnow fallback.
    let cases: Vec<Case> =
        serde_json::from_str(include_str!("fixtures/loose-parsing.json")).unwrap();
    for case in cases {
        assert_eq!(
            Version::parse(&case.input).ok().map(|v| v.to_string()),
            case.version,
            "version input: {:?}",
            case.input,
        );
        assert_eq!(
            Range::parse(&case.input).ok().map(|r| r.to_string()),
            case.range,
            "range input: {:?}",
            case.input,
        );
    }
}

#[test]
fn preserves_identifier_types_and_build_metadata() {
    let parts = Version::parse("1.2.3-01.18446744073709551616+0002.Ł.")
        .unwrap()
        .into_parts();
    assert_eq!((parts.major, parts.minor, parts.patch), (1, 2, 3));
    assert_eq!(
        parts.pre_release,
        [
            Identifier::Numeric(1),
            Identifier::AlphaNumeric("18446744073709551616".into()),
        ],
    );
    assert_eq!(
        parts.build,
        [Identifier::Numeric(2), Identifier::AlphaNumeric("Ł".into())],
    );
}

#[test]
fn preserves_range_bounds_and_prerelease_matching() {
    let range = Range::parse("foo >= 1.2.3-beta+build < 2.0.0").unwrap();
    for (version, expected) in [
        ("1.2.3-alpha", false),
        ("1.2.3-beta", true),
        ("1.2.3", true),
        ("1.2.4-beta", false),
        ("1.9.0", true),
        ("2.0.0", false),
    ] {
        assert_eq!(range.satisfies(&Version::parse(version).unwrap()), expected);
    }
    assert!(range.satisfies_with_prerelease(&Version::parse("1.2.4-beta").unwrap(), true));
}

#[test]
fn preserves_numeric_and_length_limits() {
    for component in 0..3 {
        for value in [MAX_SAFE_INTEGER + 1, u64::MAX] {
            let mut parts = ["1".to_owned(), "2".to_owned(), "3".to_owned()];
            parts[component] = value.to_string();
            assert!(Version::parse(parts.join(".")).is_err());
        }
    }
    let version = format!("1.2.3-{}", "a".repeat(MAX_LENGTH - 6));
    assert!(Version::parse(&version).is_ok());
    assert!(Version::parse(format!("{version}a")).is_err());
}

#[test]
fn parse_errors_support_standard_error_handling() {
    fn parse(input: &str) -> Result<Version, Box<dyn std::error::Error>> {
        Ok(input.parse()?)
    }
    let error = parse("not a version").unwrap_err();
    assert!(error.downcast_ref::<SemverError>().is_some());
    assert!(!error.to_string().is_empty());
    assert!("not a range".parse::<Range>().is_err());
}

#[test]
fn compound_ranges_keep_loose_only_tokens() {
    for (input, expected) in [
        ("^1.0.0 v1.2.3", "1.2.3"),
        (">=1.0.0 v1.2.3", "1.2.3"),
        ("^1.0.0 1.2.3beta", "1.2.3-beta"),
        ("foo ~1.x.3", ">=1.0.0 <2.0.0-0"),
    ] {
        assert_eq!(
            Range::parse(input).unwrap().to_string(),
            expected,
            "{input:?}"
        );
    }
}

#[test]
fn javascript_whitespace_is_handled_consistently() {
    for input in [
        "<v 1",
        "- 2.3.4",
        "1.2.3 foo",
        ">=1.2.3 <2.0.0",
        "~> 1.2",
        "1 - 2",
        "^1 || ^2",
    ] {
        let expected = Range::parse(input).unwrap();
        for padded in [
            format!(" {input}\n"),
            format!("\u{3000}{input}\u{A0}"),
            format!("\u{FEFF}{input}\t"),
        ] {
            assert_eq!(Range::parse(&padded).unwrap(), expected, "{padded:?}");
        }
    }

    for ws in [
        "\t", "\n", "\r", "\u{0B}", "\u{0C}", "\u{A0}", "\u{2003}", "\u{3000}", "\u{FEFF}",
    ] {
        let range = |input: String| Range::parse(&input).map(|r| r.to_string());
        assert_eq!(
            range(format!(">=1.2.3{ws}<2.0.0")).unwrap(),
            ">=1.2.3 <2.0.0"
        );
        assert_eq!(
            range(format!("1.2.3{ws}||{ws}2.0.0")).unwrap(),
            "1.2.3||2.0.0"
        );
        assert_eq!(range(format!("foo{ws}1.2.3-beta")).unwrap(), "1.2.3-beta");
        for version in [
            format!("{ws}1.2.3"),
            format!("v{ws}1.2.3"),
            format!("1.2.3{ws}x"),
        ] {
            assert_eq!(Version::parse(&version).unwrap().to_string(), "1.2.3");
        }
    }
}

#[test]
fn near_or_separator_does_not_recurse() {
    for input in ["^|}", "~|}", ">|}", "1|}", "*|}"] {
        assert!(Range::parse(input).is_err());
    }
}
