#![doc = include_str!("../README.md")]

#[cfg(feature = "serde")]
use serde::{de::Deserializer, ser::Serializer, Deserialize, Serialize};

use std::cmp::{self, Ordering};
use std::fmt;
use std::num::ParseIntError;

use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

use winnow::ascii::{digit1, space0};
use winnow::combinator::{alt, opt, preceded, separated};
use winnow::error::{AddContext, ErrMode, ErrorKind, FromExternalError, ParserError};
use winnow::stream::{AsChar, Stream};
use winnow::token::{literal, take_while};
use winnow::{PResult, Parser};

pub use range::*;

mod range;

/// JavaScript's
/// [MAX_SAFE_INTEGER](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Number/MAX_SAFE_INTEGER).
/// This is used to determine the maximum value for integer components in a
/// JS-compatible way.
pub const MAX_SAFE_INTEGER: u64 = 900_719_925_474_099;

/// Maximum length of a semver string.
pub const MAX_LENGTH: usize = 256;

/**
Semver version or range parsing error wrapper.

This wrapper is used to hold some parsing-related metadata, as well as
a more specific [SemverErrorKind].
*/
#[derive(Debug, Clone, Error, Eq, PartialEq)]
#[error("{kind}")]
pub struct SemverError {
    input: String,
    span: SourceSpan,
    kind: SemverErrorKind,
}

impl Diagnostic for SemverError {
    fn code<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        self.kind().code()
    }

    fn severity(&self) -> Option<miette::Severity> {
        self.kind().severity()
    }

    fn help<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        self.kind().help()
    }

    fn url<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        self.kind().url()
    }

    fn source_code(&self) -> Option<&dyn miette::SourceCode> {
        Some(&self.input)
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = miette::LabeledSpan> + '_>> {
        Some(Box::new(std::iter::once(
            miette::LabeledSpan::new_with_span(Some("here".into()), *self.span()),
        )))
    }
}

impl SemverError {
    /// Returns the input that was given to the parser.
    pub fn input(&self) -> &str {
        &self.input
    }

    /// Returns the SourceSpan of the error.
    pub fn span(&self) -> &SourceSpan {
        &self.span
    }

    /// Returns the (0-based) byte offset where the parsing error happened.
    pub fn offset(&self) -> usize {
        self.span.offset()
    }

    /// Returns the more specific [SemverErrorKind] for this error.
    ///
    /// This value can also be fetched through [std::error::Error::source],
    /// but that would require downcasting to match types.
    pub fn kind(&self) -> &SemverErrorKind {
        &self.kind
    }

    /// Returns the (0-indexed) line and column number where the parsing error
    /// happened.
    pub fn location(&self) -> (usize, usize) {
        // Taken partially from winnow.
        let prefix = &self.input.as_bytes()[..self.offset()];

        // Count the number of newlines in the first `offset` bytes of input
        let line_number = bytecount::count(prefix, b'\n');

        // Find the line that includes the subslice:
        // Find the *last* newline before the substring starts
        let line_begin = prefix
            .iter()
            .rev()
            .position(|&b| b == b'\n')
            .map(|pos| self.offset() - pos)
            .unwrap_or(0);

        // Find the full line after that newline
        let line = self.input[line_begin..]
            .lines()
            .next()
            .unwrap_or(&self.input[line_begin..])
            .trim_end();

        // The (0-indexed) column number is the offset of our substring into that line
        let column_number = self.input[self.offset()..].as_ptr() as usize - line.as_ptr() as usize;

        (line_number, column_number)
    }
}

/**
The specific kind of error that occurred. Usually wrapped in a [SemverError].
*/
#[derive(Debug, Clone, Error, Eq, PartialEq, Diagnostic)]
pub enum SemverErrorKind {
    /**
    Semver strings overall can't be longer than [MAX_LENGTH]. This is a
    restriction coming from the JavaScript `nodejs-semver`.
    */
    #[error("Semver string can't be longer than {} characters.", MAX_LENGTH)]
    #[diagnostic(code(nodejs_semver::too_long), url(docsrs))]
    MaxLengthError,

    /**
    Input to `nodejs-semver` must be "complete". That is, a version must be
    composed of major, minor, and patch segments, with optional prerelease
    and build metadata. If you're looking for alternative syntaxes, like `1.2`,
    that are meant for defining semver ranges, use [Range] instead.
    */
    #[error("Incomplete input to semver parser.")]
    #[diagnostic(code(nodejs_semver::incomplete_input), url(docsrs))]
    IncompleteInput,

    /**
    Components of a semver string (major, minor, patch, integer sections of
    build and prerelease) must all be valid, parseable integers. This error
    occurs when Rust's own integer parsing failed.
    */
    #[error("Failed to parse an integer component of a semver string: {0}")]
    #[diagnostic(code(nodejs_semver::parse_int_error), url(docsrs))]
    ParseIntError(ParseIntError),

    /**
    `nodejs-semver` inherits the JavaScript implementation's limitation on
    limiting integer component sizes to [MAX_SAFE_INTEGER].
    */
    #[error("Integer component of semver string is larger than JavaScript's Number.MAX_SAFE_INTEGER: {0}")]
    #[diagnostic(code(nodejs_semver::integer_too_large), url(docsrs))]
    MaxIntError(u64),

    /**
    This is a generic error that a certain component of the semver string
    failed to parse.
    */
    #[error("Failed to parse {0}.")]
    #[diagnostic(code(nodejs_semver::parse_component_error), url(docsrs))]
    Context(&'static str),

    #[error("No valid ranges could be parsed")]
    #[diagnostic(code(nodejs_semver::no_valid_ranges), url(docsrs), help("nodejs-semver parses in so-called 'loose' mode. This means that if you have a slightly incorrect semver operator (`>=1.y`, for ex.), it will get thrown away. This error only happens if _all_ your input ranges were invalid semver in this way."))]
    NoValidRanges,

    /**
    This error is mostly nondescript. Feel free to file an issue if you run
    into it.
    */
    #[error("An unspecified error occurred.")]
    #[diagnostic(code(nodejs_semver::other), url(docsrs))]
    Other,
}

#[derive(Debug)]
struct SemverParseError<I> {
    pub(crate) input: I,
    pub(crate) context: Option<&'static str>,
    pub(crate) kind: Option<SemverErrorKind>,
}

impl<I: Clone + Stream> ParserError<I> for SemverParseError<I> {
    fn from_error_kind(input: &I, _kind: winnow::error::ErrorKind) -> Self {
        Self {
            input: input.clone(),
            context: None,
            kind: None,
        }
    }

    fn append(
        self,
        input: &I,
        _token_start: &<I as Stream>::Checkpoint,
        _kind: winnow::error::ErrorKind,
    ) -> Self {
        Self {
            input: input.clone(),
            context: self.context,
            kind: self.kind,
        }
    }
}

impl<I: Stream> AddContext<I> for SemverParseError<I> {
    fn add_context(
        self,
        _input: &I,
        _token_start: &<I as Stream>::Checkpoint,
        ctx: &'static str,
    ) -> Self {
        Self {
            input: self.input,
            context: Some(ctx),
            kind: self.kind,
        }
    }
}

impl<'a> FromExternalError<&'a str, SemverParseError<&'a str>> for SemverParseError<&'a str> {
    fn from_external_error(
        _input: &&'a str,
        _kind: ErrorKind,
        e: SemverParseError<&'a str>,
    ) -> Self {
        e
    }
}

/**
An Identifier type for build and prerelease metadata.
*/
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Identifier {
    /// An identifier that's solely numbers.
    Numeric(u64),
    /// An identifier with letters and numbers.
    AlphaNumeric(String),
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Identifier::Numeric(n) => write!(f, "{}", n),
            Identifier::AlphaNumeric(s) => write!(f, "{}", s),
        }
    }
}

/// difference between two versions by the release type
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VersionDiff {
    Major,
    Minor,
    Patch,
    PreMajor,
    PreMinor,
    PrePatch,
    PreRelease,
}

/// difference between two versions
pub type ReleaseType = VersionDiff;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IdentifierBase {
    /// Mirrors `identifierBase === false` in node-semver.
    False,
    /// Any other truthy/falsy value. Only the zero/non-zero nature matters.
    Value(u64),
}

impl Default for IdentifierBase {
    fn default() -> Self {
        IdentifierBase::Value(0)
    }
}

impl IdentifierBase {
    fn base_value(self) -> u64 {
        match self {
            IdentifierBase::False => 0,
            IdentifierBase::Value(v) => {
                if v == 0 {
                    0
                } else {
                    1
                }
            }
        }
    }
}

impl From<bool> for IdentifierBase {
    fn from(value: bool) -> Self {
        if value {
            IdentifierBase::Value(1)
        } else {
            IdentifierBase::False
        }
    }
}

impl From<u64> for IdentifierBase {
    fn from(value: u64) -> Self {
        IdentifierBase::Value(value)
    }
}

impl From<usize> for IdentifierBase {
    fn from(value: usize) -> Self {
        IdentifierBase::Value(value as u64)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum IncrementError {
    #[error("invalid identifier: {0}")]
    InvalidIdentifier(String),
    #[error("invalid increment argument: {0}")]
    InvalidIncrementArgument(String),
    #[error("version {0} is not a prerelease")]
    NotAPrerelease(String),
    #[error("increment would overflow a version component")]
    Overflow,
}

impl fmt::Display for VersionDiff {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VersionDiff::Major => write!(f, "major"),
            VersionDiff::Minor => write!(f, "minor"),
            VersionDiff::Patch => write!(f, "patch"),
            VersionDiff::PreMajor => write!(f, "premajor"),
            VersionDiff::PreMinor => write!(f, "preminor"),
            VersionDiff::PrePatch => write!(f, "prepatch"),
            VersionDiff::PreRelease => write!(f, "prerelease"),
        }
    }
}

/**
A semantic version, conformant to the [semver spec](https://semver.org/spec/v2.0.0.html).
*/
#[derive(Clone, Debug)]
pub struct Version {
    pub major: u64,
    pub minor: u64,
    pub patch: u64,
    pub build: Vec<Identifier>,
    pub pre_release: Vec<Identifier>,
}

#[cfg(feature = "serde")]
impl Serialize for Version {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.collect_str(self)
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for Version {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let s = String::deserialize(d)?;
        s.parse().map_err(serde::de::Error::custom)
    }
}

impl Version {
    /// True if this [Version] satisfies the given [Range].
    pub fn satisfies(&self, range: &Range) -> bool {
        range.satisfies(self)
    }

    /// True if this [Version] satisfies the given [Range], treating prerelease
    /// versions as valid matches even when the range does not explicitly
    /// mention one.
    pub fn satisfies_with_prerelease(&self, range: &Range, include_prerelease: bool) -> bool {
        range.satisfies_with_prerelease(self, include_prerelease)
    }

    /// True is this [Version] has a prerelease component.
    pub fn is_prerelease(&self) -> bool {
        !self.pre_release.is_empty()
    }

    /// Increment this [Version] according to the given release type, returning a new [Version].
    ///
    /// Mirrors the behavior of the `SemVer.inc` method in node-semver.
    pub fn inc(
        &self,
        release: &str,
        identifier: Option<&str>,
        identifier_base: Option<IdentifierBase>,
    ) -> Result<Version, IncrementError> {
        let mut cloned = self.clone();
        cloned.inc_mut(release, identifier, identifier_base)?;
        Ok(cloned)
    }

    fn inc_mut(
        &mut self,
        release: &str,
        identifier: Option<&str>,
        identifier_base: Option<IdentifierBase>,
    ) -> Result<&mut Self, IncrementError> {
        let identifier_base = identifier_base.unwrap_or_default();
        let identifier_base_is_false = identifier_base == IdentifierBase::False;
        let identifier = identifier.and_then(|id| {
            if id.is_empty() {
                None
            } else {
                Some(id.to_string())
            }
        });

        if release.starts_with("pre") {
            if identifier.is_none() && identifier_base_is_false {
                return Err(IncrementError::InvalidIncrementArgument(
                    "identifier is empty".into(),
                ));
            }
            if let Some(id) = identifier.as_deref() {
                if !is_valid_prerelease_identifier(id) {
                    return Err(IncrementError::InvalidIdentifier(id.to_string()));
                }
            }
        }

        match release {
            "premajor" => {
                self.pre_release.clear();
                self.patch = 0;
                self.minor = 0;
                self.major = self.major.checked_add(1).ok_or(IncrementError::Overflow)?;
                self.inc_mut("pre", identifier.as_deref(), Some(identifier_base))?;
            }
            "preminor" => {
                self.pre_release.clear();
                self.patch = 0;
                self.minor = self.minor.checked_add(1).ok_or(IncrementError::Overflow)?;
                self.inc_mut("pre", identifier.as_deref(), Some(identifier_base))?;
            }
            "prepatch" => {
                self.pre_release.clear();
                self.inc_mut("patch", identifier.as_deref(), Some(identifier_base))?;
                self.inc_mut("pre", identifier.as_deref(), Some(identifier_base))?;
            }
            "prerelease" => {
                if self.pre_release.is_empty() {
                    self.inc_mut("patch", identifier.as_deref(), Some(identifier_base))?;
                }
                self.inc_mut("pre", identifier.as_deref(), Some(identifier_base))?;
            }
            "release" => {
                if self.pre_release.is_empty() {
                    return Err(IncrementError::NotAPrerelease(self.to_string()));
                }
                self.pre_release.clear();
            }
            "major" => {
                if self.minor != 0 || self.patch != 0 || self.pre_release.is_empty() {
                    self.major = self.major.checked_add(1).ok_or(IncrementError::Overflow)?;
                }
                self.minor = 0;
                self.patch = 0;
                self.pre_release.clear();
            }
            "minor" => {
                if self.patch != 0 || self.pre_release.is_empty() {
                    self.minor = self.minor.checked_add(1).ok_or(IncrementError::Overflow)?;
                }
                self.patch = 0;
                self.pre_release.clear();
            }
            "patch" => {
                if self.pre_release.is_empty() {
                    self.patch = self.patch.checked_add(1).ok_or(IncrementError::Overflow)?;
                }
                self.pre_release.clear();
            }
            "pre" => {
                self.apply_pre_increment(identifier.as_deref(), identifier_base)?;
            }
            _ => {
                return Err(IncrementError::InvalidIncrementArgument(
                    release.to_string(),
                ));
            }
        }

        Ok(self)
    }

    fn apply_pre_increment(
        &mut self,
        identifier: Option<&str>,
        identifier_base: IdentifierBase,
    ) -> Result<(), IncrementError> {
        let base = identifier_base.base_value();
        let identifier_base_is_false = identifier_base == IdentifierBase::False;
        let identifier = identifier.map(|id| id.to_string());

        if self.pre_release.is_empty() {
            self.pre_release.push(Identifier::Numeric(base));
        } else {
            let mut incremented = false;
            for ident in self.pre_release.iter_mut().rev() {
                if let Identifier::Numeric(num) = ident {
                    *num = num.checked_add(1).ok_or(IncrementError::Overflow)?;
                    incremented = true;
                    break;
                }
            }

            if !incremented {
                if identifier_base_is_false {
                    if let Some(id) = identifier.as_deref() {
                        if id == join_prerelease_components(&self.pre_release) {
                            return Err(IncrementError::InvalidIncrementArgument(
                                "identifier already exists".into(),
                            ));
                        }
                    }
                }
                self.pre_release.push(Identifier::Numeric(base));
            }
        }

        if let Some(id) = identifier {
            let prerelease = if identifier_base_is_false {
                vec![Identifier::AlphaNumeric(id.clone())]
            } else {
                vec![
                    Identifier::AlphaNumeric(id.clone()),
                    Identifier::Numeric(base),
                ]
            };

            if let Some(first) = self.pre_release.get(0) {
                if compare_identifier_and_str(first, &id) == Ordering::Equal {
                    if !matches!(self.pre_release.get(1), Some(Identifier::Numeric(_))) {
                        self.pre_release = prerelease;
                    }
                } else {
                    self.pre_release = prerelease;
                }
            } else {
                self.pre_release = prerelease;
            }
        }

        Ok(())
    }

    /// Parse a semver string into a [Version].
    ///
    /// ```rust
    #[doc = include_str!("../examples/parse.rs")]
    /// ```
    pub fn parse<S: AsRef<str>>(input: S) -> Result<Version, SemverError> {
        let mut input = input.as_ref();

        if input.len() > MAX_LENGTH {
            return Err(SemverError {
                input: input.into(),
                span: (input.len() - 1, 0).into(),
                kind: SemverErrorKind::MaxLengthError,
            });
        }

        match version.parse_next(&mut input) {
            Ok(arg) => Ok(arg),
            Err(err) => Err(match err {
                ErrMode::Backtrack(e) | ErrMode::Cut(e) => SemverError {
                    input: input.into(),
                    span: (e.input.as_ptr() as usize - input.as_ptr() as usize, 0).into(),
                    kind: if let Some(kind) = e.kind {
                        kind
                    } else if let Some(ctx) = e.context {
                        SemverErrorKind::Context(ctx)
                    } else {
                        SemverErrorKind::Other
                    },
                },
                ErrMode::Incomplete(_) => SemverError {
                    input: input.into(),
                    span: (input.len() - 1, 0).into(),
                    kind: SemverErrorKind::IncompleteInput,
                },
            }),
        }
    }

    /// difference between two [Version]s by the release type,
    /// or `None` if the [Version]s are the same.
    ///
    /// ```rust
    #[doc = include_str!("../examples/diff.rs")]
    /// ```
    pub fn diff(&self, other: &Self) -> Option<VersionDiff> {
        let cmp_result = self.cmp(other);

        if cmp_result == Ordering::Equal {
            return None;
        }

        let self_higher = cmp_result == Ordering::Greater;
        let high_version = if self_higher { self } else { other };
        let low_version = if self_higher { other } else { self };
        let high_has_pre = high_version.is_prerelease();
        let low_has_pre = low_version.is_prerelease();

        if low_has_pre && !high_has_pre {
            // Going from prerelease -> no prerelease requires some special casing

            // If the low version has only a major, then it will always be a major
            // Some examples:
            // 1.0.0-1 -> 1.0.0
            // 1.0.0-1 -> 1.1.1
            // 1.0.0-1 -> 2.0.0
            if low_version.patch == 0 && low_version.minor == 0 {
                return Some(VersionDiff::Major);
            }

            // Otherwise it can be determined by checking the high version
            if high_version.patch != 0 {
                // anything higher than a patch bump would result in the wrong version
                return Some(VersionDiff::Patch);
            }

            if high_version.minor != 0 {
                // anything higher than a minor bump would result in the wrong version
                return Some(VersionDiff::Minor);
            }

            // bumping major/minor/patch all have same result
            return Some(VersionDiff::Major);
        }

        if self.major != other.major {
            if high_has_pre {
                return Some(VersionDiff::PreMajor);
            }

            return Some(VersionDiff::Major);
        }

        if self.minor != other.minor {
            if high_has_pre {
                return Some(VersionDiff::PreMinor);
            }

            return Some(VersionDiff::Minor);
        }

        if self.patch != other.patch {
            if high_has_pre {
                return Some(VersionDiff::PrePatch);
            }

            return Some(VersionDiff::Patch);
        }

        // high and low are preleases
        Some(VersionDiff::PreRelease)
    }
}

impl PartialEq for Version {
    fn eq(&self, other: &Self) -> bool {
        self.major == other.major
            && self.minor == other.minor
            && self.patch == other.patch
            && self.pre_release == other.pre_release
    }
}

impl Eq for Version {}

impl std::hash::Hash for Version {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.major.hash(state);
        self.minor.hash(state);
        self.patch.hash(state);
        self.pre_release.hash(state);
    }
}

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)?;

        for (i, ident) in self.pre_release.iter().enumerate() {
            if i == 0 {
                write!(f, "-")?;
            } else {
                write!(f, ".")?;
            }
            write!(f, "{}", ident)?;
        }

        for (i, ident) in self.build.iter().enumerate() {
            if i == 0 {
                write!(f, "+")?;
            } else {
                write!(f, ".")?;
            }
            write!(f, "{}", ident)?;
        }

        Ok(())
    }
}

macro_rules! impl_from_unsigned_for_version {
    ($($t:ident),+) => {
        $(
            impl ::std::convert::From<($t, $t, $t)> for Version {
                fn from((major, minor, patch): ($t, $t, $t)) -> Self {
                    Version {
                        major: major as u64,
                        minor: minor as u64,
                        patch: patch as u64,
                        build: Vec::new(),
                        pre_release: Vec::new(),
                    }
                }
            }

            impl ::std::convert::From<($t, $t, $t, $t)> for Version {
                fn from((major, minor, patch, pre_release): ($t, $t, $t, $t)) -> Self {
                    Version {
                        major: major as u64,
                        minor: minor as u64,
                        patch: patch as u64,
                        build: Vec::new(),
                        pre_release: vec![Identifier::Numeric(pre_release as u64)],
                    }
                }
            }
        )+
    }
}

macro_rules! impl_from_signed_for_version {
    ($($t:ident),+) => {
        $(
            impl ::std::convert::From<($t, $t, $t)> for Version {
                fn from((major, minor, patch): ($t, $t, $t)) -> Self {
                    debug_assert!(major >= 0, "Version major must be non-negative, got {}", major);
                    debug_assert!(minor >= 0, "Version minor must be non-negative, got {}", minor);
                    debug_assert!(patch >= 0, "Version patch must be non-negative, got {}", patch);

                    Version {
                        major: major as u64,
                        minor: minor as u64,
                        patch: patch as u64,
                        build: Vec::new(),
                        pre_release: Vec::new(),
                    }
                }
            }

            impl ::std::convert::From<($t, $t, $t, $t)> for Version {
                fn from((major, minor, patch, pre_release): ($t, $t, $t, $t)) -> Self {
                    debug_assert!(major >= 0, "Version major must be non-negative, got {}", major);
                    debug_assert!(minor >= 0, "Version minor must be non-negative, got {}", minor);
                    debug_assert!(patch >= 0, "Version patch must be non-negative, got {}", patch);
                    debug_assert!(pre_release >= 0, "Version pre-release must be non-negative, got {}", pre_release);

                    Version {
                        major: major as u64,
                        minor: minor as u64,
                        patch: patch as u64,
                        build: Vec::new(),
                        pre_release: vec![Identifier::Numeric(pre_release as u64)],
                    }
                }
            }
        )+
    }
}

impl_from_unsigned_for_version!(u8, u16, u32, u64, usize);
impl_from_signed_for_version!(i8, i16, i32, i64, isize);

impl std::str::FromStr for Version {
    type Err = SemverError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Version::parse(s)
    }
}

impl cmp::PartialOrd for Version {
    fn partial_cmp(&self, other: &Version) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl cmp::Ord for Version {
    fn cmp(&self, other: &Version) -> cmp::Ordering {
        match self.major.cmp(&other.major) {
            Ordering::Equal => {}
            //if difference in major version, just return result
            order_result => return order_result,
        }

        match self.minor.cmp(&other.minor) {
            Ordering::Equal => {}
            //if difference in minor version, just return result
            order_result => return order_result,
        }

        match self.patch.cmp(&other.patch) {
            Ordering::Equal => {}
            //if difference in patch version, just return result
            order_result => return order_result,
        }

        match (self.pre_release.len(), other.pre_release.len()) {
            //if no pre_release string, they're equal
            (0, 0) => Ordering::Equal,
            //if other has a pre-release string, but this doesn't, this one is greater
            (0, _) => Ordering::Greater,
            //if this one has a pre-release string, but other doesn't this one is less than
            (_, 0) => Ordering::Less,
            // if both have pre_release strings, compare the strings and return the result
            (_, _) => self.pre_release.cmp(&other.pre_release),
        }
    }
}

enum Extras {
    Build(Vec<Identifier>),
    Release(Vec<Identifier>),
    ReleaseAndBuild((Vec<Identifier>, Vec<Identifier>)),
}

impl Extras {
    fn values(self) -> (Vec<Identifier>, Vec<Identifier>) {
        use Extras::*;
        match self {
            Release(ident) => (ident, Vec::new()),
            Build(ident) => (Vec::new(), ident),
            ReleaseAndBuild(ident) => ident,
        }
    }
}

/// <valid semver> ::= <version core>
///                 | <version core> "-" <pre-release>
///                 | <version core> "+" <build>
///                 | <version core> "-" <pre-release> "+" <build>
fn version<'s>(input: &mut &'s str) -> PResult<Version, SemverParseError<&'s str>> {
    (
        opt(alt((literal("v"), literal("V")))),
        space0,
        version_core,
        extras,
    )
        .map(
            |(_, _, (major, minor, patch), (pre_release, build))| Version {
                major,
                minor,
                patch,
                pre_release,
                build,
            },
        )
        .context("version")
        .parse_next(input)
}

fn extras<'s>(
    input: &mut &'s str,
) -> PResult<(Vec<Identifier>, Vec<Identifier>), SemverParseError<&'s str>> {
    Parser::map(
        opt(alt((
            Parser::map((pre_release, build), Extras::ReleaseAndBuild),
            Parser::map(pre_release, Extras::Release),
            Parser::map(build, Extras::Build),
        ))),
        |extras| match extras {
            Some(extras) => extras.values(),
            _ => Default::default(),
        },
    )
    .parse_next(input)
}

/// <version core> ::= <major> "." <minor> "." <patch>
fn version_core<'s>(input: &mut &'s str) -> PResult<(u64, u64, u64), SemverParseError<&'s str>> {
    (number, literal("."), number, literal("."), number)
        .map(|(major, _, minor, _, patch)| (major, minor, patch))
        .context("version core")
        .parse_next(input)
}

// I believe build, pre_release, and identifier are not 100% spec compliant.
fn build<'s>(input: &mut &'s str) -> PResult<Vec<Identifier>, SemverParseError<&'s str>> {
    preceded(literal("+"), separated(1.., identifier, literal(".")))
        .context("build version")
        .parse_next(input)
}

fn pre_release<'s>(input: &mut &'s str) -> PResult<Vec<Identifier>, SemverParseError<&'s str>> {
    preceded(opt(literal("-")), separated(1.., identifier, literal(".")))
        .context("pre_release version")
        .parse_next(input)
}

fn identifier<'s>(input: &mut &'s str) -> PResult<Identifier, SemverParseError<&'s str>> {
    Parser::map(
        take_while(1.., |x: char| AsChar::is_alphanum(x as u8) || x == '-'),
        |s: &str| {
            str::parse::<u64>(s)
                .map(Identifier::Numeric)
                .unwrap_or_else(|_err| Identifier::AlphaNumeric(s.to_string()))
        },
    )
    .context("identifier")
    .parse_next(input)
}

fn is_valid_prerelease_identifier(identifier: &str) -> bool {
    !identifier.is_empty()
        && identifier.split('.').all(|segment| {
            !segment.is_empty()
                && segment
                    .chars()
                    .all(|ch| ch.is_ascii_alphanumeric() || ch == '-')
        })
}

fn join_prerelease_components(pre_release: &[Identifier]) -> String {
    pre_release
        .iter()
        .map(|ident| ident.to_string())
        .collect::<Vec<_>>()
        .join(".")
}

fn compare_identifier_and_str(existing: &Identifier, other: &str) -> Ordering {
    match existing {
        Identifier::Numeric(value) => {
            if other.chars().all(|c| c.is_ascii_digit()) {
                match other.parse::<u128>() {
                    Ok(other_num) => (*value as u128).cmp(&other_num),
                    Err(_) => Ordering::Less,
                }
            } else {
                Ordering::Less
            }
        }
        Identifier::AlphaNumeric(value) => {
            if other.chars().all(|c| c.is_ascii_digit()) {
                Ordering::Greater
            } else {
                value.as_str().cmp(other)
            }
        }
    }
}

pub(crate) fn number<'s>(input: &mut &'s str) -> PResult<u64, SemverParseError<&'s str>> {
    #[allow(suspicious_double_ref_op)]
    let copied = input.clone();

    Parser::try_map(Parser::take(digit1), |raw| {
        let value = str::parse(raw).map_err(|e| SemverParseError {
            input: copied,
            context: None,
            kind: Some(SemverErrorKind::ParseIntError(e)),
        })?;

        if value > MAX_SAFE_INTEGER {
            return Err(SemverParseError {
                input: copied,
                context: None,
                kind: Some(SemverErrorKind::MaxIntError(value)),
            });
        }

        Ok(value)
    })
    .context("number component")
    .parse_next(input)
}

#[cfg(test)]
mod tests {
    use super::Identifier::*;
    use super::*;

    use pretty_assertions::assert_eq;
    use serde_json::Value;

    #[derive(Debug)]
    struct IncrementCase {
        version: String,
        release: String,
        expected: Option<String>,
        identifier: Option<String>,
        identifier_base: Option<IdentifierBase>,
    }

    fn version_without_build(version: &Version) -> String {
        let mut output = format!("{}.{}.{}", version.major, version.minor, version.patch);
        if !version.pre_release.is_empty() {
            output.push('-');
            output.push_str(&join_prerelease_components(&version.pre_release));
        }
        output
    }

    fn parse_identifier_base_value(value: &Value) -> Option<IdentifierBase> {
        match value {
            Value::Bool(false) => Some(IdentifierBase::False),
            Value::Bool(true) => Some(IdentifierBase::Value(1)),
            Value::Number(num) => num.as_u64().map(IdentifierBase::Value),
            Value::String(s) => s.parse::<u64>().ok().map(IdentifierBase::Value),
            Value::Null => None,
            _ => None,
        }
    }

    fn parse_increment_entry(entry: Value) -> IncrementCase {
        let arr = entry
            .as_array()
            .unwrap_or_else(|| panic!("fixture entry must be an array: {entry:?}"));

        let version = arr
            .get(0)
            .and_then(Value::as_str)
            .unwrap_or_else(|| panic!("missing version in fixture: {arr:?}"))
            .to_string();
        let release = arr
            .get(1)
            .and_then(Value::as_str)
            .unwrap_or_else(|| panic!("missing release in fixture: {arr:?}"))
            .to_string();
        let expected = arr.get(2).and_then(Value::as_str).map(str::to_string);

        let options = arr.get(3);
        let (identifier, identifier_base_value) = if let Some(Value::String(s)) = options {
            (Some(s.to_string()), arr.get(4).cloned())
        } else {
            (
                arr.get(4).and_then(Value::as_str).map(str::to_string),
                arr.get(5).cloned(),
            )
        };

        let identifier_base = identifier_base_value
            .as_ref()
            .and_then(parse_identifier_base_value);

        IncrementCase {
            version,
            release,
            expected,
            identifier,
            identifier_base,
        }
    }

    fn load_increment_cases() -> Vec<IncrementCase> {
        let raw = include_str!("../node-semver/test/fixtures/increments.js");
        let cleaned = raw
            .lines()
            .filter(|line| !line.trim_start().starts_with("//"))
            .collect::<Vec<_>>()
            .join("\n");

        let start = cleaned
            .find('[')
            .expect("expected array start in fixture file");
        let end = cleaned
            .rfind(']')
            .expect("expected array end in fixture file");

        let mut jsonish = cleaned[start..=end].to_string();
        jsonish = jsonish.replace('\'', "\"");
        jsonish = jsonish.replace("loose:", "\"loose\":");
        jsonish = jsonish.replace(",\n]", "\n]");
        jsonish = jsonish.replace(",]", "]");

        let fixtures: Vec<Value> =
            serde_json::from_str(&jsonish).expect("failed to parse increment fixtures");
        fixtures
            .into_iter()
            .map(parse_increment_entry)
            .collect::<Vec<_>>()
    }

    #[test]
    fn trivial_version_number() {
        let v = Version::parse("1.2.34").unwrap();

        assert_eq!(
            v,
            Version {
                major: 1,
                minor: 2,
                patch: 34,
                build: Vec::with_capacity(2),
                pre_release: Vec::with_capacity(2),
            }
        );
    }

    #[test]
    fn version_with_build() {
        let v = Version::parse("1.2.34+123.456").unwrap();

        assert_eq!(
            v,
            Version {
                major: 1,
                minor: 2,
                patch: 34,
                build: vec![Numeric(123), Numeric(456)],
                pre_release: Vec::with_capacity(2),
            }
        );
    }

    #[test]
    fn version_with_pre_release() {
        let v = Version::parse("1.2.34-abc.123").unwrap();

        assert_eq!(
            v,
            Version {
                major: 1,
                minor: 2,
                patch: 34,
                pre_release: vec![AlphaNumeric("abc".into()), Numeric(123)],
                build: Vec::with_capacity(2),
            }
        );
    }

    #[test]
    fn version_with_pre_release_and_build() {
        let v = Version::parse("1.2.34-abc.123+1").unwrap();

        assert_eq!(
            v,
            Version {
                major: 1,
                minor: 2,
                patch: 34,
                pre_release: vec![AlphaNumeric("abc".into()), Numeric(123)],
                build: vec![Numeric(1),]
            }
        );
    }

    #[test]
    fn pre_release_that_could_look_numeric_at_first() {
        let v = Version::parse("1.0.0-rc.2-migration").unwrap();

        assert_eq!(
            v,
            Version {
                major: 1,
                minor: 0,
                patch: 0,
                pre_release: vec![
                    Identifier::AlphaNumeric("rc".into()),
                    Identifier::AlphaNumeric("2-migration".into())
                ],
                build: vec![],
            }
        );
    }

    #[test]
    fn comparison_with_different_major_version() {
        let lesser_version = Version {
            major: 1,
            minor: 2,
            patch: 34,
            pre_release: vec![AlphaNumeric("abc".into()), Numeric(123)],
            build: vec![],
        };
        let greater_version = Version {
            major: 2,
            minor: 2,
            patch: 34,
            pre_release: vec![AlphaNumeric("abc".into()), Numeric(123)],
            build: vec![],
        };
        assert_eq!(lesser_version.cmp(&greater_version), Ordering::Less);
        assert_eq!(greater_version.cmp(&lesser_version), Ordering::Greater);
    }
    #[test]
    fn comparison_with_different_minor_version() {
        let lesser_version = Version {
            major: 1,
            minor: 2,
            patch: 34,
            pre_release: vec![AlphaNumeric("abc".into()), Numeric(123)],
            build: vec![],
        };
        let greater_version = Version {
            major: 1,
            minor: 3,
            patch: 34,
            pre_release: vec![AlphaNumeric("abc".into()), Numeric(123)],
            build: vec![],
        };
        assert_eq!(lesser_version.cmp(&greater_version), Ordering::Less);
        assert_eq!(greater_version.cmp(&lesser_version), Ordering::Greater);
    }

    #[test]
    fn comparison_with_different_patch_version() {
        let lesser_version = Version {
            major: 1,
            minor: 2,
            patch: 34,
            pre_release: vec![AlphaNumeric("abc".into()), Numeric(123)],
            build: vec![],
        };
        let greater_version = Version {
            major: 1,
            minor: 2,
            patch: 56,
            pre_release: vec![AlphaNumeric("abc".into()), Numeric(123)],
            build: vec![],
        };
        assert_eq!(lesser_version.cmp(&greater_version), Ordering::Less);
        assert_eq!(greater_version.cmp(&lesser_version), Ordering::Greater);
    }

    #[test]
    //confirms the comparison matches the pre-release comparison example in the SemVer spec.
    //ie checks that 1.0.0-alpha < 1.0.0-alpha.1 < 1.0.0-alpha.beta < 1.0.0-beta < 1.0.0-beta.2 < 1.0.0-beta.11 < 1.0.0-rc.1 < 1.0.0.
    //for simplicity just checks them in order. Assumes that the transitive property holds. So if a < b & b < c then a < c.
    fn comparison_with_different_pre_release_version() {
        let v1_alpha = Version {
            major: 1,
            minor: 0,
            patch: 0,
            pre_release: vec![AlphaNumeric("alpha".into())],
            build: vec![],
        };
        let v1_alpha1 = Version {
            major: 1,
            minor: 0,
            patch: 0,
            pre_release: vec![AlphaNumeric("alpha".into()), Numeric(1)],
            build: vec![],
        };
        assert_eq!(v1_alpha.cmp(&v1_alpha1), Ordering::Less);
        let v1_alpha_beta = Version {
            major: 1,
            minor: 0,
            patch: 0,
            pre_release: vec![AlphaNumeric("alpha".into()), AlphaNumeric("beta".into())],
            build: vec![],
        };
        assert_eq!(v1_alpha1.cmp(&v1_alpha_beta), Ordering::Less);
        let v1_beta = Version {
            major: 1,
            minor: 0,
            patch: 0,
            pre_release: vec![AlphaNumeric("beta".into())],
            build: vec![],
        };
        assert_eq!(v1_alpha_beta.cmp(&v1_beta), Ordering::Less);
        let v1_beta2 = Version {
            major: 1,
            minor: 0,
            patch: 0,
            pre_release: vec![AlphaNumeric("beta".into()), Numeric(2)],
            build: vec![],
        };
        assert_eq!(v1_beta.cmp(&v1_beta2), Ordering::Less);
        let v1_beta11 = Version {
            major: 1,
            minor: 0,
            patch: 0,
            pre_release: vec![AlphaNumeric("beta".into()), Numeric(11)],
            build: vec![],
        };
        assert_eq!(v1_beta2.cmp(&v1_beta11), Ordering::Less);
        let v1_rc1 = Version {
            major: 1,
            minor: 0,
            patch: 0,
            pre_release: vec![AlphaNumeric("rc".into()), Numeric(1)],
            build: vec![],
        };
        assert_eq!(v1_beta11.cmp(&v1_rc1), Ordering::Less);
        let v1 = Version {
            major: 1,
            minor: 0,
            patch: 0,
            pre_release: vec![],
            build: vec![],
        };
        assert_eq!(v1_rc1.cmp(&v1), Ordering::Less);
    }

    #[test]
    fn individual_version_component_has_an_upper_bound() {
        let out_of_range = MAX_SAFE_INTEGER + 1;
        let v = Version::parse(format!("1.2.{}", out_of_range));
        assert_eq!(v.expect_err("Parse should have failed.").to_string(), "Integer component of semver string is larger than JavaScript's Number.MAX_SAFE_INTEGER: 900719925474100");
    }

    #[test]
    fn version_string_limited_to_256_characters() {
        let prebuild = (0..257).map(|_| "X").collect::<Vec<_>>().join("");
        let version_string = format!("1.1.1-{}", prebuild);
        let v = Version::parse(version_string.clone());

        assert_eq!(
            v.expect_err("Parse should have failed").to_string(),
            "Semver string can't be longer than 256 characters."
        );

        let ok_version = version_string[0..255].to_string();
        let v = Version::parse(ok_version);
        assert!(v.is_ok());
    }

    #[test]
    fn version_prefixed_with_v() {
        // TODO: This is part of strict parsing for nodejs-semver!
        let v = Version::parse("v1.2.3").unwrap();
        assert_eq!(
            v,
            Version {
                major: 1,
                minor: 2,
                patch: 3,
                pre_release: vec![],
                build: vec![],
            }
        );
    }

    #[test]
    fn version_prefixed_with_v_space() {
        // TODO: Loose parsing supports this, so
        let v = Version::parse("v 1.2.3").unwrap();
        assert_eq!(
            v,
            Version {
                major: 1,
                minor: 2,
                patch: 3,
                pre_release: vec![],
                build: vec![],
            }
        );
    }

    fn asset_version_diff(left: &str, right: &str, expected: &str) {
        let left = Version::parse(left).unwrap();
        let right = Version::parse(right).unwrap();
        let expected_diff = match expected {
            "major" => Some(VersionDiff::Major),
            "minor" => Some(VersionDiff::Minor),
            "patch" => Some(VersionDiff::Patch),
            "premajor" => Some(VersionDiff::PreMajor),
            "preminor" => Some(VersionDiff::PreMinor),
            "prepatch" => Some(VersionDiff::PrePatch),
            "null" => None,
            _ => unreachable!("unexpected version diff"),
        };

        assert_eq!(
            left.diff(&right),
            expected_diff,
            "left: {}, right: {}",
            left,
            right
        );
    }

    #[test]
    fn version_diffs() {
        let cases = vec![
            ("1.2.3", "0.2.3", "major"),
            ("0.2.3", "1.2.3", "major"),
            ("1.4.5", "0.2.3", "major"),
            ("1.2.3", "2.0.0-pre", "premajor"),
            ("2.0.0-pre", "1.2.3", "premajor"),
            ("1.2.3", "1.3.3", "minor"),
            ("1.0.1", "1.1.0-pre", "preminor"),
            ("1.2.3", "1.2.4", "patch"),
            ("1.2.3", "1.2.4-pre", "prepatch"),
            ("1.0.0", "1.0.0", "null"),
            ("1.0.0-1", "1.0.0-1", "null"),
            ("0.0.2-1", "0.0.2", "patch"),
            ("0.0.2-1", "0.0.3", "patch"),
            ("0.0.2-1", "0.1.0", "minor"),
            ("0.0.2-1", "1.0.0", "major"),
            ("0.1.0-1", "0.1.0", "minor"),
            ("1.0.0-1", "2.0.0-1", "premajor"),
            ("1.0.0-1", "1.1.0-1", "preminor"),
            ("1.0.0-1", "1.0.1-1", "prepatch"),
        ];

        for case in cases {
            asset_version_diff(case.0, case.1, case.2);
        }
    }

    #[test]
    fn increments_match_node_semver_fixture() {
        for case in load_increment_cases() {
            if let Some(expected) = &case.expected {
                let version = Version::parse(&case.version).unwrap_or_else(|e| {
                    panic!(
                        "expected to parse {} but failed: {}",
                        case.version,
                        e.to_string()
                    )
                });
                let before = version.to_string();
                let build = version.build.clone();
                let incremented = version
                    .inc(
                        &case.release,
                        case.identifier.as_deref(),
                        case.identifier_base,
                    )
                    .unwrap_or_else(|e| {
                        panic!(
                            "expected {} {} to succeed but errored: {}",
                            case.version, case.release, e
                        )
                    });

                assert_eq!(
                    version_without_build(&incremented),
                    expected.as_str(),
                    "incrementing {} {} {:?} {:?}",
                    case.version,
                    case.release,
                    case.identifier,
                    case.identifier_base
                );
                assert_eq!(
                    incremented.build, build,
                    "build metadata should remain unchanged after increment"
                );
                assert_eq!(
                    version.to_string(),
                    before,
                    "original version should remain unchanged"
                );
            } else if let Ok(version) = Version::parse(&case.version) {
                let before = version.to_string();
                assert!(
                    version
                        .inc(
                            &case.release,
                            case.identifier.as_deref(),
                            case.identifier_base
                        )
                        .is_err(),
                    "expected {} {} to fail",
                    case.version,
                    case.release
                );
                assert_eq!(
                    version.to_string(),
                    before,
                    "version should stay unchanged on error"
                );
            }
        }
    }

    #[test]
    fn invalid_increment_errors_match_node_semver() {
        let version = Version::parse("1.2.3").unwrap();
        let err = version
            .inc("prerelease", Some(""), Some(IdentifierBase::False))
            .unwrap_err();
        assert_eq!(
            err.to_string(),
            "invalid increment argument: identifier is empty"
        );
        assert_eq!(version.to_string(), "1.2.3");

        let version = Version::parse("1.2.3-dev").unwrap();
        let err = version
            .inc("prerelease", Some("dev"), Some(IdentifierBase::False))
            .unwrap_err();
        assert_eq!(
            err.to_string(),
            "invalid increment argument: identifier already exists"
        );
        assert_eq!(version.to_string(), "1.2.3-dev");

        let version = Version::parse("1.2.3").unwrap();
        let err = version
            .inc("prerelease", Some("invalid/preid"), None)
            .unwrap_err();
        assert_eq!(err.to_string(), "invalid identifier: invalid/preid");
        assert_eq!(version.to_string(), "1.2.3");
    }
}

#[cfg(feature = "serde")]
#[cfg(test)]
mod serde_tests {
    use super::Identifier::*;
    use super::*;

    #[test]
    fn version_serde() {
        let v = Version {
            major: 1,
            minor: 2,
            patch: 3,
            pre_release: vec![AlphaNumeric("abc".into()), Numeric(123)],
            build: vec![AlphaNumeric("build".into())],
        };

        let serialized = serde_json::to_string(&v).unwrap();
        let deserialized: Version = serde_json::from_str(&serialized).unwrap();

        assert_eq!(v, deserialized);
    }
}
