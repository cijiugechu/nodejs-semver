//! Shared scanning for the loose fallback parsers. Common inputs use the fast parsers.

use crate::{Identifier, MAX_SAFE_INTEGER, Version};

#[derive(Clone, Copy)]
pub(crate) struct Cursor<'a> {
    pub(crate) remaining: &'a str,
}

impl<'a> Cursor<'a> {
    pub(crate) fn new(input: &'a str) -> Self {
        Self { remaining: input }
    }

    pub(crate) fn eat(&mut self, token: &str) -> bool {
        if let Some(rest) = self.remaining.strip_prefix(token) {
            self.remaining = rest;
            true
        } else {
            false
        }
    }

    // The legacy fallback separates tokens with spaces and tabs only.
    pub(crate) fn spaces(&mut self) -> bool {
        let rest = self.remaining.trim_start_matches([' ', '\t']);
        let consumed = rest.len() != self.remaining.len();
        self.remaining = rest;
        consumed
    }

    pub(crate) fn number(&mut self) -> Option<u64> {
        let mut value = 0u64;
        let mut len = 0;
        for ch in self.remaining.bytes().take_while(u8::is_ascii_digit) {
            value = value.checked_mul(10)?.checked_add(u64::from(ch - b'0'))?;
            if value > MAX_SAFE_INTEGER {
                return None;
            }
            len += 1;
        }
        if len == 0 {
            return None;
        }
        self.remaining = &self.remaining[len..];
        Some(value)
    }

    pub(crate) fn extras(&mut self) -> (Vec<Identifier>, Vec<Identifier>) {
        let mut release = *self;
        release.eat("-");
        if let Some(pre) = release.identifiers() {
            *self = release;
            let build = self.build().unwrap_or_default();
            return (pre, build);
        }
        (Vec::new(), self.build().unwrap_or_default())
    }

    fn build(&mut self) -> Option<Vec<Identifier>> {
        let mut build = *self;
        if !build.eat("+") {
            return None;
        }
        let identifiers = build.identifiers()?;
        *self = build;
        Some(identifiers)
    }

    fn identifiers(&mut self) -> Option<Vec<Identifier>> {
        let mut identifiers = vec![self.identifier()?];
        loop {
            let mut next = *self;
            if !next.eat(".") {
                break;
            }
            let Some(identifier) = next.identifier() else {
                break;
            };
            identifiers.push(identifier);
            *self = next;
        }
        Some(identifiers)
    }

    fn identifier(&mut self) -> Option<Identifier> {
        let len = self
            .remaining
            .chars()
            // Preserve the legacy low-byte classification for non-ASCII input.
            .take_while(|&ch| (ch as u8).is_ascii_alphanumeric() || ch == '-')
            .map(char::len_utf8)
            .sum();
        if len == 0 {
            return None;
        }
        let raw = &self.remaining[..len];
        self.remaining = &self.remaining[len..];
        Some(
            raw.parse::<u64>()
                .map(Identifier::Numeric)
                .unwrap_or_else(|_| Identifier::AlphaNumeric(raw.to_owned())),
        )
    }
}

pub(crate) fn version(input: &str) -> Option<Version> {
    let mut cursor = Cursor::new(input);
    if !cursor.eat("v") {
        cursor.eat("V");
    }
    cursor.spaces();
    let major = cursor.number()?;
    if !cursor.eat(".") {
        return None;
    }
    let minor = cursor.number()?;
    if !cursor.eat(".") {
        return None;
    }
    let patch = cursor.number()?;
    let (pre, build) = cursor.extras();
    // Loose version parsing deliberately permits unconsumed suffixes.
    Some(Version::new(major, minor, patch, pre, build))
}
