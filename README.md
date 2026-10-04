# `nodejs-semver` — npm-compatible SemVer for Rust

[![Cargo](https://img.shields.io/crates/v/nodejs-semver.svg)](https://crates.io/crates/nodejs-semver)
[![Documentation](https://docs.rs/nodejs-semver/badge.svg)](https://docs.rs/nodejs-semver)

A pure Rust parser and evaluator for npm/node-semver versions and ranges,
built for package managers and JavaScript tooling. Use `nodejs-semver` to match
`package.json` dependency ranges, select compatible versions, compare releases,
and check Node.js engine requirements without a JavaScript runtime.

`nodejs-semver` targets the behavior of JavaScript's
[`node-semver`](https://github.com/npm/node-semver), published on npm as `semver`.
It forked from the Rust [`node-semver` crate](https://crates.io/crates/node-semver)
in September 2023 and has since added version-selection and release APIs,
optimized parsing and storage, and made Serde optional.

- **npm range syntax:** caret, tilde, wildcard, hyphen, comparator, and `||` ranges.
- **Package-manager APIs:** `max_satisfying`, `min_satisfying`, `min_version`,
  `outside`, `diff`, and `inc`, alongside range intersection and difference.
- **Parsing:** handwritten parsers with fast paths for common inputs and compact
  storage for versions and single comparator sets.

[API documentation](https://docs.rs/nodejs-semver) ·
[Changelog](https://github.com/cijiugechu/nodejs-semver/blob/main/CHANGELOG.md) ·
[Examples](https://github.com/cijiugechu/nodejs-semver/tree/main/examples)

## Installation

Add this to your `Cargo.toml`:

```toml
[dependencies]
nodejs-semver = "7"
```

The Cargo package name is `nodejs-semver`; the Rust import is `nodejs_semver`.

## Usage

### Check whether a version satisfies an npm range

Parse a [Version] and a [Range], then call `satisfies`:

```rust
use nodejs_semver::{Range, Version};

let version: Version = "1.2.3".parse().unwrap();
let range: Range = "^1.2".parse().unwrap();

assert!(version.satisfies(&range));
assert!(!Version::parse("2.0.0").unwrap().satisfies(&range));
```

## nodejs-semver vs. the node-semver Rust crate

Both crates implement npm-style semantic versioning in Rust and share project
history. The comparison below is scoped to **`nodejs-semver` 7.0.0** and
**`node-semver` 2.2.0**; the latter is a Rust crate, distinct from the JavaScript
`node-semver` project.

| Capability | `nodejs-semver` 7.0.0 | `node-semver` 2.2.0 |
| --- | --- | --- |
| Parse versions and npm ranges; check satisfaction | Yes | Yes |
| Range intersection, difference, and `min_version` | Yes | Yes |
| Select from a version list | `max_satisfying` and `min_satisfying` | No corresponding public methods |
| Release operations and range bounds | `Version::diff`, `Version::inc`, and `Range::outside` | No corresponding public methods |
| Include prereleases explicitly when matching | `satisfies_with_prerelease` | No corresponding public method |
| Parser and required direct dependencies | Handwritten parser; `smallvec`, `thiserror` | `nom` parser; `nom`, `miette`, `bytecount`, `thiserror`, `serde` |
| Serde serialization | Optional `serde` feature, disabled by default | Included unconditionally |
| Parse errors | Lightweight `SemverError` with a fixed message | Error kinds, original input, source locations, and `miette` diagnostics |

Sources: `node-semver` 2.2.0's [Range API](https://docs.rs/node-semver/2.2.0/node_semver/struct.Range.html),
[Version API](https://docs.rs/node-semver/2.2.0/node_semver/struct.Version.html),
[error API](https://docs.rs/node-semver/2.2.0/node_semver/struct.SemverError.html),
and [Cargo manifest](https://docs.rs/crate/node-semver/2.2.0/source/Cargo.toml.orig);
`nodejs-semver`'s [API](https://docs.rs/nodejs-semver/7.0.0/nodejs_semver/)
and [release history](https://github.com/cijiugechu/nodejs-semver/blob/main/CHANGELOG.md).

Choose `nodejs-semver` when you need its additional package-manager APIs,
optional serialization, or its parsing optimizations.

### How does this differ from the semver crate?

The [`semver` crate](https://docs.rs/semver) implements Cargo's flavor of semantic
versioning. `nodejs-semver` targets npm range syntax and matching behavior for
JavaScript tooling. Use the ecosystem's range semantics when interpreting
dependency requirements: npm and Cargo requirements are not interchangeable.

## Performance

The following compares the Rust crates **`nodejs-semver` 7.0.0** and
**`node-semver` 2.2.0**, their latest stable releases on crates.io as of
2026-10-04 ([nodejs-semver](https://crates.io/crates/nodejs-semver),
[node-semver](https://crates.io/crates/node-semver)).

Measured on an Apple M4, macOS 15.7.5 (aarch64), with Rust 1.98.1 and Cargo's
optimized bench profile. Each case uses Criterion 0.5.1 with 100 samples,
a 1-second warm-up, and a 3-second measurement window. Times are Criterion
slope point estimates per operation; speedup is `node-semver / nodejs-semver`
(higher is better for `nodejs-semver`).

| Workload | `nodejs-semver` 7.0.0 | `node-semver` 2.2.0 | Speedup |
| --- | ---: | ---: | ---: |
| `Version::parse("1.2.3")` | 9.40 ns | 239.25 ns | 25.46× |
| `Version::parse("1.2.3-rc.4+build.7")` | 217.90 ns | 501.74 ns | 2.30× |
| `Range::parse("1.2.3")` | 71.57 ns | 766.80 ns | 10.71× |
| `Range::parse("^1.2.3")` | 150.72 ns | 859.02 ns | 5.70× |
| `Range::parse(">=1.2.3 <2.0.0")` | 280.56 ns | 1016.48 ns | 3.62× |
| `Range::parse(">=18 <20 \|\| >=22")` | 713.99 ns | 1426.52 ns | 2.00× |


## Migrating from node-semver or older nodejs-semver releases

- Change the Cargo dependency to `nodejs-semver` and imports to `nodejs_semver`.
- Since 5.0.0, read version components through `major()`, `minor()`, `patch()`,
  `pre_release()`, and `build()`. Replace struct literals or direct field mutation
  with `Version::new(major, minor, patch, pre_release, build)`. Use `into_parts()`
  to move owned components into [VersionParts] without cloning.
- Since 6.0.0, parsing returns a lightweight `SemverError`. It implements
  `std::error::Error` and `Display`, with the message
  `Invalid semantic version or range`, but no longer retains input or exposes
  `SemverErrorKind`, source locations, or `miette::Diagnostic`. Keep the original
  input in your application if you need it for error reporting.
- For 7.0.0, recheck unusual whitespace and mixed loose/strict range inputs:
  accepted inputs and displayed range forms can differ from earlier releases.
- Enable `serde` explicitly if you serialize versions or ranges, and use
  Rust 1.85.0 or newer.

The [changelog](https://github.com/cijiugechu/nodejs-semver/blob/main/CHANGELOG.md)
contains the full breaking-change notes and migration examples.

## Optional Features

No features are enabled by default. Enable **serde** for serialization and
deserialization of [Version] and [Range] as strings:

```toml
[dependencies]
nodejs-semver = { version = "7", features = ["serde"] }
```

[Version]: https://docs.rs/nodejs-semver/latest/nodejs_semver/struct.Version.html
[Range]: https://docs.rs/nodejs-semver/latest/nodejs_semver/struct.Range.html
[VersionParts]: https://docs.rs/nodejs-semver/latest/nodejs_semver/struct.VersionParts.html
