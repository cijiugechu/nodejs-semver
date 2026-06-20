# `nodejs-semver` Release Changelog

<a name="5.0.0"></a>
## 5.0.0 (2026-06-20)

### Features

* **version:** add `VersionParts` and `Version::into_parts()` for moving owned version components out without cloning ([8a7014f](https://github.com/cijiugechu/nodejs-semver/commit/8a7014fbd1fe244e8970c05e76232df6e2871849))

* **range:** improve npm compatibility coverage for wildcard, hyphen, prerelease, and disjunction ranges ([4bce182](https://github.com/cijiugechu/nodejs-semver/commit/4bce182f5df287c117e0fc9edf3e69ee747c6c12))

### Performance

* **version:** add a fast path for common `Version::parse` inputs ([2764904](https://github.com/cijiugechu/nodejs-semver/commit/27649049dad315de3755582ea0011c6e015838eb))

* **range:** add fast paths for common range parsing cases, including exact, comparator, wildcard, tilde, and fallback attempts ([413660e](https://github.com/cijiugechu/nodejs-semver/commit/413660ee971d3e88ce1bfb3e5c6be1e5d390aee8), [786b864](https://github.com/cijiugechu/nodejs-semver/commit/786b864d3507c9db188084df5dfea01f2b7a6669), [6bcc483](https://github.com/cijiugechu/nodejs-semver/commit/6bcc483e6653092240d9b46f9196432c846b5aca))

* **layout:** compact `Version` and common single-range storage to reduce allocation and improve parse-heavy workloads ([2471252](https://github.com/cijiugechu/nodejs-semver/commit/2471252313f6fec692232143f62c39ea8f02e898), [439cb1e](https://github.com/cijiugechu/nodejs-semver/commit/439cb1e25646a6e8d59d9fdb00f8f2e8205964f5))

Benchmarked with `cargo bench --bench parser`, using the same benchmark suite for `v4.2.0` and `5.0.0`. Values are Criterion slope estimates from the same machine.

| benchmark | 4.2.0 | 5.0.0 | speedup |
|---|---:|---:|---:|
| `Version::parse("1.2.3")` | 60.52 ns | 4.86 ns | 12.46x |
| `Version::parse("1.2.3-rc.4+build.7")` | 109.02 ns | 65.00 ns | 1.68x |
| `Range::parse("1.2.3")` | 333.84 ns | 35.91 ns | 9.30x |
| `Range::parse(">=1.2.3 <2.0.0")` | 464.21 ns | 103.39 ns | 4.49x |
| <code>Range::parse("&gt;=18 &lt;20 &#124;&#124; &gt;=22")</code> | 584.19 ns | 261.19 ns | 2.24x |
| `Range::parse("1.x.x")` | 314.54 ns | 58.80 ns | 5.35x |
| parse and satisfy exact range | 386.88 ns | 44.45 ns | 8.70x |
| parse and satisfy wildcard range | 365.71 ns | 65.97 ns | 5.54x |
| filter version strings with current API | 774.59 ns | 221.29 ns | 3.50x |
| package-manager corpus: resolved versions | 7.97 us | 914.05 ns | 8.71x |
| package-manager corpus: specifier range parse attempts | 40.91 us | 7.39 us | 5.54x |
| package-manager corpus: version-then-range parse | 21.61 us | 5.29 us | 4.09x |

Grouped geomean speedups from the full benchmark suite: `version_parse` 4.36x, `range_parse` 4.20x, `range_parse_fallback_attempt` 3.97x, `parse_and_satisfies` 3.72x, and `package_manager_corpus` 5.01x. Already-parsed `Range::satisfies` microbenchmarks remain nanosecond-level and are mixed overall (`0.94x` geomean vs 4.2.0).

### Miscellaneous Tasks

* **bench:** expand parser benchmarks with npm-style range cases and package-manager corpus inputs ([2aef643](https://github.com/cijiugechu/nodejs-semver/commit/2aef643dc9d6504e242c4245698125c31102a33a))

* **msrv:** bump MSRV to `1.85.0` and move the crate to Rust 2024 edition ([4abc489](https://github.com/cijiugechu/nodejs-semver/commit/4abc489bb4db4b3244c89300b0d4d7bba53a104b))

### **BREAKING CHANGE**

The minimum supported Rust version is now `1.85.0`.

`Version` fields are no longer public. This lets the crate keep optimizing the internal representation without exposing layout details.

Read fields through methods:

```rust
let version = Version::parse("1.2.3-alpha.1+build.7")?;

let major = version.major();
let minor = version.minor();
let patch = version.patch();
let pre_release = version.pre_release();
let build = version.build();
```

Construct versions with `Version::new` instead of struct literals:

```rust
let version = Version::new(1, 2, 3, vec![], vec![]);
```

Move all owned components out with `into_parts()` when you previously destructured a `Version`:

```rust
use nodejs_semver::{Version, VersionParts};

let version = Version::parse("1.2.3-alpha.1+build.7")?;
let VersionParts {
    major,
    minor,
    patch,
    pre_release,
    build,
} = version.into_parts();
```

If code previously mutated fields directly, build a new `Version` from updated parts with `Version::new`.

<a name="4.2.0"></a>
## 4.2.0 (2025-11-27)

### Features

* **version:** implement `inc` ([73547a1](https://github.com/cijiugechu/nodejs-semver/commit/73547a1edb25f846ee43976835e151b8c79da57b)) 

* **range:** implement `outside` ([eb5b36f](https://github.com/cijiugechu/nodejs-semver/commit/eb5b36f4fb4ec5a61ab2c262ddef0762482c11ed)) 

### Performance

* **range:** inline `outside` comparisons by specializing helpers ([e933faf](https://github.com/cijiugechu/nodejs-semver/commit/e933faf317ae61da3fc20d519f8608d2a6fc949f)) 

* **range:** remove unnecessary `collect()` ([6bcbbb7](https://github.com/cijiugechu/nodejs-semver/commit/6bcbbb7c6319c6de430b9ce0ad46b03e55933ac0)) 

### Miscellaneous Tasks

* **deps:** bump deps ([e0179f1](https://github.com/cijiugechu/nodejs-semver/commit/e0179f1949bbdb1b7561ad6df9c7f2a79632c0d7))

* **clippy:** make clippy happy ([9013a4c](https://github.com/cijiugechu/nodejs-semver/commit/9013a4cbe87ed4eafc103cac376b7a0681450f57))

* **deps:** bump `winnow` ([0185b2f](https://github.com/cijiugechu/nodejs-semver/commit/0185b2f5a9c58623db2f3b37210209cc6321c9c8))

* **deps:** bump `miette` ([7f64b85](https://github.com/cijiugechu/nodejs-semver/commit/7f64b85eb32119549ba902578d393d610f347db0)) 

<a name="4.1.0"></a>
## 4.1.0 (2024-11-05)

### Features

* **conversion:** implement additional traits for converting integer types to Version. ([d1b6021](https://github.com/cijiugechu/nodejs-semver/commit/d1b6021381be66f8edb8359cdc987a21945baca2)) 

### Bug Fixes

* **namespace:** add prefix to std to avoid namespace conflict ([02a866b](https://github.com/cijiugechu/nodejs-semver/commit/02a866b0c2a0128ff394f6624db2d906a1b9ad73))

### Performance

* **range:** boxing `BoundSet` ([#8](https://github.com/cijiugechu/nodejs-semver/pull/8)) 

### Miscellaneous Tasks

* **deps:** bump deps

<a name="4.0.0"></a>
## 4.0.0 (2024-03-10)

### Miscellaneous Tasks

* **winnow:** upgrade to `winnow` 0.6 ([#6](https://github.com/cijiugechu/nodejs-semver/pull/6))

* **miette:** upgrade to `miette` 7.2 ([#7](https://github.com/cijiugechu/nodejs-semver/pull/7)) 

### **BREAKING CHANGE**

bump MSRV to `1.70.0` ([#7](https://github.com/cijiugechu/nodejs-semver/pull/7))

<a name="3.4.0"></a>
## 3.4.0 (2024-01-06)

### Features

* **range:** add `min_version` ([14ab733](https://github.com/cijiugechu/nodejs-semver/commit/14ab73317ff2de3bd565e65c2ef5c07f8137f8bb)) 

<a name="3.3.1"></a>
## 3.3.1 (2023-12-19)

### Performance

* **winnow:** migrate to `winnow` ([#3](https://github.com/cijiugechu/nodejs-semver/pull/3)) 

<a name="3.3.0"></a>
## 3.3.0 (2023-11-30)

### Features

* **serde:** add optional feature: `serde` ([3842e9af](https://github.com/cijiugechu/nodejs-semver/commit/3842e9af9ae266a672c073063c8765a2f07dbec7)) 

<a name="3.2.0"></a>
## 3.2.0 (2023-10-22)

### Features

* **range:** add `max_satisfying` ([5efbeaa](https://github.com/cijiugechu/nodejs-semver/commit/5efbeaa35982d4ebc4ab1cbb393d1bba20b5b3d1)) and `min_satisfying` ([a476865](https://github.com/cijiugechu/nodejs-semver/commit/a4768658bc225e92c05862c13f59357f75d83583))

* **type:** add `ReleaseType` ([10e0caa](https://github.com/cijiugechu/nodejs-semver/commit/10e0caaa64b14d6a086a337c72c5a26ad5fa1328))

### Documentation

* **examples:** add examples ([648b45c](https://github.com/cijiugechu/nodejs-semver/commit/648b45ceed08b299455617a9bea68705e4c82861))

<a name="3.1.0"></a>
## 3.1.0 (2023-10-10)

### Miscellaneous Tasks

* **deps:** bump deps

### Features

* **diff:** add `diff` for `Version` ([1dae57fa](https://github.com/cijiugechu/nodejs-semver/commit/1dae57faa246ed8bd3207d29893f0c9c2f0bea78))

<a name="3.0.1"></a>
## 3.0.1 (2023-09-29)

### Bug Fixes

* **range:** make `<=11` work the same as in npm (#1) ([6438d9f4](https://github.com/cijiugechu/nodejs-semver/commit/6438d9f46a888b4296a665673e3361b35999979b))

<a name="3.0.0"></a>
## 3.0.0 (2023-09-06)

### **BREAKING CHANGE**

remove unnecessary `serde`([18f26b43](https://github.com/cijiugechu/nodejs-semver/commit/18f26b4305150385fb174a8c60c50a328e4998d6))

### Performance

* **vector:** initialize vector with capacity([f454c8e1](https://github.com/cijiugechu/nodejs-semver/commit/f454c8e1ad04b7b41adbb5a5aa6d8e46e694cc2f))

<a name="2.2.0"></a>
## 2.2.0 (2023-09-05)

### Miscellaneous Tasks

* **crate:** Project forked.

### Performance

* **syscall:** Reduced unnecessary cloning operations([598e3554](https://github.com/cijiugechu/nodejs-semver/commit/598e355476e19e96f7dd6dd1582d65b7fdc13221))

<a name="2.1.0"></a>
## 2.1.0 (2022-09-21)

### Features

* **format:** Include the build and prerelease when stringifying to maintain consistency (#9) ([f2b2e44c](https://github.com/felipesere/node-semver-rs/commit/f2b2e44c8dfe815c194c4f458025fbbbf418fd9f))

<a name="2.0.1"></a>
## 2.0.1 (2022-09-04)

### Bug Fixes

* **satisfies:** Fix `.satisfies` bug for higher major/minor/path pre-release versions (#8) ([ee8376e7](https://github.com/felipesere/node-semver-rs/commit/ee8376e7f060cb19829e5e0e62c1a729cf4653f8))
* **range:** handle partial `=` ranges, which was causing panics (#7) ([f0eef040](https://github.com/felipesere/node-semver-rs/commit/f0eef04032cf1fe7ed341a110897005c31e61ead))

<a name="2.0.0"></a>
## 2.0.0 (2021-09-26)

This is an almost full rewrite of the Range parser to make it work much more
closely to how the JS `node-semver` parser works. Not by using regex,
fortunately.

As such, this is potentially a pretty breaking change, but it's a breaking
change in the direction of compatibility.

Please file issues for any compatibility issues you find and we'll fix them
asap!

### Features

* **loose:** rewrite to support loose mode better (#5) ([20fb02d8](https://github.com/felipesere/node-semver-rs/commit/20fb02d882caf12439f115277ec3ca587ad1e62e))
  * **BREAKING CHANGE**: This accepts (and rejects) some semver strings that
    were valid before, and I'm not comfortable just calling thos e bugs. It
    also vastly reduces the number of "bad" semver parses by outright throwing
    out bad-looking data without warning you. This is literally what the
    JavaScript node-semver does. And so...

<a name="1.0.1"></a>
## 1.0.1 (2021-09-24)

### Bug Fixes

* **api:** stop exporting anything but Range from range mod ([4eeb862d](https://github.com/felipesere/node-semver-rs/commit/4eeb862dd2d07901826c3e6d47b8c9ffe2cf90d3))

<a name="1.0.0"></a>
## 1.0.0 (2021-09-24)

### Features

* **error:** upgrade miette and change error API a bit ([82625fd3](https://github.com/felipesere/node-semver-rs/commit/82625fd37384cc24469a55e28a8c8d310e619276))
    * **BREAKING CHANGE**: This changes the error API a bit. You may need to update code that handles errors by hand
* **version:** add .satisfies() method to Version ([da70b187](https://github.com/felipesere/node-semver-rs/commit/da70b1872bdd6f910d56d6b1c674d0c3dabdeaf6))
