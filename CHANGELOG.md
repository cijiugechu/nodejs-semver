# `nodejs-semver` Release Changelog

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

