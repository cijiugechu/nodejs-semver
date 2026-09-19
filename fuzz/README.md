# Development

```sh
cargo +nightly fuzz run semver -- -max_total_time=60 -max_len=1024
```

The target exercises version and range parsing for all valid UTF-8 input,
including Unicode identifiers and control characters.
