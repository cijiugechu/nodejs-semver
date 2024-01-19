# Development

```sh
cargo +nightly fuzz run semver -- -only_ascii=1 -max_total_time=60 -max_len=30
```