use criterion::{black_box, criterion_group, criterion_main, Criterion};
use nodejs_semver::{Range, Version};

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("version parser", |b| {
        b.iter(|| {
            let _v = Version::parse(black_box("1.2.3-rc.4")).unwrap();
        })
    });

    c.bench_function("range", |b| {
        b.iter(|| {
            let range = Range::parse(black_box(">=1.2.3-rc.4")).unwrap();
            let version = Version::parse(black_box("1.2.3")).unwrap();

            let _r = range.satisfies(black_box(&version));
        })
    });

    c.bench_function("min version in range", |b| {
        b.iter(|| {
            let range = Range::parse(black_box(">=1.2.3-rc.4")).unwrap();
            let _version = range.min_version().unwrap();
        })
    });
}

criterion_group!(bench, criterion_benchmark);
criterion_main!(bench);
