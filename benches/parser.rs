use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use nodejs_semver::{Range, Version};

const VERSION_CASES: &[(&str, &str)] = &[
    ("plain", "1.2.3"),
    ("v_prefix", "v1.2.3"),
    ("prerelease", "1.2.3-rc.4"),
    ("build", "1.2.3+build.7"),
    ("prerelease_build", "1.2.3-rc.4+build.7"),
];

const RANGE_CASES: &[(&str, &str)] = &[
    ("exact", "1.2.3"),
    ("comparator", ">=1.2.3-rc.4"),
    ("and", ">=1.2.3 <2.0.0"),
    ("or", ">=18 <20 || >=22"),
    ("wildcard", "1.x.x"),
    ("hyphen_wildcard", "1.0.0 - 1.0.x"),
    ("tilde", "~1.2.3"),
    ("tilde_gt", "~>3.2.1"),
    ("prerelease_bounds", ">=3.3.0-beta.1 <3.4.0-beta.3"),
];

const SATISFIES_CASES: &[(&str, &str, &str)] = &[
    ("exact_true", "1.2.3", "1.2.3"),
    ("comparator_true", ">=1.2.3-rc.4", "1.2.3"),
    ("and_false", ">=1.2.3 <2.0.0", "2.0.0"),
    ("or_true", ">=18 <20 || >=22", "22.0.0"),
    ("wildcard_true", "1.x.x", "1.2.3"),
    ("hyphen_wildcard_true", "1.0.0 - 1.0.x", "1.0.1"),
    (
        "prerelease_bounds_false",
        ">=3.3.0-beta.1 <3.4.0-beta.3",
        "3.4.5",
    ),
    (
        "prerelease_matching_core_true",
        ">=1.2.3-alpha <2.0.0",
        "1.2.3-beta",
    ),
    (
        "prerelease_non_matching_core_false",
        ">=1.2.3-alpha <2.0.0",
        "1.2.4-beta",
    ),
];

const FILTER_VERSIONS: &[&str] = &[
    "17.9.1",
    "18.19.0",
    "19.0.0",
    "20.0.0",
    "20.1.0",
    "21.9.0",
    "22.0.0",
    "22.1.0-beta.1",
    "v22.2.0",
    "23.0.0",
    "latest",
    "not-a-version",
];

// Sampled from pnpm-lock.yaml files in Next.js, Nuxt, Vue core, and Prisma.
const PACKAGE_MANAGER_VERSION_CORPUS: &[&str] = &[
    "1.10.1",
    "7.25.9",
    "0.41.0",
    "0.5.3",
    "1.1.1",
    "22.2.3",
    "1.1.1",
    "8.6.0",
    "3.0.3",
    "9.0.8",
    "8.14.0",
    "2.0.3",
    "3.1.0",
    "1.0.4",
    "3.1.8",
    "7.0.10",
    "4.2.0",
    "2.12.1",
    "3.5.1",
    "1.0.0",
    "1.0.0",
    "3.0.5",
    "3.1.0",
    "0.4.1",
    "4.2.1",
    "12.3.0",
    "1.6.0",
    "3.0.3",
    "2.1.0",
    "4.1.0",
    "4.0.2",
    "0.0.0-experimental-b1786c31-20260618",
    "2.0.2",
    "0.0.1",
    "0.5.1",
    "2.1.0",
    "1.1.0",
    "9.1.3",
    "5.1.0",
    "7.25.9",
    "1.5.0",
    "0.5.3",
    "0.21.6",
    "1.1.0",
    "7.9.1",
    "4.0.8",
    "2.0.5",
    "2.8.0",
    "5.0.0",
    "2.6.9",
    "6.10.2",
    "2.3.3",
    "5.0.1",
    "29.7.0",
    "6.0.0",
    "2.0.1",
    "0.8.3",
    "4.2.0",
    "2.0.7",
    "1.0.2",
    "1.17.0",
    "2.1.0",
    "4.2.1",
    "7.29.7",
    "0.15.0",
    "0.133.0",
    "6.0.3",
    "4.6.0",
    "1.12.2",
    "3.17.0",
    "14.0.3",
    "5.22.0",
    "0.2.2",
    "8.3.1",
    "1.32.0",
    "3.1.5",
    "2.1.0",
    "2.1.0",
    "1.11.1",
    "0.3.8",
    "9.3.4",
    "0.28.1",
    "0.132.0",
    "0.134.0",
    "4.1.0",
    "4.1.6",
    "1.9.3",
    "0.3.0",
    "1.32.0",
    "10.2.0",
    "3.0.0",
    "7.5.15",
    "5.1.11",
    "1.0.3",
    "1.11.1",
    "1.1.0",
    "4.0.0",
    "1.61.0",
    "3.1.0",
    "1.2.1",
    "8.61.0",
    "6.0.2",
    "6.0.0",
    "7.18.6",
    "0.25.4",
    "0.1.3",
    "1.10.2",
    "0.6.0",
    "1.12.1",
    "3.1.0",
    "10.0.0",
    "3.0.1",
    "1.0.6",
    "6.0.3",
    "3.3.11",
    "5.0.0",
    "2.0.0",
    "1.2.3",
    "7.0.0",
    "1.20250718.0",
    "0.25.5",
    "0.5.22",
    "6.0.0",
    "6.12.6",
    "30.0.0-alpha.6",
    "1.0.0-beta.2",
    "0.1.6-no-external-plugins",
    "7.21.0-placeholder-for-preset-env.2",
];

const PACKAGE_MANAGER_SPECIFIER_CORPUS: &[&str] = &[
    "1.10.1",
    "^3",
    "workspace:*",
    "1.5.3",
    "1.7.1",
    "5.6.0",
    "workspace:*",
    "5.5.3",
    "1.2.1",
    "15.2.2",
    "1.61.0",
    "npm:react-dom@19.3.0-canary-b1786c31-20260618",
    "1.1.2",
    "3.2.7",
    "8.2.3",
    "^0.4.6",
    "^4.1.9",
    "^10.9.1",
    "workspace:*",
    "5.0.1",
    "2.4.2",
    "5.0.1",
    "9.37.0",
    "npm:react-dom@19.3.0-canary-b1786c31-20260618",
    "7.26.3",
    "6.0.0",
    "1.6.7",
    "7.0.6",
    "0.5.0",
    "1.7.1",
    "2.0.0",
    "1.1.2",
    "1.5.1",
    "1.0.0",
    "4.1.1",
    "4.0.1",
    "0.12.0",
    "5.0.0",
    "5.27.0",
    "npm:webpack-sources@3.2.3",
    "17.0.0",
    "10.0.0",
    "^29.1.0",
    "20.17.6",
    "^1.9.6",
    "workspace:*",
    "workspace:*",
    "2.2.1",
    "20.10.2",
    "0.3.0",
    "3.5.35",
    "^2.0.11",
    "6.1.1",
    "^2.0.5",
    "^4.1.0",
    "4.1.8",
    "^3.4.2",
    "^1.8.2",
    "^4.1.0",
    "^5.1.0",
    "0.2.3",
    "^2.7.0",
    "^0.3.0",
    "^7.0.0",
    "workspace:*",
    "0.2.0",
    "7.0.1",
    "66.7.0",
    "workspace:*",
    "^0.3.0",
    "10.5.0",
    "^10.5.0",
    "^1.8.2",
    "^0.2.17",
    "4.7.0",
    "^1.6.4",
    "workspace:*",
    "5.9.3",
    "^16.0.3",
    "^0.28.0",
    "^3.8.4",
    "^2.8.1",
    "workspace:*",
    "workspace:*",
    "10.1.0",
    "workspace:*",
    "catalog:",
    "7.0.5",
    "6.0.3",
    "1.0.5",
    "npm:prettier@2.8.8",
    "4.0.18",
    "3.4.5",
    "^1.19.0",
    "workspace:*",
    "8.11.11",
    "workspace:*",
    "0.2.37",
    "5.1.1",
    "0.15.0",
    "workspace:*",
    "0.206.0",
    "workspace:*",
    "workspace:*",
    "0.2.37",
    "1.2.2",
    "4.17.2",
    "0.31.2",
    "workspace:*",
    "2.1.4",
    "2.0.6",
    "7.8.0-6.3c6e192761c0362d496ed980de936e2f3cebcd3a",
    "0.0.33",
    "5.4.5",
    "workspace:*",
    "4.6.2",
    "4.1.5",
    "8.0.1",
    "workspace:*",
    "3.4.5",
    "workspace:*",
    "1.20.6",
    "3.1.0",
    "4.0.0",
    "2.4.2",
    "4.0.0",
    "5.4.5",
    "^4.12.23",
];

fn bench_version_parse(c: &mut Criterion) {
    let mut group = c.benchmark_group("version_parse");

    for (name, input) in VERSION_CASES {
        group.bench_with_input(BenchmarkId::from_parameter(name), input, |b, input| {
            b.iter(|| black_box(Version::parse(black_box(*input)).unwrap()));
        });
    }

    group.finish();
}

fn bench_range_parse(c: &mut Criterion) {
    let mut group = c.benchmark_group("range_parse");

    for (name, input) in RANGE_CASES {
        group.bench_with_input(BenchmarkId::from_parameter(name), input, |b, input| {
            b.iter(|| black_box(Range::parse(black_box(*input)).unwrap()));
        });
    }

    group.finish();
}

fn bench_satisfies(c: &mut Criterion) {
    let mut group = c.benchmark_group("satisfies_parsed");

    for (name, range, version) in SATISFIES_CASES {
        let range = Range::parse(range).unwrap();
        let version = Version::parse(version).unwrap();

        group.bench_function(BenchmarkId::from_parameter(name), |b| {
            b.iter(|| black_box(range.satisfies(black_box(&version))));
        });
    }

    group.finish();
}

fn bench_parse_and_satisfies(c: &mut Criterion) {
    let mut group = c.benchmark_group("parse_and_satisfies");

    for (name, range, version) in SATISFIES_CASES {
        group.bench_function(BenchmarkId::from_parameter(name), |b| {
            b.iter(|| {
                let range = Range::parse(black_box(*range)).unwrap();
                let version = Version::parse(black_box(*version)).unwrap();
                black_box(range.satisfies(black_box(&version)))
            });
        });
    }

    group.finish();
}

fn bench_filter_version_strings(c: &mut Criterion) {
    let mut group = c.benchmark_group("filter_version_strings");
    group.throughput(Throughput::Elements(FILTER_VERSIONS.len() as u64));

    let range = Range::parse(">=18 <20 || >=22").unwrap();

    group.bench_function("current_api_parse_each_candidate", |b| {
        b.iter(|| {
            let mut count = 0usize;

            for version in black_box(FILTER_VERSIONS) {
                if Version::parse(black_box(*version))
                    .is_ok_and(|version| range.satisfies(black_box(&version)))
                {
                    count += 1;
                }
            }

            black_box(count)
        });
    });

    group.finish();
}

fn bench_package_manager_corpus(c: &mut Criterion) {
    let mut group = c.benchmark_group("package_manager_corpus");

    group.throughput(Throughput::Elements(
        PACKAGE_MANAGER_VERSION_CORPUS.len() as u64
    ));
    group.bench_function("resolved_versions_version_parse", |b| {
        b.iter(|| {
            let mut count = 0usize;

            for version in black_box(PACKAGE_MANAGER_VERSION_CORPUS) {
                if Version::parse(black_box(*version)).is_ok() {
                    count += 1;
                }
            }

            black_box(count)
        });
    });

    group.throughput(Throughput::Elements(
        PACKAGE_MANAGER_SPECIFIER_CORPUS.len() as u64
    ));
    group.bench_function("specifiers_version_parse_attempt", |b| {
        b.iter(|| {
            let mut count = 0usize;

            for specifier in black_box(PACKAGE_MANAGER_SPECIFIER_CORPUS) {
                if Version::parse(black_box(*specifier)).is_ok() {
                    count += 1;
                }
            }

            black_box(count)
        });
    });

    group.bench_function("specifiers_range_parse_attempt", |b| {
        b.iter(|| {
            let mut count = 0usize;

            for specifier in black_box(PACKAGE_MANAGER_SPECIFIER_CORPUS) {
                if Range::parse(black_box(*specifier)).is_ok() {
                    count += 1;
                }
            }

            black_box(count)
        });
    });

    group.bench_function("specifiers_version_then_range_parse", |b| {
        b.iter(|| {
            let mut count = 0usize;

            for specifier in black_box(PACKAGE_MANAGER_SPECIFIER_CORPUS) {
                if Version::parse(black_box(*specifier)).is_ok()
                    || Range::parse(black_box(*specifier)).is_ok()
                {
                    count += 1;
                }
            }

            black_box(count)
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_version_parse,
    bench_range_parse,
    bench_satisfies,
    bench_parse_and_satisfies,
    bench_filter_version_strings,
    bench_package_manager_corpus,
);
criterion_main!(benches);
