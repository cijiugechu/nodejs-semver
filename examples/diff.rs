use nodejs_semver::{Version, VersionDiff};

fn main() {
    let v1 = Version::parse("1.2.3-rc.4").unwrap();
    let v2 = Version::parse("1.2.3").unwrap();

    let diff = v1.diff(&v2);

    assert_eq!(diff, Some(VersionDiff::Patch));
}
