use nodejs_semver::{Range, Version};

fn main() {
    let versions: Vec<_> = vec!["1.2.3", "1.2.4", "1.2.5", "1.2.6"]
        .iter()
        .map(|s| Version::parse(s).unwrap())
        .collect();
    let range = Range::parse("~1.2.3").unwrap();

    let result = range.max_satisfying(&versions);

    assert_eq!(result, Some(&Version::parse("1.2.6").unwrap()));
}
