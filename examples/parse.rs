use nodejs_semver::Version;

fn main() {
    let v = Version::parse("1.2.3-rc.4").unwrap();
    println!("{}", v);
}
