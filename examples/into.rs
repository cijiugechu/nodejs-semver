use nodejs_semver::Version;

fn main() {
    let v: Version = (1, 2, 3).into();
    println!("{}", v);
}
