use nodejs_semver::Version;
use serde::Serialize;

#[derive(Serialize)]
struct MyVersion {
    version: Version,
    info: String,
}

fn main() {
    let v = "3.4.5-rc.1".parse::<Version>().unwrap();
    let my_version = MyVersion {
        version: v,
        info: "info".to_string(),
    };

    println!("{}", serde_json::to_string(&my_version).unwrap());
}
