use std::process::Command;
use std::env;
use std::fs::File;

fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();
    let parser_h = File::create(format!("{}/parser.h", out_dir)).unwrap();

    Command::new("python3")
        .args(&["extract_token_defs.py", "src/parz.rs"])
        .stdout(parser_h)
        .status().expect("failed to execute python3");

    let toknums_rs = File::create(format!("{}/toknums.rs", out_dir)).unwrap();
    Command::new("python3")
        .args(&["extract_token_defs.py", "src/parz.rs", "--mode=rustconst"])
        .stdout(toknums_rs)
        .status().expect("failed to execute python3");

    let tokcvt_rs = File::create(format!("{}/tokcvt.rs", out_dir)).unwrap();
    Command::new("python3")
        .args(&["extract_token_defs.py", "src/parz.rs", "--mode=rustconvert"])
        .stdout(tokcvt_rs)
        .status().expect("failed to execute python3");

    cc::Build::new()
        .file("gen/fosterlexer.c")
        .include(out_dir)
        .compile("fosterlexer");
    
    println!("cargo:rerun-if-changed=extract_token_defs.py");
    println!("cargo:rerun-if-changed=src/parz.rs");
    println!("cargo:rerun-if-changed=gen/fosterlexer.c");
    println!("cargo:rerun-if-changed=build.rs");
}
