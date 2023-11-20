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

    let fosterlexer_c = format!("{}/fosterlexer.c", out_dir);
    Command::new("re2c")
        .args(&["src/fosterlexer.re", "--input", "custom", "-8", "-W", "-o", &fosterlexer_c])
        .status().expect("failed to execute re2c");

    cc::Build::new()
        .file(fosterlexer_c)
        .include(out_dir)
        .include("inc")
        .compile("fosterlexer");
    
    println!("cargo:rerun-if-changed=extract_token_defs.py");
    println!("cargo:rerun-if-changed=src/parz.rs");
    println!("cargo:rerun-if-changed=src/fosterlexer.re");
    println!("cargo:rerun-if-changed=build.rs");
}
