fn main() {
    cc::Build::new()
        .file("gen/fosterlexer.c")
        .compile("fosterlexer");
    //println!("cargo:rerun-if-changed=gen/fosterlexer.c");
    //println!("cargo:rustc-link-lib=libfosterlexer.a");
}
