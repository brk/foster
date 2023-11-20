use argh::FromArgs;
use std::fs;

/// Fraz driver options struct
#[derive(FromArgs)]
struct FrazDriverOpts {
    /// root file
    #[argh(positional)]
    rootfile: Option<String>,
}

fn run_with_rootfile(rootfile: String) {
    match fs::read_to_string(rootfile) {
        Err(_) => println!("rootfile not found"),
        Ok(mut contents) => {
            println!("rootfile found with len {}", contents.len());
            let toks = fraz::lex::tokenize(&mut contents);
            println!("lexed {} tokens", toks.len())
        }
    }
}

fn main() {
    let fdo: FrazDriverOpts = argh::from_env();
    match fdo.rootfile {
        None => println!("no root file provided"),
        Some(rootfile) => run_with_rootfile(rootfile),
    }
}
