use argh::FromArgs;
use std::fs;
use std::path::PathBuf;

/// Fraz driver options struct
#[derive(FromArgs, PartialEq, Debug)]
struct FrazDriverOpts {
    #[argh(subcommand)]
    subcommand: FrazSubcommand,
}

/// Fraz driver subcommand wrapper
#[derive(FromArgs, PartialEq, Debug)]
#[argh(subcommand)]
enum FrazSubcommand {
    Footprint(FrazFootprint),
    Tokendump(FrazTokendump),
}

/// A footprint measures the amount of code the compiler will process
#[derive(FromArgs, PartialEq, Debug)]
#[argh(subcommand, name = "footprint")]
struct FrazFootprint {
    /// shallow means only consider the root file
    #[argh(option)]
    shallow: Option<bool>,

    /// include paths to search
    #[argh(option, short = 'I')]
    searchpaths: Vec<String>,

    /// root file
    #[argh(positional)]
    rootfile: Option<String>,
}

/// Print the raw token information from the root file
#[derive(FromArgs, PartialEq, Debug)]
#[argh(subcommand, name = "tokendump")]
struct FrazTokendump {
    /// root file
    #[argh(positional)]
    rootfile: Option<String>,
}

use std::str;

fn footprint_with_rootfile(rootfile: String, incpaths: &Vec<PathBuf>) {
    match fs::read_to_string(rootfile) {
        Err(_) => println!("rootfile not found"),
        Ok(mut contents) => {
            println!("rootfile found with len {}", contents.len());
            let toks = fraz::lex::tokenize(&mut contents);
            let rawpaths = fraz::lex::extract_raw_include_paths(contents.as_ref(), &toks);
            println!("lexed {} tokens", toks.len());
            for s in rawpaths {
                println!(
                    "\timp: {:?} => {:?}",
                    str::from_utf8(s),
                    fraz::resolve_include_path(s, &incpaths)
                );
            }
        }
    }
}

fn tokendump_with_rootfile(rootfile: String) {
    match fs::read_to_string(rootfile) {
        Err(_) => println!("rootfile not found"),
        Ok(mut contents) => {
            let toks = fraz::lex::tokenize(&mut contents);
            for t in toks {
                println!("{{type: {}, bufidx: {}, len: {}}}", t.tok, t.off, t.len);
            }
        }
    }
}

fn main() {
    let fdo: FrazDriverOpts = argh::from_env();
    match fdo.subcommand {
        FrazSubcommand::Footprint(fp) => match fp.rootfile {
            None => println!("no root file provided"),
            Some(rootfile) => {
                let incpaths = fp
                    .searchpaths
                    .into_iter()
                    .map(|s| PathBuf::from(s))
                    .collect();
                footprint_with_rootfile(rootfile, &incpaths)
            }
        },
        FrazSubcommand::Tokendump(td) => match td.rootfile {
            None => println!("no root file provided"),
            Some(rootfile) => tokendump_with_rootfile(rootfile),
        },
    }
}
