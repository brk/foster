use argh::FromArgs;
use cityhash::cityhash_1_1_1::city_hash_64;
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
    Compile(FrazCompile),
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

use codemap::CodeMap;
//use codemap::Span;
use codemap_diagnostic::{ColorConfig, Diagnostic, Emitter, Level, SpanLabel, SpanStyle};
use std::collections::HashSet;
use std::collections::VecDeque;
use std::str;
use std::sync::Arc;

fn scavenge(
    rootfile: String,
    incpaths: &[PathBuf],
    seenfiles: &mut Vec<Arc<codemap::File>>,
    alltokens: &mut Vec<fraz::lex::FrazToken>,
) -> CodeMap {
    let mut codemap = CodeMap::new();

    let rootpath = PathBuf::from(&rootfile);
    let mut deq = VecDeque::from([(rootfile, rootpath)]);
    let mut seen = HashSet::new();

    while let Some((name, path)) = deq.pop_front() {
        match fs::read_to_string(path) {
            Err(e) => eprintln!("{:?}", e),
            Ok(contents) => {
                let cmfile = codemap.add_file(name, contents);
                let toks = fraz::lex::tokenize(cmfile.source(), cmfile.span);
                seenfiles.push(cmfile.clone());

                let rawpathtoks = fraz::lex::extract_raw_include_path_toks(&toks);
                for t in rawpathtoks {
                    let toksrc = cmfile.source_slice(t.span);
                    let s = fraz::lex::str_lit_contents(toksrc.as_ref());
                    let sstr = String::from(str::from_utf8(s).expect("already checked"));
                    if !seen.contains(&sstr) {
                        seen.insert(sstr);
                        match fraz::resolve_include_path(s, incpaths) {
                            Some(p) => deq.push_back((String::from(str::from_utf8(s).unwrap()), p)),
                            None => {
                                let mut emitter =
                                    Emitter::stderr(ColorConfig::Always, Some(&codemap));
                                emitter.emit(&[Diagnostic {
                                    level: Level::Error,
                                    message: "unable to find any source code for this path".into(),
                                    code: Some("E484".into()),
                                    spans: vec![SpanLabel {
                                        span: t.span,
                                        style: SpanStyle::Primary,
                                        label: None,
                                    }],
                                }]);
                            }
                        }
                    }
                }
                alltokens.extend(toks)
            }
        }
    }
    codemap
}

fn footprint_with_rootfile(rootfile: String, incpaths: &[PathBuf]) {
    let mut seenfiles = vec![];
    let mut alltokens = vec![];
    let _codemap = scavenge(rootfile, incpaths, &mut seenfiles, &mut alltokens);
    let mut numbytes = 0;
    let mut numlines = 0;
    let mut numfiles = 0;
    for file in seenfiles {
        numfiles += 1;
        numbytes += file.source().as_bytes().len();
        numlines += file.source().lines().count();
        println!(
            "{:016x}   {:>6.1} KB    {}",
            city_hash_64(file.source().as_ref()),
            (file.source().as_bytes().len() as f64) / 1024.0,
            file.name()
        );
    }
    println!(
        "{} files {} lines {} bytes {} tokens",
        numfiles,
        numlines,
        numbytes,
        alltokens.len()
    );
}

fn tokendump_with_rootfile(rootfile: String) {
    match fs::read_to_string(rootfile.clone()) {
        Err(_) => println!("rootfile not found"),
        Ok(contents) => {
            let mut codemap = CodeMap::new();
            let file = codemap.add_file(rootfile, contents);
            let toks = fraz::lex::tokenize(file.source(), file.span);
            for t in toks {
                println!(
                    "{{type: {}, bufidx: {:?}, len: {}, name: {}}}",
                    t.tok,
                    t.span.low(),
                    t.span.len(),
                    fraz::lex::gen::token_name(&t)
                );
            }
        }
    }
}

fn compile_with_rootfile(rootfile: String, incpaths: &[PathBuf]) {
    let mut seenfiles = vec![];
    let mut alltokens = vec![];
    let codemap = scavenge(rootfile, incpaths, &mut seenfiles, &mut alltokens);
    match fraz::parz::tryparse(alltokens, codemap) {
        Ok(_ast) => (),
        Err(pe) => eprintln!("parse error: {:?}", pe),
    }
}

/// Main compiler driver
#[derive(FromArgs, PartialEq, Debug)]
#[argh(subcommand, name = "compile")]
struct FrazCompile {
    /// include paths to search
    #[argh(option, short = 'I')]
    searchpaths: Vec<String>,

    /// root file
    #[argh(positional)]
    rootfile: Option<String>,
}

fn main() {
    let fdo: FrazDriverOpts = argh::from_env();
    match fdo.subcommand {
        FrazSubcommand::Footprint(fp) => match fp.rootfile {
            None => println!("no root file provided"),
            Some(rootfile) => {
                let incpaths: Vec<PathBuf> =
                    fp.searchpaths.into_iter().map(PathBuf::from).collect();
                footprint_with_rootfile(rootfile, &incpaths)
            }
        },
        FrazSubcommand::Tokendump(td) => match td.rootfile {
            None => println!("no root file provided"),
            Some(rootfile) => tokendump_with_rootfile(rootfile),
        },
        FrazSubcommand::Compile(fc) => match fc.rootfile {
            None => println!("no root file provided"),
            Some(rootfile) => {
                let incpaths: Vec<PathBuf> =
                    fc.searchpaths.into_iter().map(PathBuf::from).collect();
                compile_with_rootfile(rootfile, &incpaths);
            }
        },
    }
}
