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
    incpaths: &Vec<PathBuf>,
    seenfiles: &mut Vec<Arc<codemap::File>>,
) -> CodeMap {
    let mut codemap = CodeMap::new();

    let rootpath = PathBuf::from(&rootfile);
    let mut deq = VecDeque::from([(rootfile, rootpath)]);
    let mut seen = HashSet::new();
    let mut baseidx = 0;

    while let Some((name, path)) = deq.pop_front() {
        match fs::read_to_string(path) {
            Err(e) => eprintln!("{:?}", e),
            Ok(contents) => {
                let toks = fraz::lex::tokenize(&contents, baseidx);
                let srclen = contents.len() as i32;
                let cmfile = codemap.add_file(name, contents);
                seenfiles.push(cmfile.clone());

                let rawpathtoks = fraz::lex::extract_raw_include_path_toks(&toks);
                for t in rawpathtoks {
                    // Note: token offsets are pre-globalized, but subspan()
                    // expects localized offsets, so we re-subtract baseidx.
                    let tokoff = t.off - baseidx;
                    let tokspan = cmfile.span.subspan(tokoff as u64, (tokoff + t.len) as u64);
                    let toksrc = cmfile.source_slice(tokspan);
                    let s = fraz::lex::str_lit_contents(toksrc.as_ref());
                    let sstr = String::from(str::from_utf8(s).expect("already checked"));
                    if !seen.contains(&sstr) {
                        seen.insert(sstr);
                        match fraz::resolve_include_path(s, &incpaths) {
                            Some(p) => deq.push_back((String::from(str::from_utf8(s).unwrap()), p)),
                            None => {
                                let mut emitter =
                                    Emitter::stderr(ColorConfig::Always, Some(&codemap));
                                emitter.emit(&[Diagnostic {
                                    level: Level::Error,
                                    message: "unable to find any source code for this path".into(),
                                    code: Some("E404".into()),
                                    spans: vec![SpanLabel {
                                        span: tokspan,
                                        style: SpanStyle::Primary,
                                        label: None,
                                    }],
                                }]);
                            }
                        }
                    }
                }
                baseidx += srclen;
            }
        }
    }
    return codemap;
}

fn footprint_with_rootfile(rootfile: String, incpaths: &Vec<PathBuf>) {
    let mut seenfiles = vec![];
    let _codemap = scavenge(rootfile, incpaths, &mut seenfiles);
    let mut numbytes = 0;
    let mut numlines = 0;
    let mut numfiles = 0;
    for file in seenfiles {
        numfiles += 1;
        numbytes += file.source().as_bytes().len();
        numlines += file.source().lines().count();
        println!(
            "{:016x} {}",
            city_hash_64(file.source().as_ref()),
            file.name()
        );
    }
    println!("{} files {} lines {} bytes", numfiles, numlines, numbytes);
}

fn tokendump_with_rootfile(rootfile: String) {
    match fs::read_to_string(rootfile) {
        Err(_) => println!("rootfile not found"),
        Ok(mut contents) => {
            let toks = fraz::lex::tokenize(&mut contents, 0);
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
