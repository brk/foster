use argh::FromArgs;
use fasthash::xx;
use human_format::Formatter;
use std::fs;
use std::path::PathBuf;
use std::time::{Duration, Instant};

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
            xx::hash64(file.source().as_bytes()),
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

fn timed<F, R>(dur: &mut Duration, f: F) -> R
where
    F: FnOnce() -> R,
{
    let start = Instant::now();
    let rv = f();
    *dur += start.elapsed();
    rv
}

fn compile_with_rootfile(rootfile: String, incpaths: &[PathBuf]) {
    let mut seenfiles = vec![];
    let mut alltokens = vec![];
    let mut times: FrazCompileTimes = Default::default();

    let compiler_start = Instant::now();

    let mut codemap = timed(&mut times.lexscavenge, || {
        scavenge(rootfile, incpaths, &mut seenfiles, &mut alltokens)
    });

    let parseresult = timed(&mut times.parsing, || {
        fraz::parz::tryparse(alltokens, &mut codemap)
    });

    match parseresult {
        Ok(_ast) => {
            timed(&mut times.codegenprep, || {
                let ss = fraz::tochez::tochez_transunit(&_ast, &codemap);
                fraz::tochez::emit(&ss)
            });
        },
        Err(pe) => eprintln!("parse error: {:?}", pe),
    }
    println!("{:?}", times);

    let mut numlines: usize = 0;
    let mut numbytes: usize = 0;
    for file in seenfiles {
        numlines += file.source().lines().count();
        numbytes += file.source().as_bytes().len();
    }
    let elapsed = compiler_start.elapsed().as_secs_f64();
    println!("# source lines: {}", numlines);
    println!(
        "source lines/second: {}\t\tMB/s: {}",
        Formatter::new().format((numlines as f64) / elapsed),
        Formatter::new().format((numbytes as f64 / 1e6) / elapsed)
    );
}

struct CompilerContext {
    verbose: bool,
}

struct TcEnv {
    uniq: u64,
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

#[derive(Default, Debug)]
struct FrazCompileTimes {
    lexscavenge: Duration,
    parsing: Duration,
    typecheck: Duration,
    monomorph: Duration,
    staticchk: Duration,
    loophdsnk: Duration,
    inlining: Duration,
    closureconv: Duration,
    codegenprep: Duration,
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
