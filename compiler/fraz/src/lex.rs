#[allow(dead_code)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct FrazToken {
    pub tok: i32,
    pub span: codemap::Span,
}

extern "C" {
    fn scan_token_start(
        s: *mut FLScanner,
        t: *mut FLToken,
        buff_end: libc::c_int,
    );
}

#[derive(Copy, Clone)]
#[repr(C)]
pub struct FLToken {
    pub tok: libc::c_int,
    pub line: libc::c_int,
    pub col: libc::c_int,
    pub endline: libc::c_int,
    pub endcol: libc::c_int,
}

#[derive(Copy, Clone)]
#[repr(C)]
pub struct FLScanner {
    pub buf: *const u8,
    pub num_errors: libc::c_int,
    pub ptr: libc::c_int,
    pub cur: libc::c_int,
    pub top: libc::c_int,
    pub commentdepth: libc::c_int,
    pub line: libc::c_int,
    pub linepos: libc::c_int,
    pub linepos_prev: libc::c_int,
}

pub mod gen {
    include!(concat!(env!("OUT_DIR"), "/toknums.rs"));
}

pub fn tokenize(contents: &str, filespan: codemap::Span) -> Vec<FrazToken> {
    let mut t = FLToken {
        tok: 0,
        line: 0,
        col: 0,
        endline: 0,
        endcol: 0,
    };
    let mut s = FLScanner {
        buf: contents.as_ptr(),
        num_errors: 0,
        ptr: 0,
        cur: 0,
        top: 0,
        commentdepth: 0,
        line: 0,
        linepos: 0,
        linepos_prev: 0,
    };
    let mut toks = vec![];
    let len: libc::c_int = contents.len().try_into().unwrap();
    let mut prevcur = s.cur;

    loop {
        unsafe { scan_token_start(&mut s, &mut t, len) }
        if t.tok == gen::FINI {
            break;
        }
        toks.push(FrazToken {
            tok: t.tok,
            span: filespan.subspan(prevcur as u64, s.cur as u64),
        });
        prevcur = s.cur;
    }
    toks
}

fn nonwhite(it: &mut std::slice::Iter<FrazToken>) -> Option<FrazToken> {
    loop {
        let tok = it.next()?;
        if tok.tok < 0 { continue }
        return Some(*tok);
    }
}

pub fn extract_raw_include_path_toks(toks: &[FrazToken]) -> Vec<FrazToken> {
    let mut it = toks.iter();
    let mut rawpaths = vec![];
    loop {
        match nonwhite(&mut it) {
            None => break,
            Some(tok) if tok.tok == gen::INCLUDE => {
                let _name = nonwhite(&mut it);
                let _path = nonwhite(&mut it);
                let _semi = nonwhite(&mut it);
                match _path {
                    Some(path) if path.tok == gen::STR => {
                        rawpaths.push(path);
                    },
                    _ => continue
                }
            },
            _ => break,
        }
    }
    rawpaths
}

/// Returns a slice of the quote-mark-less contents of the given string literal
pub fn str_lit_contents(s: &[u8]) -> &[u8] {
    let mut firstquote = 0;
    while let Some(c) = s.get(firstquote) {
        if *c == b'\'' || *c == b'"' { break; }
        firstquote += 1
    }
    let mut numquotes = 0;
    while let Some(c) = s.get(firstquote + numquotes) {
        if *c == b'\'' || *c == b'"' { numquotes += 1; }
        else { break; }
    }
    &s[firstquote + numquotes .. s.len() - numquotes]
}