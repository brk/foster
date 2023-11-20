#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        let result = 2 + 2;
        assert_eq!(result, 4);
    }
}

pub mod lex {

    #[allow(dead_code)]
    pub struct FrazToken {
        tok: i32,
        len: i32,
    }

    extern "C" {
        fn scan_token_start(
            s: *mut FLScanner,
            t: *mut FLToken,
            buff_end: libc::c_int,
            yych: *mut libc::c_uchar,
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
        pub buf: *mut u8,
        pub num_errors: libc::c_int,
        pub ptr: libc::c_int,
        pub cur: libc::c_int,
        pub top: libc::c_int,
        pub commentdepth: libc::c_int,
        pub line: libc::c_int,
        pub linepos: libc::c_int,
        pub linepos_prev: libc::c_int,
    }

    pub fn tokenize(contents: &mut String) -> Vec<FrazToken> {
        let mut t = FLToken {
            tok: 0,
            line: 0,
            col: 0,
            endline: 0,
            endcol: 0,
        };
        let mut s = FLScanner {
            buf: contents.as_mut_ptr(),
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
        let mut yych: libc::c_uchar = 0;
        const FINI: libc::c_int = 1;
        let mut prevcur = s.cur;

        loop {
            unsafe { scan_token_start(&mut s, &mut t, len, &mut yych) }
            if t.tok == FINI {
                break;
            }
            toks.push(FrazToken {
                tok: t.tok,
                len: s.cur - prevcur,
            });
            prevcur = s.cur;
        }
        return toks;
    }
}
