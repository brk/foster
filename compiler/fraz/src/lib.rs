pub mod lex;

use std::ffi::OsStr;
use std::path::Path;
use std::path::PathBuf;
use std::str;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        let result = 2 + 2;
        assert_eq!(result, 4);
    }
}

pub fn resolve_include_path(raw: &[u8], search_paths: &Vec<PathBuf>) -> Option<PathBuf> {
    let rawpath = Path::new(OsStr::new(str::from_utf8(raw).unwrap()));
    for search in search_paths {
        // Try foo/bar.foster
        let mut direct = search.join(rawpath);
        direct.set_extension("foster");
        if direct.is_file() {
            return Some(direct);
        }

        // Try foo/bar/bar.foster
        direct = search.join(rawpath).join(rawpath.file_stem()?);
        direct.set_extension("foster");
        if direct.is_file() {
            return Some(direct);
        }
    }
    return None;
}
