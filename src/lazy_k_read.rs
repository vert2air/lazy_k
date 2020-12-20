use std::str;

use super::lazy_k_core::{PLamExpr, i, s, k};

/// ```
/// assert_eq!( read_unlam('), )
/// ```
pub fn read_unlam(src: &str) -> Result<PLamExpr, String> {
    aux(&mut src.chars())
}

fn aux(src: &mut str::Chars<'_>) -> Result<PLamExpr, String> {
    loop {
        let r = match src.next() {
            Some('`') => {
                let f = aux(src);
                match f {
                    Ok(fs) => {
                        let o = aux(src);
                        match o {
                            Ok(os) => Ok(fs * os),
                            Err(_) => o,
                        }
                    },
                    Err(_) => f,
                }
            }
            Some('i') => Ok(i()),
            Some('s') => Ok(s()),
            Some('k') => Ok(k()),
            Some(_) => continue,
            None => Err("EOF".to_string()),
        };
        return r
    }
}

