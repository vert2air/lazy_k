use std::str;

use super::lazy_k_core::{PLamExpr, i, s, k};

/// ```
/// use crate::lazy_k::lazy_k_core::{i, k, s};
/// use crate::lazy_k::lazy_k_read::read_unlam;
///
/// assert_eq!( read_unlam("i"), Ok(i()) );
/// assert_eq!( read_unlam("`sk"), Ok(s()*k()) );
/// assert_eq!( read_unlam(" ` k i "), Ok(k()*i()) );
/// assert_eq!( read_unlam("`ski"), Err("Extra string: i".to_string()) );
/// assert_eq!( read_unlam("`s"), Err("Unexpected EOF".to_string()) );
/// ```
pub fn read_unlam(s: &str) -> Result<PLamExpr, String> {
    let mut src = s.chars();
    let lam = aux(&mut src);
    let rem: String = src.filter(|c| {
            *c == '`' || *c == 's' || *c == 'k' || *c == 'i'
    }).collect();
    match lam {
        Ok(_) if rem.len() == 0 => lam,
        Ok(_) => Err(format!("Extra string: {}", rem)),
        Err(_) => Err(format!("Unexpected EOF")),
    }
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

