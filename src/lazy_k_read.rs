use std::str;

use super::lazy_k_core::{PLamExpr, i, s, k, iota, jot};

/// ```
/// use crate::lazy_k::lazy_k_core::{i, k, s, iota, jot};
/// use crate::lazy_k::lazy_k_read::read_lazy_k;
///
/// assert_eq!( read_lazy_k("i"), Ok(i()) );
/// assert_eq!( read_lazy_k("`sk"), Ok(s()*k()) );
/// assert_eq!( read_lazy_k(" ` k i "), Ok(k()*i()) );
/// assert_eq!( read_lazy_k("`ski"), Ok((s()*k())*i()) );
/// assert_eq!( read_lazy_k("`s"), Err("Unexpected EOF".to_string()) );
/// assert_eq!( read_lazy_k(""), Ok(i()) );
/// assert_eq!( read_lazy_k("*i*ii"), Ok(iota()*(iota()*iota())) );
/// assert_eq!( read_lazy_k("11100"), Ok(jot("11100")) );
/// assert_eq!( read_lazy_k("11100*i*ii"),
///                 Ok( jot("11100") * (iota()*(iota()*iota())) ) );
/// ```
pub fn read_lazy_k(s: &str) -> Result<PLamExpr, String> {
    let mut src = s.chars();
    match multi_expr(None, &mut src) {
        Ok( (None, e) ) => Ok(e),
        Ok( (o, _e) )   => panic!("read_lazy_k: {:?}", o),
        Err(msg)        => Err(msg),
    }
}

fn multi_expr(h0: Option<char>, src: &mut str::Chars<'_>)
                    -> Result<(Option<char>, PLamExpr), String> {
    let mut sum = Vec::new();
    let mut h = h0;
    loop {
        match expr(h, src) {
            Ok( (n, res) ) => {
                sum.push(res);
                h = n;
                match h {
                    Some(c) if c == ')' => break,
                    _ => (),
                }
            },
            Err(msg) if msg == "RightParen" => {
                h = Some(')');
                break
            }
            Err(msg) if msg == "EOF" => break,
            Err(msg)                 => return Err(msg),
        }
    }
    let mut sum_iter = sum.iter();
    match sum_iter.next() {
        None      => Ok( (h, i()) ),     // Epsilon
        Some(ini) =>
            Ok( (h, sum_iter.fold(ini.clone(), |acc, e| acc * e.clone())) ),
    }
}

fn expr(h0: Option<char>, src: &mut str::Chars<'_>)
                    -> Result<(Option<char>, PLamExpr), String> {
    let mut h = h0;
    if h == None {
        h = src.next();
    }
    loop {
        let r = match h {
            Some('i') => Ok( (None, i()) ),
            Some(c) if is_lazy_k_char(c) => expr_tail(h, src),
            Some(_)   => {
                h = src.next();
                continue;
            }
            None      => Err("EOF".to_string()),
        };
        return r;
    }
}

fn iota_expr(h0: Option<char>, src: &mut str::Chars<'_>)
                    -> Result<(Option<char>, PLamExpr), String> {
    let mut h = h0;
    if h == None {
        h = src.next();
    }
    loop {
        let r = match h {
            Some('i') => Ok( (None, iota()) ),
            Some(c) if is_lazy_k_char(c) => expr_tail(h, src),
            Some(_)   => {
                h = src.next();
                continue;
            }
            None => Err("EOF".to_string()),
        };
        return r;
    }
}

fn expr_tail(h0: Option<char>, src: &mut str::Chars<'_>)
                    -> Result<(Option<char>, PLamExpr), String> {
    let mut h = h0;
    loop {
        let r = match h {
            Some('I') => Ok( (None, i()) ),
            Some('K') => Ok( (None, k()) ),
            Some('k') => Ok( (None, k()) ),
            Some('S') => Ok( (None, s()) ),
            Some('s') => Ok( (None, s()) ),
            Some('`') => app(expr, src),
            Some('(') => match multi_expr(None, src) {
                Err(msg) if msg == "RightParen" => {
                    Ok( (None, i()) )  // epsilon()
                }
                Err(msg) => Err(msg),
                Ok( (Some(c), e) ) if c == ')' => Ok( (None, e) ),
                Ok( (_, e) ) => loop {
                    match src.next() {
                        Some(')') => return Ok( (None, e) ),
                        Some(c) if is_lazy_k_char(c) => panic!("expr_tail:" ),
                        Some(_) => continue,
                        None => return Err("lack of right paren 2".to_string()),
                    }
                }
            }
            Some(')') => Err("RightParen".to_string()),
            Some('*') => app(iota_expr, src),
            Some('0') => jot_expr(h, src),
            Some('1') => jot_expr(h, src),
            Some(_) => {
                h = src.next();
                continue;
            }
            None => Err("EOF".to_string()),
        };
        return r
    }
}

fn app(exp: fn(Option<char>, &mut str::Chars<'_>)
                                -> Result<(Option<char>, PLamExpr), String>,
        src: &mut str::Chars<'_>) -> Result<(Option<char>, PLamExpr), String> {
    let f = exp(None, src);
    match f {
        Ok( (n, fs) ) => {
            let o = exp(n, src);
            match o {
                Ok( (n, os) ) => Ok( (n, fs * os) ),
                Err(_) => Err("Unexpected EOF".to_string()),
            }
        },
        Err(_) => Err("Unexpected EOF".to_string()),
    }
}

fn jot_expr(h0: Option<char>, src: &mut str::Chars<'_>)
                    -> Result<(Option<char>, PLamExpr), String> {
    let mut h = h0;
    let mut je = String::new();
    loop {
        match h {
            Some('0') => je.push('0'),
            Some('1') => je.push('1'),
            Some(c) if is_lazy_k_char(c) => break,
            Some(_) => (),
            None    => break,
        }
        h = src.next();
    }
    return Ok( (h, jot(&je)) );
}

fn is_lazy_k_char(c: char) -> bool {
    c == 'I' || c == 'i' || c == 'S' || c == 's' || c == 'K' || c == 'k'
    || c == '(' || c == ')'
    || c == '`' || c == '*'
    || c == '0' || c == '1'
}

