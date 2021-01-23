use std::char;

use super::lazy_k_core::*;

pub fn exec_lazy_k2(prog_data: PLamExpr) -> Vec<u32> {
    let mut cnt = 0;
    let lk2 = apply_fully(100_000_000, prog_data, PLamExpr::beta_red_cc, move |x| {
        cnt += 1;
        if cnt % 10_000 == 0 {
            println!("cnt = {}, len = {}", cnt, x.len());
        }
        if x.len() > 10_000_000 {
            Some("Space Limit".to_string())
        } else {
            None
        }
    });
    let mut lk = match lk2 {
        Ok((res, remain)) => res,
        Err((_, remain, msg)) => {
            println!("Give up! : {} : {} / 100_000_000", msg, remain);
            return vec![256];
        }
    };
    let mut v = Vec::new();
    loop {
        if is_nil(&lk) {
            break;
        }
        let car = s() * i() * (k() * k());
        match (car * lk.clone()).get_num() {
            Some(n) if n < 256 => {
                println!("calculating...: {}", n);
                v.push(n);
            }
            _ => break,
        }
        let cdr = s() * i() * (k() * (k() * i()));
        lk = cdr * lk;
    }
    v
}

pub fn exec_lazy_k(prog_data: PLamExpr) -> Vec<u32> {
    let mut v = Vec::new();
    let mut lk = prog_data;
    loop {
        if is_nil(&lk) {
            println!("output: NULL terminated");
            break;
        }
        let car = s() * i() * (k() * k());
        match (car * lk.clone()).get_num_n(100_000_000) {
            Ok((n, c)) if n < 256 => {
                println!("calculating[{}] : '{}' ({:>3} = 0x{:02x}): c={}",
                            v.len(), char::from_u32(n).unwrap(), n, n, c);
                v.push(n);
            }
            Ok((n, c)) => {
                println!("output: over 255: {}, c={}", n, c);
                break;
            }
            Err(msg) => {
                println!("output: Non-number: {}", msg);
                break;
            }
        }
        let cdr = s() * i() * (k() * (k() * i()));
        lk = cdr * lk;
    }
    v
}

/// ```
/// use crate::lazy_k::lazy_k_core::{la, v};
/// use crate::lazy_k::lazy_k_interpreter::{is_nil};
/// let nil = la( la( v(1) ) );
/// //assert_eq!( is_nil(&nil), true );
/// ```
pub fn is_nil(e: &PLamExpr) -> bool {
    let aux =  e.clone() * (k() * ( k() * (k() * nm("false")))) * nm("true");
    match ChNumEval::new(aux).eval_cc() {
        Some(r) => match r.get_lam2() {
            LamExpr::Nm { name } if **name == "true".to_string() => true,
            _ => false,
        },
        _ => false,
    }
}

