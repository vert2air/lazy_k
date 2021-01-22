use super::lazy_k_core::*;

pub fn exec_lazy_k(prog_data: PLamExpr) -> Vec<u32> {
    let lk2 = apply_fully(100_000_000, prog_data, PLamExpr::beta_red_cc, |x|
        if x.len() > 10_000_000 {
            Some("Space Limit".to_string())
        } else {
            None
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

