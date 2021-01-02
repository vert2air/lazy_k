use super::lazy_k_core::*;

pub fn exec_lazy_k(prog_data: PLamExpr) -> Vec<u32> {
    let mut lk = prog_data;
    let mut v = Vec::new();
    loop {
        if is_nil(&lk) {
            break;
        }
        let car = s() * i() * (k() * k());
        match (car * lk.clone()).get_num() {
            Some(n) if n < 256 => v.push(n),
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

