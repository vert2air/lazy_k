use super::lazy_k_core::*;

/// ```
/// use crate::lazy_k::lazy_k_core::{la, v};
/// use crate::lazy_k::lazy_k_interpreter::{is_nil};
/// let nil = la( la( v(1) ) );
/// //assert_eq!( is_nil(&nil), true );
/// ```
pub fn is_nil(e: &PLamExpr) -> bool {
    let aux =  e.clone() * (k() * ( k() * (k() * nm("false")))) * nm("true");
    match ChNumEval::new(aux).eval_cc(true) {
        Some(r) => match r.get_lam2() {
            LamExpr::Nm { name } if **name == "true".to_string() => true,
            _ => false,
        },
        _ => false,
    }
}

