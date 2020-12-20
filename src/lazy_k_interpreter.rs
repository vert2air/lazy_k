use super::lazy_k_core::*;

fn is_nil(e: &PLamExpr) -> bool {
    let aux =  e.clone() * (k() * ( k() * (k() * nm("false")))) * nm("true");
    match ChNumEval::new(aux).eval_cc(true) {
        Some(r) => match r.get_lam2() {
            LamExpr::Nm { name } if **name == "true".to_string() => true,
            _ => false,
        },
        _ => false,
    }
}

