extern crate num_bigint;

use num_bigint::{BigInt, ToBigInt};

use super::lazy_k_core::PLamExpr;

/// ```
/// assert_eq!( Some( n_to_unlam( 0) ), read_unlam("i")     );
/// assert_eq!( Some( n_to_unlam( 3) ), read_unlam("`ii")   );
/// assert_eq!( Some( n_to_unlam( 4) ), read_unlam("`ik")   );
/// assert_eq!( Some( n_to_unlam(12) ), read_unlam("`i`ii") );
/// assert_eq!( Some( n_to_unlam(30) ), read_unlam("`s`ii") );
/// ```
/*
pub fn n_to_unlam(n: BitInt) -> PLamExpr {
    n_to_expr( ["I", "K", "S"], n )
}
*/

// Transform an Integer of Godel Number to Unlambda style expression.
// But if there is a shorter Unlambda style expression obviously,
// This function returns Nothing.
/*
pub fn n_to_min_unlam(n: BitInt) -> Option<PLamExpr> {
    n_to_min_expr( {"I", "K", "S"], n )
}

pub fn n_to_iota(n: BitInt) -> PLamExpr {
    if n == 0 {
        panic!("n_to_iota(0) is not defined.");
    }
    n_to_min_expr( {"iota"], n );
    None
}

pub fn n_to_min_iota(n: BitInt) -> Option<PLamExpr> {
    n_to_min_expr( {"iota"], n );
    None
}

fn n_to_expr(us: [String], n: BigInt) -> PLamExpr {
    i()
}

fn n_to_min_expr(us: [String], n: BigInt) -> Option<PLamExpr> {
    None
}
*/

//fn mul_up_down(es: [BigInt]) -> [BitInt] {
fn mul_up_down(es: [u64]) -> [u64] {
    es.clone().zip(es.rev()).map(|(a, b)| a * b).collect()
}

