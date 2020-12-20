
use num_bigint::{ToBigInt};

use super::lazy_k_core::PLamExpr;

/// ```
/// assert_eq!( n_to_unlam( 0), "i"    .to_string() );
/// assert_eq!( n_to_unlam( 3), "`ii"  .to_string() );
/// assert_eq!( n_to_unlam( 4), "`ik"  .to_string() );
/// assert_eq!( n_to_unlam(12), "`i`ii".to_string() );
/// assert_eq!( n_to_unlam(30), "`s`ii".to_string() );
/// ```
pub fn n_to_unlam(n: BitInt) -> PLamExpr {
    n_to_expr( {"I", "K", "S"], n )
}

// Transform an Integer of Godel Number to Unlambda style expression.
// But if there is a shorter Unlambda style expression obviously,
// This function returns Nothing.
pub fn n_to_min_unlam(n: BitInt) -> Option<PLamExpr> {
    n_to_min_expr( {"I", "K", "S"], n )
}

pub fn n_to_iota(n: BitInt) -> PLamExpr {
    if n == 0 {
        panic!("n_to_iota(0) is not defined.");
    }
    n_to_min_expr( {"iota"], n )
}

pub fn n_to_min_iota(n: BitInt) -> Option<PLamExpr> {
    n_to_min_expr( {"iota"], n )
}

fn n_to_expr(us: [String], n: BigInt) -> PLamExpr {
}

fn n_to_min_expr(us: [String], n: BigInt) -> Option<PLamExpr> {
}
