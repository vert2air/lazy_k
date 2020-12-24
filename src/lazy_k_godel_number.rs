//extern crate num_bigint;
extern crate num_traits;

use num_bigint::BigInt;
use num_traits::Zero;
use std::convert::TryFrom;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Sub;
use std::ops::SubAssign;
use std::ops::Mul;
use std::vec::Vec;

use super::lazy_k_core::{PLamExpr, nm};


/// ```
/// use lazy_k::lazy_k_read::read_lazy_k;
/// use lazy_k::lazy_k_godel_number::n_to_unlam;
/// use num_bigint::BigInt;
/// use std::convert::TryFrom;
/// 
/// fn bn(a: i32) -> BigInt {
///     match BigInt::try_from(a) {
///         Ok(a2) => a2,
///         _ => panic!("bn"),
///     }
/// }
/// assert_eq!( Ok( n_to_unlam(bn( 0)) ), read_lazy_k("i")     );
/// assert_eq!( Ok( n_to_unlam(bn( 1)) ), read_lazy_k("k")     );
/// assert_eq!( Ok( n_to_unlam(bn( 2)) ), read_lazy_k("s")     );
/// assert_eq!( Ok( n_to_unlam(bn( 3)) ), read_lazy_k("`ii")   );
/// assert_eq!( Ok( n_to_unlam(bn( 4)) ), read_lazy_k("`ik")   );
/// assert_eq!( Ok( n_to_unlam(bn( 5)) ), read_lazy_k("`is")   );
/// assert_eq!( Ok( n_to_unlam(bn( 6)) ), read_lazy_k("`ki")   );
/// assert_eq!( Ok( n_to_unlam(bn( 7)) ), read_lazy_k("`kk")   );
/// assert_eq!( Ok( n_to_unlam(bn( 8)) ), read_lazy_k("`ks")   );

/// assert_eq!( Ok( n_to_unlam(bn( 9)) ), read_lazy_k("`si")   );

// assert_eq!( Ok( n_to_unlam(bn(10)) ), read_lazy_k("`sk")   );

// assert_eq!( Ok( n_to_unlam(bn(11)) ), read_lazy_k("`ss")   );
// assert_eq!( Ok( n_to_unlam(bn(12)) ), read_lazy_k("`i`ii") );
// assert_eq!( Ok( n_to_unlam(bn(30)) ), read_lazy_k("`s`ii") );
/// ```
pub fn n_to_unlam(n: BigInt) -> PLamExpr {
    n_to_expr(vec!["I".to_string(), "K".to_string(), "S".to_string()], n)
}
/*
*/

// Transform an Integer of Godel Number to Unlambda style expression.
// But if there is a shorter Unlambda style expression obviously,
// This function returns Nothing.

/*
pub fn n_to_min_unlam(n: BigInt) -> Option<PLamExpr> {
    n_to_min_expr( vec!["I".to_string(), "K".to_string(), "S".to_string()], n )
}
*/
pub fn n_to_iota(n: BigInt) -> PLamExpr {
    if n == Zero::zero() {
        panic!("n_to_iota(0) is not defined.");
    }
    n_to_expr(vec!["iota".to_string()], n)
}
/*
pub fn n_to_min_iota(n: BigInt) -> Option<PLamExpr> {
    n_to_min_expr( {"iota"], n );
    None
}
*/
fn n_to_expr(us: Vec<String>, n: BigInt) -> PLamExpr {
    let lsiz = match BigInt::try_from(us.len()) {
        Ok(size) => build_layer(size, n.clone()),
        Err(_) => panic!("n_to_expr"),
    };
    let sum: BigInt = lsiz.iter().fold(Zero::zero(), |acc, a| acc + a);
    n_to_expr_aux(us, &lsiz, n - sum)
}

/*
fn n_to_min_expr(us: [String], n: BigInt) -> Option<PLamExpr> {
    None
}
*/

fn n_to_expr_aux(b: Vec<String>, lsiz: &[BigInt], n: BigInt) -> PLamExpr {
    if lsiz.len() == 0 {
        match usize::try_from(n.clone()) {
            Ok(u) => return nm(&b[u]),
            Err(_) => panic!(format!("n_to_expr_aux({})", n)),
        }
    }
    let (g, t) = sub_rem(n, mul_up_down(lsiz.to_vec()));
    let gi = g;
    let m = t.clone()       % lsiz[gi].clone();
    let d = (t - m.clone()) / lsiz[gi].clone();
    let f = n_to_expr_aux(b.clone(), &lsiz[lsiz.len() - gi ..], d);
    let o = n_to_expr_aux(b,         &lsiz[gi + 1..], m);
    f * o
}

fn build_layer<T: Ord + Add<Output = T> + AddAssign + Sub<Output = T> + SubAssign + Mul<Output = T> + Clone>(base_num: T, gn: T) -> Vec<T> {
    let mut l = Vec::<T>::new();
    if gn < base_num {
        return l;
    }
    l.push(base_num.clone());
    let mut g_rem = gn;
    loop {
        let n = mul_up_down(l.clone());
        let mut it = n.iter();
        if let Some(ini) = it.next() {
            let mut sz = ini.clone();
            let _ = it.map(|e: &T| {
                sz += e.clone();
                e   // dummy return value
            });
            if g_rem < sz {
                return l;
            }
            g_rem -= sz.clone();
            // l.push(sz)
            l.insert(0, sz)
        } else {
            panic!("layer_gn")
        }
    }
}

fn sub_rem<T: Ord + Sub<Output = T> + Clone>(n0: T, ns: Vec<T>) -> (usize, T) {
    let mut n = n0;
    for i in 0 .. ns.len() {
        if n < ns[i] {
            return (i, n)
        } else {
            n = n - ns[i].clone()
        }
    }
    panic!("sub_rem: Impossible!")
}

fn mul_up_down<T: Mul<Output = T> + Clone>(es: Vec<T>) -> Vec<T> {
    let mut res = Vec::<T>::new();
    for i in 0 .. es.len() {
        res.push(es[i].clone() * es[es.len() - i - 1].clone());
    }
    res
}

#[test]
fn test_build_layer() {
    assert_eq!( build_layer(3, 2), vec![] );
    assert_eq!( build_layer(3, 5), vec![3, ] );
    assert_eq!( build_layer(3, 15), vec![3*3, 3, ] );
    assert_eq!( build_layer(3, 70), vec![27*2, 9, 3, ] );
    //assert_eq!( build_layer(3, 500), vec![3, 9, 54, 3*54*2 + 81] );

}

#[test]
fn test_sub_rem() {
    //assert_eq!( sum_rem(1, vec![100, 10]), (0, 1) );
    //assert_eq!( sum_rem(20, vec![100, 10]), (0, 1) );
}

#[test]
fn test_mul_up_down() {
    assert_eq!( mul_up_down(vec![1, 2, 3]), vec![3, 4, 3] );
    assert_eq!( mul_up_down(vec![1, 2, 3, 4]), vec![4, 6, 6, 4] );
    assert_eq!( mul_up_down(vec![1, 2, 3, 4, 5]), vec![5, 8, 9, 8, 5] );

    assert_eq!( mul_up_down(vec![3]), vec![9] );
    assert_eq!( mul_up_down(vec![3, 9]), vec![27, 27] );
    assert_eq!( mul_up_down(vec![3, 9, 54]), vec![162, 81, 162] );
    assert_eq!( mul_up_down(vec![3, 9, 54, 305]), vec![915, 486, 486, 915] );
}
