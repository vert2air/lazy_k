//extern crate num_bigint;
extern crate num_traits;

use std::convert::TryFrom;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Sub;
use std::ops::SubAssign;
use std::ops::Mul;
use std::vec::Vec;
use num_bigint::BigInt;
use num_traits::Zero;

type OwnInt = BigInt;
//type OwnInt = i64;

use super::lazy_k_core::{PLamExpr, nm, LamExpr};


/// ```
/// use lazy_k::lazy_k_read::read_lazy_k;
/// use lazy_k::lazy_k_godel_number::n_to_unlam;
/// use std::convert::TryFrom;
/// use num_bigint::BigInt;
/// 
/// type OwnInt = BigInt;
/// //type OwnInt = i64;
/// 
/// fn bn(a: i32) -> OwnInt {
///     match OwnInt::try_from(a) {
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
/// assert_eq!( Ok( n_to_unlam(bn(10)) ), read_lazy_k("`sk")   );
/// assert_eq!( Ok( n_to_unlam(bn(11)) ), read_lazy_k("`ss")   );
/// assert_eq!( Ok( n_to_unlam(bn(56)) ), read_lazy_k("``kss") );
/// assert_eq!( Ok( n_to_unlam(bn(60)) ), read_lazy_k("``ski") );
/// ```
pub fn n_to_unlam(n: OwnInt) -> PLamExpr {
    n_to_expr(vec!["I".to_string(), "K".to_string(), "S".to_string()], n)
}

/// Transform an Integer of Godel Number to Unlambda style expression.
/// But if there is a shorter Unlambda style expression obviously,
/// This function returns Nothing.
///
/// ```
/// use lazy_k::lazy_k_read::read_lazy_k;
/// use lazy_k::lazy_k_godel_number::n_to_min_unlam;
/// use std::convert::TryFrom;
/// use num_bigint::BigInt;
/// 
/// type OwnInt = BigInt;
/// //type OwnInt = i64;
/// 
/// fn bn(a: i32) -> OwnInt {
///     match OwnInt::try_from(a) {
///         Ok(a2) => a2,
///         _ => panic!("bn"),
///     }
/// }
/// assert_eq!( n_to_min_unlam(bn( 3)), None );   // `ii -> i
/// assert_eq!( n_to_min_unlam(bn( 4)), None );   // `ik -> k
/// assert_eq!( n_to_min_unlam(bn( 5)), None );   // `is -> s
/// assert_eq!( n_to_min_unlam(bn(56)), None );   // ``kss -> s (kXY -> Y
/// assert_eq!( n_to_min_unlam(bn(60)), None );   // ``ski -> i
/// ```
pub fn n_to_min_unlam(n: OwnInt) -> Option<PLamExpr> {
    n_to_min_expr(vec!["I".to_string(), "K".to_string(), "S".to_string()], n)
}

/// ```
/// use lazy_k::lazy_k_read::read_lazy_k;
/// use lazy_k::lazy_k_godel_number::n_to_iota;
/// use std::convert::TryFrom;
/// use num_bigint::BigInt;
/// 
/// type OwnInt = BigInt;
/// //type OwnInt = i64;
/// 
/// fn bn(a: i32) -> OwnInt {
///     match OwnInt::try_from(a) {
///         Ok(a2) => a2,
///         _ => panic!("bn"),
///     }
/// }
/// assert_eq!( Ok( n_to_iota(bn( 1)) ), read_lazy_k("*ii") );
/// assert_eq!( Ok( n_to_iota(bn( 2)) ), read_lazy_k("*i*ii") );
/// assert_eq!( Ok( n_to_iota(bn( 4)) ), read_lazy_k("*i*i*ii") );
/// assert_eq!( Ok( n_to_iota(bn( 9)) ), read_lazy_k("*i*i*i*ii") );
/// ```
pub fn n_to_iota(n: OwnInt) -> PLamExpr {
    if n == Zero::zero() {
        panic!("n_to_iota(0) is not defined.");
    }
    n_to_expr(vec!["iota".to_string()], n)
}
/*
pub fn n_to_min_iota(n: OwnInt) -> Option<PLamExpr> {
    n_to_min_expr( {"iota"], n );
    None
}
*/
fn n_to_expr(b: Vec<String>, n: OwnInt) -> PLamExpr {
    let lsiz = match OwnInt::try_from(b.len()) {
        Ok(size) => build_layer(size, n.clone()),
        Err(_) => panic!("n_to_expr"),
    };
    let sum: OwnInt = lsiz.iter().fold(Zero::zero(), |acc, a| acc + a);
    n_to_expr_aux(b, &lsiz[..], n - sum)
}

fn n_to_expr_aux(b: Vec<String>, lsiz: &[OwnInt], n: OwnInt) -> PLamExpr {
    if lsiz.len() == 0 {
        match usize::try_from(n.clone()) {
            Ok(u) => return nm(&b[u]),
            Err(_) => panic!(format!("n_to_expr_aux({})", n)),
        }
    }
    let (g, t) = sub_rem(n, mul_up_down(lsiz.to_vec()));
    let m = t.clone()       % lsiz[g].clone();
    let d = (t - m.clone()) / lsiz[g].clone();
    let f = n_to_expr_aux(b.clone(), &lsiz[lsiz.len() - g ..], d);
    let o = n_to_expr_aux(b,         &lsiz[g + 1          ..], m);
    f * o
}

fn n_to_min_expr(b: Vec<String>, n: OwnInt) -> Option<PLamExpr> {
    let lsiz = match OwnInt::try_from(b.len()) {
        Ok(size) => build_layer(size, n.clone()),
        Err(_) => panic!("n_to_expr"),
    };
    let sum: OwnInt = lsiz.iter().fold(Zero::zero(), |acc, a| acc + a);
    n_to_min_expr_aux(b, &lsiz[..], n - sum)
}

fn n_to_min_expr_aux(b: Vec<String>, lsiz: &[OwnInt], n: OwnInt)
                                                        -> Option<PLamExpr> {
    if lsiz.len() == 0 {
        match usize::try_from(n.clone()) {
            Ok(u) => return Some(nm(&b[u])),
            Err(_) => panic!(format!("n_to_expr_aux({})", n)),
        }
    }
    let (g, t) = sub_rem(n, mul_up_down(lsiz.to_vec()));
    let m = t.clone()       % lsiz[g].clone();
    let d = (t - m.clone()) / lsiz[g].clone();
    let f1 = match n_to_min_expr_aux(b.clone(), &lsiz[lsiz.len() - g ..], d) {
        Some(x) => x,
        None => return None,
    };
    let o1 = match n_to_min_expr_aux(b,         &lsiz[g + 1          ..], m) {
        Some(x) => x,
        None => return None,
    };
    match f1.extract() {
        LamExpr::Nm { name } if **name == "I" => None,
        LamExpr::App { func: f2, oprd: o2, ..  } => match f2.extract() {
            LamExpr::Nm { name } if **name == "K" => None,
            LamExpr::Nm { name } if **name == "S" => match o2.extract() {
                LamExpr::Nm { name } if **name == "K" => None,
                _ => Some(f1 * o1)
            }
            _ => Some(f1 * o1)
        }
        _ => Some(f1 * o1)
    }
}
/*
fn n_to_min_expr(us: [String], n: OwnInt) -> Option<PLamExpr> {
    None
}
*/

fn build_layer<T: Ord + Add<Output = T> + AddAssign + Sub<Output = T> + SubAssign + Mul<Output = T> + Clone>(base_num: T, gn: T) -> Vec<T> {
    let mut l = Vec::<T>::new();
    if gn < base_num {
        return l;
    }
    l.push(base_num.clone());
    let mut g_rem = gn -  base_num;
    loop {
        let n = mul_up_down(l.clone());
        let mut it = n.iter();
        if let Some(ini) = it.next() {
            let mut sz = ini.clone();
            for e in it {
                sz += e.clone();
            }
            if g_rem < sz {
                return l;
            }
            g_rem -= sz.clone();
            l.insert(0, sz)
        } else {
            panic!("layer_gn")
        }
    }
}

fn sub_rem<T: Ord + SubAssign + Clone>(n0: T, ns: Vec<T>) -> (usize, T) {
    let mut n = n0;
    for i in 0 .. ns.len() {
        if n < ns[i] {
            return (i, n)
        } else {
            n -= ns[i].clone()
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
    assert_eq!( build_layer(3,   2), vec![] );
    assert_eq!( build_layer(3,   5), vec![                     3] );
    assert_eq!( build_layer(3,  15), vec![                3*3, 3] );
    assert_eq!( build_layer(3,  70), vec![            27*2, 9, 3] );
    assert_eq!( build_layer(3, 500), vec![3*54*2 + 9*9, 54, 9, 3] );

}

#[test]
fn test_sub_rem() {
    assert_eq!( sub_rem(0, vec![3]), (0, 0) );
    assert_eq!( sub_rem(1, vec![3]), (0, 1) );
    assert_eq!( sub_rem(2, vec![3]), (0, 2) );
    assert_eq!( sub_rem(4, vec![9, 3]), (0, 4) );
    assert_eq!( sub_rem(8, vec![9, 3]), (0, 8) );
    assert_eq!( sub_rem(9, vec![9, 3]), (1, 0) );
    assert_eq!( sub_rem(10, vec![9, 3]), (1, 1) );
    assert_eq!( sub_rem(11, vec![9, 3]), (1, 2) );
}

#[test]
fn test_mul_up_down() {
    assert_eq!( mul_up_down(vec![1, 2, 3]), vec![3, 4, 3] );
    assert_eq!( mul_up_down(vec![1, 2, 3, 4]), vec![4, 6, 6, 4] );
    assert_eq!( mul_up_down(vec![1, 2, 3, 4, 5]), vec![5, 8, 9, 8, 5] );

    assert_eq!( mul_up_down(vec![            3]), vec![9] );
    assert_eq!( mul_up_down(vec![         9, 3]), vec![27, 27] );
    assert_eq!( mul_up_down(vec![     54, 9, 3]), vec![162, 81, 162] );
    assert_eq!( mul_up_down(vec![405, 54, 9, 3]), vec![1215, 486, 486, 1215] );
}
