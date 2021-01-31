extern crate num_traits;

use std::cmp::{PartialOrd, Ordering};
use std::convert::TryFrom;
use std::ops::AddAssign;
use std::ops::Sub;
use std::ops::SubAssign;
use std::ops::Mul;
use std::vec::Vec;
use num_bigint::BigInt;
use num_traits::{Zero, One};

pub type OurInt = BigInt;
pub fn our0() -> OurInt { Zero::zero() }
pub fn our1() -> OurInt { One::one() }
//pub type OurInt = i64;
//pub fn our0() -> OurInt { 0 }
//pub fn our1() -> OurInt { 1 }

use super::lazy_k_core::{PLamExpr, nm, LamExpr};


/// ```
/// use lazy_k::lazy_k_read::read_lazy_k;
/// use lazy_k::goedel_number::n_to_unlam;
/// use std::convert::TryFrom;
/// use num_bigint::BigInt;
/// 
/// type OurInt = BigInt;
/// //type OurInt = i64;
/// 
/// fn bn(a: i32) -> OurInt {
///     match OurInt::try_from(a) {
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
pub fn n_to_unlam(n: OurInt) -> PLamExpr {
    n_to_expr(vec!["I".to_string(), "K".to_string(), "S".to_string()], n)
}

/// Transform an Integer of Goedel Number to Unlambda style expression.
/// But if there is a shorter Unlambda style expression obviously,
/// This function returns Nothing.
///
/// ```
/// use lazy_k::lazy_k_read::read_lazy_k;
/// use lazy_k::goedel_number::n_to_min_unlam;
/// use std::convert::TryFrom;
/// use num_bigint::BigInt;
/// 
/// type OurInt = BigInt;
/// //type OurInt = i64;
/// 
/// fn bn(a: i32) -> OurInt {
///     match OurInt::try_from(a) {
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
pub fn n_to_min_unlam(n: OurInt) -> Option<PLamExpr> {
    n_to_min_expr(vec!["I".to_string(), "K".to_string(), "S".to_string()], n)
}

/// ```
/// use lazy_k::lazy_k_read::read_lazy_k;
/// use lazy_k::goedel_number::n_to_iota;
/// use std::convert::TryFrom;
/// use num_bigint::BigInt;
/// 
/// type OurInt = BigInt;
/// //type OurInt = i64;
/// 
/// fn bn(a: i32) -> OurInt {
///     match OurInt::try_from(a) {
///         Ok(a2) => a2,
///         _ => panic!("bn"),
///     }
/// }
/// assert_eq!( Ok( n_to_iota(bn( 1)) ), read_lazy_k("*ii") );
/// assert_eq!( Ok( n_to_iota(bn( 2)) ), read_lazy_k("*i*ii") );
/// assert_eq!( Ok( n_to_iota(bn( 4)) ), read_lazy_k("*i*i*ii") );
/// assert_eq!( Ok( n_to_iota(bn( 9)) ), read_lazy_k("*i*i*i*ii") );
/// ```
pub fn n_to_iota(n: OurInt) -> PLamExpr {
    if n == our0() {
        panic!("n_to_iota(0) is not defined.");
    }
    n_to_expr(vec!["iota".to_string()], n)
}
/*
pub fn n_to_min_iota(n: OurInt) -> Option<PLamExpr> {
    n_to_min_expr( {"iota"], n );
    None
}
*/
fn n_to_expr(b: Vec<String>, n: OurInt) -> PLamExpr {
    let lsiz = match OurInt::try_from(b.len()) {
        Ok(size) => build_layer(size, n.clone()),
        Err(_) => panic!("n_to_expr"),
    };
    let sum: OurInt = lsiz.iter().fold(our0(), |acc, a| acc + a);
    n_to_expr_aux(b, &lsiz[..], n - sum)
}

fn n_to_expr_aux(b: Vec<String>, lsiz: &[OurInt], n: OurInt) -> PLamExpr {
    if lsiz.len() == 0 {
        match usize::try_from(n.clone()) {
            Ok(u) => return nm(&b[u]),
            Err(_) => panic!(format!("n_to_expr_aux({})", n)),
        }
    }
    let (g, t) = sub_rem(n, &mul_up_down(&lsiz.to_vec()));
    let m = t.clone()       % lsiz[g].clone();
    let d = (t - m.clone()) / lsiz[g].clone();
    let f = n_to_expr_aux(b.clone(), &lsiz[lsiz.len() - g ..], d);
    let o = n_to_expr_aux(b,         &lsiz[g + 1          ..], m);
    f * o
}

fn decompose(n: OurInt) -> Option<(OurInt, OurInt)> {
    let base = 3;
    let lsiz = match OurInt::try_from(base) {
        Ok(size) => build_layer(size, n.clone()),
        Err(_) => panic!("decompose"),
    };
    let sum: OurInt = lsiz.iter().fold(our0(), |acc, a| acc + a);
    let n = n - sum;
    if lsiz.len() == 0 {
        return None
    }
    let (g, t) = sub_rem(n, &mul_up_down(&lsiz.to_vec()));
    let m = t.clone()       % lsiz[g].clone();
    let d = (t - m.clone()) / lsiz[g].clone();
    let sumF = lsiz[lsiz.len() - g ..].iter().fold(our0(), |acc, a| acc + a);
    let sumO = lsiz[g + 1          ..].iter().fold(our0(), |acc, a| acc + a);
    Some((d +sumF, m + sumO))
}

#[test]
fn test_decompose_basic() {
    fn n(i: u32) -> OurInt {
        OurInt::try_from(i).unwrap()
    }
    assert_eq!( decompose(n(0)), None);
    assert_eq!( decompose(n(1)), None);
    assert_eq!( decompose(n(2)), None);

    assert_eq!( decompose(n( 3)), Some((n(0),n(0))) );
    assert_eq!( decompose(n( 4)), Some((n(0),n(1))) );
    assert_eq!( decompose(n( 5)), Some((n(0),n(2))) );
    assert_eq!( decompose(n( 6)), Some((n(1),n(0))) );
    assert_eq!( decompose(n( 7)), Some((n(1),n(1))) );
    assert_eq!( decompose(n( 8)), Some((n(1),n(2))) );
    assert_eq!( decompose(n( 9)), Some((n(2),n(0))) );
    assert_eq!( decompose(n(10)), Some((n(2),n(1))) );
    assert_eq!( decompose(n(11)), Some((n(2),n(2))) );

    assert_eq!( decompose(n(12)), Some((n(0),n(3))) );
    assert_eq!( decompose(n(13)), Some((n(0),n(4))) );
    assert_eq!( decompose(n(14)), Some((n(0),n(5))) );
    assert_eq!( decompose(n(15)), Some((n(0),n(6))) );
    assert_eq!( decompose(n(20)), Some((n(0),n(11))) );
    assert_eq!( decompose(n(21)), Some((n(1),n(3))) );
    assert_eq!( decompose(n(29)), Some((n(1),n(11))) );
    assert_eq!( decompose(n(30)), Some((n(2),n(3))) );
    assert_eq!( decompose(n(38)), Some((n(2),n(11))) );
    assert_eq!( decompose(n(39)), Some((n(3),n(0))) );
}

#[test]
fn test_decompose() {
    use super::lazy_k_read::read_lazy_k;
    fn test(a: &str, b: &str) {
        let a = read_lazy_k(a).unwrap();
        let b = read_lazy_k(b).unwrap();
        let (_, na) = lam_to_n(&a.clone());
        let (_, nb) = lam_to_n(&b.clone());
        let (_, nab) = lam_to_n(&(a*b));
        assert_eq!( decompose(nab), Some((na, nb)) );
    }
    test("``ssk", "`ks");
    test("```kssk", "`s`i`ks");
}

fn goedel_number_len(n: OurInt) -> usize {
    let base = 3;
    let lsiz = build_layer(OurInt::try_from(base).unwrap(), n.clone());
    lsiz.len()
}

#[test]
fn test_goedel_number_len() {
    fn n(i: u32) -> OurInt {
        OurInt::try_from(i).unwrap()
    }
    assert_eq!( goedel_number_len(n(0)), 0 );
    assert_eq!( goedel_number_len(n(2)), 0 );
    assert_eq!( goedel_number_len(n(3)), 1 );
    assert_eq!( goedel_number_len(n(11)), 1 );
    assert_eq!( goedel_number_len(n(12)), 2 );
    assert_eq!( goedel_number_len(n(65)), 2 );
    assert_eq!( goedel_number_len(n(66)), 3 );
}

fn compose(nf: OurInt, no: OurInt) -> OurInt {
    let sf = goedel_number_len(nf.clone()) * 2 + 1;
    let so = goedel_number_len(no.clone()) * 2 + 1;
    let mut lsiz = vec![OurInt::try_from(3).unwrap()];
    for _ in 1 .. (1 + sf + so + 1) / 2 - 1{
        let n = mul_up_down(&lsiz);
        lsiz.push(sum(n));
    }
    let (_, nf2) = sub_rem(nf, &lsiz);
    let (_, no2) = sub_rem(no, &lsiz);
    let ud = mul_up_down(&lsiz);
    let mut a = our0();
    for i in 0 .. (sf - 1) / 2 {
        a += ud[i].clone();
    }
    lsiz[(so - 1) / 2].clone() * nf2 + no2 + a + sum(lsiz)
}

#[test]
fn test_compose_basic() {
    fn n(i: u32) -> OurInt {
        OurInt::try_from(i).unwrap()
    }
    assert_eq!( compose(n(0), n(0)), n( 3) );
    assert_eq!( compose(n(0), n(1)), n( 4) );
    assert_eq!( compose(n(0), n(2)), n( 5) );
    assert_eq!( compose(n(1), n(0)), n( 6) );
    assert_eq!( compose(n(1), n(1)), n( 7) );
    assert_eq!( compose(n(1), n(2)), n( 8) );
    assert_eq!( compose(n(2), n(0)), n( 9) );
    assert_eq!( compose(n(2), n(1)), n(10) );
    assert_eq!( compose(n(2), n(2)), n(11) );

    assert_eq!( compose(n(0), n( 3)), n(12) );
    assert_eq!( compose(n(0), n( 4)), n(13) );
    assert_eq!( compose(n(0), n( 5)), n(14) );
    assert_eq!( compose(n(0), n( 6)), n(15) );
    assert_eq!( compose(n(0), n(11)), n(20) );
    assert_eq!( compose(n(1), n( 3)), n(21) );
    assert_eq!( compose(n(1), n(11)), n(29) );
    assert_eq!( compose(n(2), n( 3)), n(30) );
    assert_eq!( compose(n(2), n(11)), n(38) );
    assert_eq!( compose(n(3), n( 0)), n(39) );
}

fn n_to_min_expr(b: Vec<String>, n: OurInt) -> Option<PLamExpr> {
    let lsiz = match OurInt::try_from(b.len()) {
        Ok(size) => build_layer(size, n.clone()),
        Err(_) => panic!("n_to_expr"),
    };
    let sum: OurInt = lsiz.iter().fold(our0(), |acc, a| acc + a);
    n_to_min_expr_aux(b, &lsiz[..], n - sum)
}

fn n_to_min_expr_aux(b: Vec<String>, lsiz: &[OurInt], n: OurInt)
                                                        -> Option<PLamExpr> {
    if lsiz.len() == 0 {
        match usize::try_from(n.clone()) {
            Ok(u) => return Some(nm(&b[u])),
            Err(_) => panic!(format!("n_to_expr_aux({})", n)),
        }
    }
    let (g, t) = sub_rem(n, &mul_up_down(&lsiz.to_vec()));
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

fn build_layer<T: Ord + AddAssign + Sub<Output = T> + SubAssign + Mul<Output = T> + Clone>(base_num: T, gn: T) -> Vec<T> {
    let mut l = Vec::<T>::new();
    if gn < base_num {
        return l;
    }
    l.push(base_num.clone());
    let mut g_rem = gn -  base_num;
    loop {
        let n = mul_up_down(&l);
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

fn sub_rem<T: Ord + SubAssign + Clone>(n0: T, ns: &Vec<T>) -> (usize, T) {
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

fn mul_up_down<T: Mul<Output = T> + Clone>(es: &Vec<T>) -> Vec<T> {
    let mut res = Vec::<T>::new();
    for i in 0 .. es.len() {
        res.push(es[i].clone() * es[es.len() - i - 1].clone());
    }
    res
}

// pub fn n_to_jot(n: OurInt) -> String

fn sum(v: Vec<OurInt>) -> OurInt {
    let it = v.iter();
    let mut sz = our0();
    for e in it {
        sz += e.clone();
    }
    sz
}

/// ```
/// use lazy_k::lazy_k_core::i;
/// use lazy_k::lazy_k_read::read_lazy_k;
/// use lazy_k::goedel_number::lam_to_n;
/// use std::convert::TryFrom;
/// use num_bigint::BigInt;
/// type OurInt = BigInt;
/// //type OurInt = i64;
/// fn n(num: u32) -> OurInt {
///     match OurInt::try_from(num) {
///         Ok(a) => a,
///         _ => panic!("lam_to_n(0)"),
///     }
/// };
/// assert_eq!(lam_to_n(&read_lazy_k("i").unwrap()), (n(3), n(0)));
/// assert_eq!(lam_to_n(&read_lazy_k("k").unwrap()), (n(3), n(1)));
/// assert_eq!(lam_to_n(&read_lazy_k("s").unwrap()), (n(3), n(2)));
/// assert_eq!(lam_to_n(&read_lazy_k("`ii").unwrap()), (n(3), n(3)));
/// assert_eq!(lam_to_n(&read_lazy_k("`ik").unwrap()), (n(3), n(4)));
/// assert_eq!(lam_to_n(&read_lazy_k("`is").unwrap()), (n(3), n(5)));
/// assert_eq!(lam_to_n(&read_lazy_k("`ki").unwrap()), (n(3), n(6)));
/// assert_eq!(lam_to_n(&read_lazy_k("`kk").unwrap()), (n(3), n(7)));
/// assert_eq!(lam_to_n(&read_lazy_k("`ks").unwrap()), (n(3), n(8)));
/// assert_eq!(lam_to_n(&read_lazy_k("`si").unwrap()), (n(3), n(9)));
/// assert_eq!(lam_to_n(&read_lazy_k("`sk").unwrap()), (n(3), n(10)));
/// assert_eq!(lam_to_n(&read_lazy_k("`ss").unwrap()), (n(3), n(11)));
/// assert_eq!(lam_to_n(&read_lazy_k("`i`ii").unwrap()), (n(3), n(12)));
/// assert_eq!(lam_to_n(&read_lazy_k("`i`ik").unwrap()), (n(3), n(13)));
/// assert_eq!(lam_to_n(&read_lazy_k("`i`is").unwrap()), (n(3), n(14)));
/// assert_eq!(lam_to_n(&read_lazy_k("`i`ki").unwrap()), (n(3), n(15)));
/// assert_eq!(lam_to_n(&read_lazy_k("``kss").unwrap()), (n(3), n(56)));
/// assert_eq!(lam_to_n(&read_lazy_k("``ski").unwrap()), (n(3), n(60)));
/// 
/// assert_eq!(lam_to_n(&read_lazy_k("*ii").unwrap()), (n(1), n(1)));
/// assert_eq!(lam_to_n(&read_lazy_k("*i*ii").unwrap()), (n(1), n(2)));
/// assert_eq!(lam_to_n(&read_lazy_k("**iii").unwrap()), (n(1), n(3)));
/// assert_eq!(lam_to_n(&read_lazy_k("*i*i*ii").unwrap()), (n(1), n(4)));
/// assert_eq!(lam_to_n(&read_lazy_k("*i**iii").unwrap()), (n(1), n(5)));
/// assert_eq!(lam_to_n(&read_lazy_k("**ii*ii").unwrap()), (n(1), n(6)));
/// assert_eq!(lam_to_n(&read_lazy_k("**i*iii").unwrap()), (n(1), n(7)));
/// assert_eq!(lam_to_n(&read_lazy_k("***iiii").unwrap()), (n(1), n(8)));
/// 
/// assert_eq!(lam_to_n(&read_lazy_k("``s`k``s`si`kik").unwrap()),
///                                                     (n(3), n(2_471_467)));
/// assert_eq!(lam_to_n(&read_lazy_k("``s`k``s`si`sik").unwrap()),
///                                                     (n(3), n(2_471_476)));
/// ```
pub fn lam_to_n(lam: &PLamExpr) -> (OurInt, OurInt) {
    let zero  = OurInt::try_from(0).unwrap();
    let one   = OurInt::try_from(1).unwrap();
    let two   = OurInt::try_from(2).unwrap();
    let three = OurInt::try_from(3).unwrap();
    match lam.extract() {
        LamExpr::Nm { name } if **name == "I" => (three, zero),
        LamExpr::Nm { name } if **name == "K" => (three, one),
        LamExpr::Nm { name } if **name == "S" => (three, two),
        LamExpr::Nm { name } if **name == "iota" => (one, zero),
        LamExpr::App { func, oprd, size } => {
            let (tf, nf) = lam_to_n(func);
            let (_t, no) = lam_to_n(oprd);
            let mut lsiz = vec![tf.clone()];
            for _ in 1 .. (size + 1) / 2 - 1 {
                let n = mul_up_down(&lsiz);
                lsiz.push(sum(n));
            }
            let (_, nf2) = sub_rem(nf, &lsiz);
            let (_, no2) = sub_rem(no, &lsiz);
            let ud = mul_up_down(&lsiz);
            let mut a = zero;
            for i in 0 .. (func.len() - 1) / 2 {
                a += ud[i].clone();
            }
            (tf, lsiz[(oprd.len() - 1) / 2].clone() * nf2 + no2 + a + sum(lsiz))
        },
        _ => panic!("lam_to_n"),
    }
}

impl PartialOrd for PLamExpr {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PLamExpr {
    fn cmp(&self, other: &Self) -> Ordering {
        let lo = self.len().cmp(&other.len());
        match lo {
            Ordering::Equal => match (self.extract(), other.extract()) {
                (LamExpr::Nm { name: n1}, LamExpr::Nm { name: n2}) =>
                    n1.cmp(&n2),
                (LamExpr::App { func: f1, oprd: o1, .. },
                                LamExpr::App { func: f2, oprd: o2, .. }) => {
                    let fo = f1.cmp(&f2);
                    match fo {
                        Ordering::Equal => o1.cmp(&o2),
                        _ => fo,
                    }
                }
                _ => panic!("Ord<PLamExpr>::partial_cmp"),
            }
            _ => lo
        }
    }
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
    assert_eq!( sub_rem(0, &vec![3]), (0, 0) );
    assert_eq!( sub_rem(1, &vec![3]), (0, 1) );
    assert_eq!( sub_rem(2, &vec![3]), (0, 2) );
    assert_eq!( sub_rem(4, &vec![9, 3]), (0, 4) );
    assert_eq!( sub_rem(8, &vec![9, 3]), (0, 8) );
    assert_eq!( sub_rem(9, &vec![9, 3]), (1, 0) );
    assert_eq!( sub_rem(10, &vec![9, 3]), (1, 1) );
    assert_eq!( sub_rem(11, &vec![9, 3]), (1, 2) );
}

#[test]
fn test_mul_up_down() {
    assert_eq!( mul_up_down(&vec![1, 2, 3]), vec![3, 4, 3] );
    assert_eq!( mul_up_down(&vec![1, 2, 3, 4]), vec![4, 6, 6, 4] );
    assert_eq!( mul_up_down(&vec![1, 2, 3, 4, 5]), vec![5, 8, 9, 8, 5] );

    assert_eq!( mul_up_down(&vec![            3]), vec![9] );
    assert_eq!( mul_up_down(&vec![         9, 3]), vec![27, 27] );
    assert_eq!( mul_up_down(&vec![     54, 9, 3]), vec![162, 81, 162] );
    assert_eq!( mul_up_down(&vec![405, 54, 9, 3]), vec![1215, 486, 486, 1215] );
}

#[test]
fn test_read_n_to_unlam() {
    use super::lazy_k_read::read_lazy_k;
    fn bn(a: i32) -> OurInt {
        match OurInt::try_from(a) {
            Ok(a2) => a2,
            _ => panic!("bn"),
        }
    }
    fn check(n: &OurInt) {
        let ul = n_to_unlam(n.clone()); // PLamExpr
        let st = ul.to_unlam().unwrap();        // String
        let cc = read_lazy_k(&st).unwrap();     // PLamExpr
        let (_, n2) = lam_to_n(&cc);        // OurInt
        println!("Goedel number: {} <=> {} <=> {}", n.clone(), st, n2.clone());
        assert_eq!( n.clone(), n2 );
    }
    let mut n = bn(100);
    //for _ in 1..100 {
    for _ in 1..5 {
        check(&n);
        n *= bn(100);
    }
}

