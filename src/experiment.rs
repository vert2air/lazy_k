use num_bigint::BigInt;
use num_traits::{Zero, One};
use std::collections::BTreeMap;
use std::convert::TryFrom;
use std::fs;

use super::lazy_k_read;
use super::lazy_k_core;
use super::rev_iter::RevIter;
use super::lazy_k_core::{PLamExpr, LamExpr};
use super::goedel_number;
use super::goedel_number::{sub_rem};

pub fn experiment(args: Vec<String>) {
    let prog = fs::read_to_string(&args[2]).unwrap();
    let p = lazy_k_read::read_lazy_k(&prog).unwrap();
    let data = fs::read_to_string(&args[3]).unwrap();
    let d = lazy_k_read::read_lazy_k(&data).unwrap();
    let w = p * d;
    ana_tree(w.clone());
    println!("");
    match lazy_k_core::apply_fully(100, w, |x| PLamExpr::beta_red_cc(&x), |_| None) {
        Err((r, _, _)) => {
            ana_tree(r.clone());
            match lazy_k_core::apply_fully(100, r,
                                |x| PLamExpr::beta_red_cc(&x), |_| None) {
                Err((r, _, _)) => ana_tree(r.clone()),
                _ => ()
            }
        }
        _ => ()
    }
}

fn ana_tree(e: PLamExpr) {
    let mut map:BTreeMap<BigInt, u32> = BTreeMap::new();
    ana_subtree(&mut map, &e);
    for (k, v) in map.iter() {
        if k < &BigInt::try_from(4_000_000_000u32).unwrap() {
            let le = goedel_number::n_to_unlam(k.clone());
            println!("gn: {} {} => {}", k, le.to_unlam().unwrap(), v);
        } else {
            println!("gn: {} => {}", k, v);
        }
    }
}

fn ana_subtree(map: &mut BTreeMap<BigInt, u32>, e: &PLamExpr) {
    match &*e.extract() {
        LamExpr::Nm { name } if **name == "I" => inc(map, Zero::zero()),
        LamExpr::Nm { name } if **name == "K" => inc(map, One::one()),
        LamExpr::Nm { name } if **name == "S" =>
                                inc(map, BigInt::try_from(2).unwrap()),
        LamExpr::App { func, oprd, .. } => {
            let (_, gn) = goedel_number::lam_to_n(&e);
            inc(map, gn);
            ana_subtree(map, func);
            ana_subtree(map, oprd);
        },
        _ => panic!("ana_subtree"),
    }
}

fn inc(map: &mut BTreeMap<BigInt, u32>, idx: BigInt) {
    match map.get(&idx) {
        Some(c) => map.insert(idx, c + 1),
        None    => map.insert(idx, 1),
    };
}

pub type GN = BigInt;

#[derive(PartialEq, Eq, Debug)]
pub struct GNBuilder {
    num: Vec<GN>,
    acc: Vec<GN>,
    pair_num: Vec<Vec<GN>>,
    pair_acc: Vec<Vec<GN>>,
    base: Vec<String>,
}

impl GNBuilder {

    pub fn new(b: Vec<String>) -> Self {
        let ob = GN::try_from(b.len()).unwrap();
        GNBuilder {
            num: vec![Zero::zero(), ob.clone()],
            acc: vec![Zero::zero(), ob],
            pair_num: vec![vec![], vec![Zero::zero()]],
            pair_acc: vec![vec![], vec![Zero::zero()]],
            base: b,
        }
    }

    fn prepare_count(&mut self, cnt: usize) {
        match self.num.get(cnt) {
            Some(_) => (),
            None => {
                self.prepare_count(cnt - 1);
                let mut pnum = vec![];
                let mut pacc = vec![Zero::zero()];
                let mut sum: GN = Zero::zero();
                for i in 1 .. cnt {
                    pnum.push(self.num[i].clone()
                              * self.num[cnt - i].clone());
                    sum += pnum[pnum.len() - 1].clone();
                    pacc.push(sum.clone());
                }
                self.pair_num.insert(cnt, pnum);
                self.pair_acc.insert(cnt, pacc.clone());
                self.num.insert(cnt, pacc[pacc.len() - 1].clone());
                self.acc.insert(cnt, self.num[cnt].clone()
                                    + self.acc[cnt - 1].clone());
            }
        }
    }

    fn prepare_gn(&mut self, gn: GN) {
        loop {
            if gn < self.acc[self.acc.len() - 1] {
                break;
            }
            self.prepare_count(self.acc.len());
        }
    }

    /// the Number of I, K, S
    fn count(&mut self, gn: GN) -> usize {
        self.prepare_gn(gn.clone());
        for c in 0..self.acc.len() {
            if gn < self.acc[c] {
                return c;
            }
        }
        0 // dummy, never reach here.
    }

    pub fn compose(&mut self, nf: GN, no: GN) -> GN {
        let cf = self.count(nf.clone());
        let co = self.count(no.clone());
        let total_cnt = cf.clone() + co.clone();
        self.prepare_count(total_cnt);
        let of = nf - self.acc[cf - 1].clone();
        let oo = no - self.acc[co - 1].clone();
        let tf = self.num[co].clone();
        of * tf + oo + self.pair_acc[total_cnt][cf - 1].clone()
                    + self.acc[total_cnt - 1].clone()
    }

    pub fn decompose(&mut self, n: GN) -> Option<(GN, GN)> {
        self.prepare_gn(n.clone());
        let cnt = self.count(n.clone());
        if cnt == 1 {
            return None
        }
        let on = n - self.acc[cnt - 1].clone();
        let (g, t) = sub_rem(on, &self.pair_num[cnt]);
        let om = t.clone()        % self.num[cnt - (g + 1)].clone();
        let od = (t - om.clone()) / self.num[cnt - (g + 1)].clone();
        Some( (od + self.acc[g].clone(),
                om + self.acc[cnt - g - 2].clone()) )
    }

    /// ```
    /// use lazy_k::experiment::{GNBuilder, GN};
    /// use lazy_k::lazy_k_read::read_lazy_k;
    /// use lazy_k::goedel_number::n_to_unlam;
    /// use std::convert::TryFrom;
    /// use num_bigint::BigInt;
    /// 
    /// fn bn(a: i32) -> GN {
    ///     match GN::try_from(a) {
    ///         Ok(a2) => a2,
    ///         _ => panic!("bn"),
    ///     }
    /// }
    /// let mut gnb = GNBuilder::new(vec!["I", "K", "S"]
    ///                         .into_iter().map(|x| x.to_string()).collect());
    /// assert_eq!( Ok( gnb.gn_to_lam(bn( 0)) ), read_lazy_k("i")     );
    /// assert_eq!( Ok( gnb.gn_to_lam(bn( 1)) ), read_lazy_k("k")     );
    /// assert_eq!( Ok( gnb.gn_to_lam(bn( 2)) ), read_lazy_k("s")     );
    /// assert_eq!( Ok( gnb.gn_to_lam(bn( 3)) ), read_lazy_k("`ii")   );
    /// assert_eq!( Ok( gnb.gn_to_lam(bn( 4)) ), read_lazy_k("`ik")   );
    /// assert_eq!( Ok( gnb.gn_to_lam(bn( 5)) ), read_lazy_k("`is")   );
    /// assert_eq!( Ok( gnb.gn_to_lam(bn( 6)) ), read_lazy_k("`ki")   );
    /// assert_eq!( Ok( gnb.gn_to_lam(bn( 7)) ), read_lazy_k("`kk")   );
    /// assert_eq!( Ok( gnb.gn_to_lam(bn( 8)) ), read_lazy_k("`ks")   );
    /// assert_eq!( Ok( gnb.gn_to_lam(bn( 9)) ), read_lazy_k("`si")   );
    /// assert_eq!( Ok( gnb.gn_to_lam(bn(10)) ), read_lazy_k("`sk")   );
    /// assert_eq!( Ok( gnb.gn_to_lam(bn(11)) ), read_lazy_k("`ss")   );
    /// assert_eq!( Ok( gnb.gn_to_lam(bn(56)) ), read_lazy_k("``kss") );
    /// assert_eq!( Ok( gnb.gn_to_lam(bn(60)) ), read_lazy_k("``ski") );
    /// ```
    pub fn gn_to_lam(&mut self, n: GN) -> PLamExpr {
        match self.decompose(n.clone()) {
            Some((f, o)) => self.gn_to_lam(f) * self.gn_to_lam(o),
            None => lazy_k_core::nm(&self.base[usize::try_from(n).unwrap()]),
        }
    }

    pub fn gn_to_min_lam(&mut self, n: GN) -> Option<PLamExpr> {
        match self.decompose(n.clone()) {
            None => return
                Some(lazy_k_core::nm(&self.base[usize::try_from(n).unwrap()])),
            Some((f1, _)) if f1 == Zero::zero() => return None,
            Some((f1, _)) if f1 == GN::try_from(10).unwrap() => return None,
            Some((f1, o1)) => {
                match self.decompose(f1.clone()) {
                    Some((f2, _)) if f2 == One::one() => return None,
                    _ => (),
                }
                let f1e = match self.gn_to_min_lam(f1) {
                    None => return None,
                    Some(f1e) => f1e,
                };
                let o1e = match self.gn_to_min_lam(o1) {
                    None => return None,
                    Some(o1e) => o1e,
                };
                return Some(f1e * o1e);
            }
        }
    }

    pub fn lam_to_gn(&mut self, lam: &PLamExpr) -> GN {
        match lam.extract() {
            LamExpr::Nm { name } => {
                for n in 0..self.base.len() {
                    if **name == self.base[n] {
                        return GN::try_from(n).unwrap();
                    }
                }
                panic!("lam_to_gn: Nm");
            }
            LamExpr::App { func, oprd, size } => {
                let f = self.lam_to_gn(func);
                let o = self.lam_to_gn(oprd);
                self.prepare_count((size + 1) / 2);
                self.compose(f, o)
            }
            _ => panic!("lam_to_gn: other"),
        }
    }

}

#[test]
fn test_gn_builder_count() {
    let mut gnb = GNBuilder::new(vec!["I", "K", "S"]
                                .into_iter().map(|x| x.to_string()).collect());
    gnb.prepare_count(4);
    //assert_eq!( gnb, GNBuilder::new(vec![]) );
}

#[test]
fn test_gn_builder_gn() {
    fn n(i: u32) -> GN {
        GN::try_from(i).unwrap()
    }
    let mut gnb = GNBuilder::new(vec!["I", "K", "S"]
                                .into_iter().map(|x| x.to_string()).collect());
    gnb.prepare_gn(n(404));
    //assert_eq!( gnb, GNBuilder::new(vec![]) );
}

#[test]
fn test_count() {
    fn n(i: u32) -> GN {
        GN::try_from(i).unwrap()
    }
    let mut gnb = GNBuilder::new(vec!["I", "K", "S"]
                                .into_iter().map(|x| x.to_string()).collect());
    assert_eq!( gnb.count(n(    0)), 1 );
    assert_eq!( gnb.count(n(    2)), 1 );
    assert_eq!( gnb.count(n(    3)), 2 );
    assert_eq!( gnb.count(n(   11)), 2 );
    assert_eq!( gnb.count(n(   12)), 3 );
    assert_eq!( gnb.count(n(   65)), 3 );
    assert_eq!( gnb.count(n(   66)), 4 );
    assert_eq!( gnb.count(n(  470)), 4 );
    assert_eq!( gnb.count(n(  471)), 5 );
    assert_eq!( gnb.count(n(3_872)), 5 );
    assert_eq!( gnb.count(n(3_873)), 6 );
}

#[test]
fn test_compose_basic() {
    fn n(i: u32) -> GN {
        GN::try_from(i).unwrap()
    }
    let mut gnb = GNBuilder::new(vec!["I", "K", "S"]
                                .into_iter().map(|x| x.to_string()).collect());
    assert_eq!( gnb.compose(n(0), n(0)), n( 3) ); // I * I
    assert_eq!( gnb.compose(n(0), n(1)), n( 4) ); // I * K
    assert_eq!( gnb.compose(n(0), n(2)), n( 5) ); // I * S
    assert_eq!( gnb.compose(n(1), n(0)), n( 6) ); // K * I
    assert_eq!( gnb.compose(n(1), n(1)), n( 7) ); // K * K
    assert_eq!( gnb.compose(n(1), n(2)), n( 8) ); // K * S
    assert_eq!( gnb.compose(n(2), n(0)), n( 9) ); // S * I
    assert_eq!( gnb.compose(n(2), n(1)), n(10) ); // S * K
    assert_eq!( gnb.compose(n(2), n(2)), n(11) ); // S * S

    assert_eq!( gnb.compose(n(0), n( 3)), n(12) ); // I * II
    assert_eq!( gnb.compose(n(0), n( 4)), n(13) ); // I * IK
    assert_eq!( gnb.compose(n(0), n( 5)), n(14) ); // I * IS
    assert_eq!( gnb.compose(n(0), n( 6)), n(15) ); // I * KI
    assert_eq!( gnb.compose(n(0), n(11)), n(20) ); // I * SS
    assert_eq!( gnb.compose(n(1), n( 3)), n(21) ); // K * II
    assert_eq!( gnb.compose(n(1), n(11)), n(29) ); // K * SS
    assert_eq!( gnb.compose(n(2), n( 3)), n(30) );
    assert_eq!( gnb.compose(n(2), n(11)), n(38) );
    assert_eq!( gnb.compose(n(3), n( 0)), n(39) );
}

#[test]
fn test_decompose_basic() {
    fn n(i: u32) -> GN {
        GN::try_from(i).unwrap()
    }
    let mut gnb = GNBuilder::new(vec!["I", "K", "S"]
                                .into_iter().map(|x| x.to_string()).collect());
    assert_eq!( gnb.decompose(n(0)), None);
    assert_eq!( gnb.decompose(n(1)), None);
    assert_eq!( gnb.decompose(n(2)), None);

    assert_eq!( gnb.decompose(n( 3)), Some((n(0),n(0))) );
    assert_eq!( gnb.decompose(n( 4)), Some((n(0),n(1))) );
    assert_eq!( gnb.decompose(n( 5)), Some((n(0),n(2))) );
    assert_eq!( gnb.decompose(n( 6)), Some((n(1),n(0))) );
    assert_eq!( gnb.decompose(n( 7)), Some((n(1),n(1))) );
    assert_eq!( gnb.decompose(n( 8)), Some((n(1),n(2))) );
    assert_eq!( gnb.decompose(n( 9)), Some((n(2),n(0))) );
    assert_eq!( gnb.decompose(n(10)), Some((n(2),n(1))) );
    assert_eq!( gnb.decompose(n(11)), Some((n(2),n(2))) );

    assert_eq!( gnb.decompose(n(12)), Some((n(0),n(3))) );
    assert_eq!( gnb.decompose(n(13)), Some((n(0),n(4))) );
    assert_eq!( gnb.decompose(n(14)), Some((n(0),n(5))) );
    assert_eq!( gnb.decompose(n(15)), Some((n(0),n(6))) );
    assert_eq!( gnb.decompose(n(20)), Some((n(0),n(11))) );
    assert_eq!( gnb.decompose(n(21)), Some((n(1),n(3))) );
    assert_eq!( gnb.decompose(n(29)), Some((n(1),n(11))) );
    assert_eq!( gnb.decompose(n(30)), Some((n(2),n(3))) );
    assert_eq!( gnb.decompose(n(38)), Some((n(2),n(11))) );
    assert_eq!( gnb.decompose(n(39)), Some((n(3),n(0))) );
}

#[test]
fn test_decompose() {
    use super::lazy_k_read::read_lazy_k;
    fn test(a: &str, b: &str) {
        let mut gnb = GNBuilder::new(vec!["I", "K", "S"]
                                .into_iter().map(|x| x.to_string()).collect());
        let a = read_lazy_k(a).unwrap();
        let b = read_lazy_k(b).unwrap();
        let na = gnb.lam_to_gn(&a.clone());
        let nb = gnb.lam_to_gn(&b.clone());
        let nab = gnb.lam_to_gn(&(a*b));
        assert_eq!( gnb.decompose(nab), Some((na, nb)) );
    }
    test("``ssk", "`ks");
    test("```kssk", "`s`i`ks");
}
