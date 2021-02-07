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

type GN = BigInt;

#[derive(PartialEq, Eq, Debug)]
struct GNBuilder {
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
    pub fn count(&mut self, gn: GN) -> usize {
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
}

#[test]
fn test_gn_builder_count() {
    let mut gnb = GNBuilder::new(vec!["I".to_string(), "K".to_string(), "S".to_string()]);
    gnb.prepare_count(4);
    //assert_eq!( gnb, GNBuilder::new(vec![]) );
}

#[test]
fn test_gn_builder_gn() {
    fn n(i: u32) -> GN {
        GN::try_from(i).unwrap()
    }
    let mut gnb = GNBuilder::new(vec!["I".to_string(), "K".to_string(), "S".to_string()]);
    gnb.prepare_gn(n(404));
    //assert_eq!( gnb, GNBuilder::new(vec![]) );
}

#[test]
fn test_count() {
    fn n(i: u32) -> GN {
        GN::try_from(i).unwrap()
    }
    let mut gnb = GNBuilder::new(vec!["I".to_string(), "K".to_string(), "S".to_string()]);
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
    let mut gnb = GNBuilder::new(vec!["I".to_string(), "K".to_string(), "S".to_string()]);
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
    let mut gnb = GNBuilder::new(vec!["I".to_string(), "K".to_string(), "S".to_string()]);
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
    use super::goedel_number::{lam_to_n};
    fn test(a: &str, b: &str) {
        let mut gnb = GNBuilder::new(vec!["I".to_string(), "K".to_string(), "S".to_string()]);
        let a = read_lazy_k(a).unwrap();
        let b = read_lazy_k(b).unwrap();
        let (_, na) = lam_to_n(&a.clone());
        let (_, nb) = lam_to_n(&b.clone());
        let (_, nab) = lam_to_n(&(a*b));
        assert_eq!( gnb.decompose(nab), Some((na, nb)) );
    }
    test("``ssk", "`ks");
    test("```kssk", "`s`i`ks");
}
