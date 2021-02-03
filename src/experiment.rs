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
//use super::goedel_number::{OurInt, mul_up_down};
use super::goedel_number::{OurInt};

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

struct GNBuilder {
    num: Vec<GN>,
    acc: Vec<GN>,
    pair_num: Vec<Vec<GN>>,
    pair_acc: Vec<Vec<GN>>,
    base: String[],
}

impl GNBuilder {

    pub fn new(b: String[]) -> Self {
        let ob = GN::try_from(b.len()).unwrap();
        GNBuilder {
            num: vec![ob],
            acc: vec![ob],
            pair_num: vec![vec![]],
            pair_acc: vec![vec![]],
            base: b,
        }
    }

    fn prepare_count(&self, cnt: usize) {
        let idx = cnt - 1;
        match self.num.get(idx) {
            Some(_) => (),
            None => {
                self.prepare_count(idx);
                let mut res = Vec::new();
                for i in 0 .. idx {
                    res.push(self.num[i] * self.num[idx - i - 1]);
                }
                self.pair_num.insert(idx, res);

                let mut s = Zero::zero();
                for p in self.pair_num.get(idx).unwrap().iter() {
                    s += p;
                }
                self.num.insert(idx, s);
                self.acc.insert(idx, self.num.get(idx).unwrap()
                                    + self.acc.get(idx - 1).unwrap());
            }
        }
    }

    fn prepare_gn(&self, gn: GN) {
        loop {
            if gn < self.acc[self.acc.len() - 1] {
                break;
            }
            self.prepare_len(self.acc.len());
        }
    }

    /// the Number of I, K, S
    pub fn count(&self, gn: GN) -> usize {
        self.prepare_gn(gn);
        for c in RevIter::new(self.acc.len() - 1, 0) {
            if gn < self.acc.get(c).unwrap() {
                return c + 1;
            }
        }
    }

    pub fn compose(&self, nf: GN, no: GN) -> GN {
        let total_cnt = self.count(nf) + self.count(no);
        self.prepare_count(total_cnt);
        let (_, nf2) = sub_rem(nf, self.acc);
        let (_, no2) = sub_rem(no, self.acc);
        //self.count(nf)
        self.num
    }

    /// Return the number of all expressions which has 'len' functions 
    /// ```
    /// fn n(num: u32) -> GN {
    ///     match GN::try_from(num) {
    ///         Ok(a) => a,
    ///         _ => panic!("lam_to_n(0)"),
    ///     }
    /// };
    /// 
    /// let l2n = GNBuilder::new(3);
    /// assert_eq!( l2n.get(n(1)), n(3) )
    /// assert_eq!( l2n.get(n(2)), n(3 * 3) )       // 9
    /// //assert_eq!( l2n.get(n(3)), n(3 * 9 * 2) )   // 54
    /// assert_eq!( l2n.get(n(4)), n(3 * 54 * 2 + 9 * 9) )
    /// ```
    fn get(&mut self, len: &usize) -> GN {
        let idx = len - 1;
        match self.num.get(idx) {
            Some(n) => n,
            None => {
                self.prepare(len);
                self.num.get(idx).unrwap()
            }
        }
    }
}




/*
enum LERed{
    App {
        org_gn: BigNum,
        size: usize,
        f: BigNum
        o: BigNum,

    }
    Nm {
    },
}*/

