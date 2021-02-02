use num_bigint::BigInt;
use num_traits::{Zero, One};
use std::collections::BTreeMap;
use std::convert::TryFrom;
use std::fs;

use super::lazy_k_read;
use super::lazy_k_core;
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

struct LenToNum {
    num: Vec<OurInt>,
    acc: Vec<OurInt>,
    pair: Vec<Vec<OurInt>>,
    base: OurInt,
}

impl LenToNum {

    fn new(b: i32) -> Self {
        let ob = OurInt::try_from(b).unwrap();
        LenToNum {
            num: vec![ob],
            acc: vec![ob],
            pair: vec![vec![]],
            base: ob,
        }
    }

    fn prepare_len(&self, len: usize) {
        let idx = len - 1;
        match self.num.get(idx) {
            Some(_) => (),
            None => {
                self.prepare_len(idx);
                let mut res = Vec::new();
                for i in 0 .. idx {
                    res.push(self.num[i] * self.num[idx - i - 1]);
                }
                self.pair.insert(idx, res);
                let mut s = Zero::zero();
                for p in self.pair.get(idx).unwrap().iter() {
                    s += p;
                }
                self.num.insert(idx, s);
                self.acc.insert(idx, self.num.get(idx).unwrap()
                                    + self.acc.get(idx - 1).unwrap());
            }
        }
    }

    fn prepare_gn(&self, gn: OurInt) {
        loop {
            if gn < self.acc[self.acc.len() - 1] {
                break;
            }
            self.prepare_len(self.acc.len() + 1)
        }
    }

    /// Return the number of all expressions which has 'len' functions 
    /// ```
    /// fn n(num: u32) -> OurInt {
    ///     match OurInt::try_from(num) {
    ///         Ok(a) => a,
    ///         _ => panic!("lam_to_n(0)"),
    ///     }
    /// };
    /// 
    /// let l2n = LenToNum::new(3);
    /// assert_eq!( l2n.get(n(1)), n(3) )
    /// assert_eq!( l2n.get(n(2)), n(3 * 3) )       // 9
    /// //assert_eq!( l2n.get(n(3)), n(3 * 9 * 2) )   // 54
    /// assert_eq!( l2n.get(n(4)), n(3 * 54 * 2 + 9 * 9) )
    /// ```
    fn get(&mut self, len: &usize) -> OurInt {
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

