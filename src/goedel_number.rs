extern crate num_traits;

use std::cmp::{PartialOrd, Ordering};
use std::ops::Sub;
use std::vec::Vec;
use num_bigint::BigInt;
use num_traits::Zero;
use std::convert::TryFrom;

use super::lazy_k_core;
use super::lazy_k_core::{PLamExpr, LamExpr};

pub type GN = BigInt;

#[derive(PartialEq, Eq, Debug)]
pub struct GNBuilder {
    num: Vec<GN>,
    acc: Vec<GN>,
    pair_num: Vec<Vec<GN>>,
    pair_acc: Vec<Vec<GN>>,
    base: Vec<String>,
    i: GN,
    k: GN,
    s: GN,
    sk: GN,
}

impl GNBuilder {

    pub fn new(b: Vec<String>) -> Self {
        let ob = GN::try_from(b.len()).unwrap();
        let mut i = GN::try_from(-1).unwrap();
        let mut k = GN::try_from(-1).unwrap();
        let mut s = GN::try_from(-1).unwrap();
        let blen = GN::try_from(b.len()).unwrap();
        for (idx, c) in b.iter().enumerate() {
            match c {
                x if x == "I" => i = GN::try_from(idx).unwrap(),
                x if x == "K" => k = GN::try_from(idx).unwrap(),
                x if x == "S" => s = GN::try_from(idx).unwrap(),
                _ => (),
            }
        }
        GNBuilder {
            num: vec![Zero::zero(), ob.clone()],
            acc: vec![Zero::zero(), ob],
            pair_num: vec![vec![], vec![Zero::zero()]],
            pair_acc: vec![vec![], vec![Zero::zero()]],
            i: i,
            k: k.clone(),
            s: s.clone(),
            //sk: blen * (s + One::one()) + k,
            sk: blen.clone() * s + blen + k,
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
        let (g, t) = sub_rem(on, &self.pair_acc[cnt]);
        let om = t.clone()        % self.num[cnt - (g + 1)].clone();
        let od = (t - om.clone()) / self.num[cnt - (g + 1)].clone();
        Some( (od + self.acc[g].clone(),
                om + self.acc[cnt - g - 2].clone()) )
    }

    /// ```
    /// use lazy_k::goedel_number::{GNBuilder, GN};
    /// use lazy_k::lazy_k_read::read_lazy_k;
    /// use std::convert::TryFrom;
    /// use num_bigint::BigInt;
    /// 
    /// fn n(a: i32) -> GN {
    ///     match GN::try_from(a) {
    ///         Ok(a2) => a2,
    ///         _ => panic!("bn"),
    ///     }
    /// }
    /// let mut gnb = GNBuilder::new(vec!["I", "K", "S"]
    ///                         .into_iter().map(|x| x.to_string()).collect());
    /// assert_eq!( Ok( gnb.gn_to_lam(n( 0)) ), read_lazy_k("i")     );
    /// assert_eq!( Ok( gnb.gn_to_lam(n( 1)) ), read_lazy_k("k")     );
    /// assert_eq!( Ok( gnb.gn_to_lam(n( 2)) ), read_lazy_k("s")     );
    /// assert_eq!( Ok( gnb.gn_to_lam(n( 3)) ), read_lazy_k("`ii")   );
    /// assert_eq!( Ok( gnb.gn_to_lam(n( 4)) ), read_lazy_k("`ik")   );
    /// assert_eq!( Ok( gnb.gn_to_lam(n( 5)) ), read_lazy_k("`is")   );
    /// assert_eq!( Ok( gnb.gn_to_lam(n( 6)) ), read_lazy_k("`ki")   );
    /// assert_eq!( Ok( gnb.gn_to_lam(n( 7)) ), read_lazy_k("`kk")   );
    /// assert_eq!( Ok( gnb.gn_to_lam(n( 8)) ), read_lazy_k("`ks")   );
    /// assert_eq!( Ok( gnb.gn_to_lam(n( 9)) ), read_lazy_k("`si")   );
    /// assert_eq!( Ok( gnb.gn_to_lam(n(10)) ), read_lazy_k("`sk")   );
    /// assert_eq!( Ok( gnb.gn_to_lam(n(11)) ), read_lazy_k("`ss")   );
    /// assert_eq!( Ok( gnb.gn_to_lam(n(56)) ), read_lazy_k("``kss") );
    /// assert_eq!( Ok( gnb.gn_to_lam(n(60)) ), read_lazy_k("``ski") );
    /// 
    /// let mut gnb = GNBuilder::new(vec!["iota".to_string()]);
    /// assert_eq!( Ok( gnb.gn_to_lam(n( 1)) ), read_lazy_k("*ii") );
    /// assert_eq!( Ok( gnb.gn_to_lam(n( 2)) ), read_lazy_k("*i*ii") );
    /// assert_eq!( Ok( gnb.gn_to_lam(n( 4)) ), read_lazy_k("*i*i*ii") );
    /// assert_eq!( Ok( gnb.gn_to_lam(n( 9)) ), read_lazy_k("*i*i*i*ii") );
    /// ```
    pub fn gn_to_lam(&mut self, n: GN) -> PLamExpr {
        match self.decompose(n.clone()) {
            Some((f, o)) => self.gn_to_lam(f) * self.gn_to_lam(o),
            None => lazy_k_core::nm(&self.base[usize::try_from(n).unwrap()]),
        }
    }

    /// Transform an Integer of Goedel Number to Combinator style expression.
    /// But if there is a shorter Combinator style expression obviously,
    /// This function returns None.
    ///
    /// ```
    /// use lazy_k::goedel_number::{GNBuilder, GN};
    /// use lazy_k::lazy_k_read::read_lazy_k;
    /// use std::convert::TryFrom;
    /// 
    /// fn bn(a: i32) -> GN {
    ///     GN::try_from(a).unwrap()
    /// }
    /// let mut gnb = GNBuilder::new(vec!["I", "K", "S"]
    ///                         .into_iter().map(|x| x.to_string()).collect());
    /// assert_eq!( gnb.gn_to_min_lam(bn( 3)), None ); // `ii -> i
    /// assert_eq!( gnb.gn_to_min_lam(bn( 4)), None ); // `ik -> k
    /// assert_eq!( gnb.gn_to_min_lam(bn( 5)), None ); // `is -> s
    /// assert_eq!( gnb.gn_to_min_lam(bn(56)), None ); // ``kss -> s (kXY -> Y
    /// assert_eq!( gnb.gn_to_min_lam(bn(60)), None ); // ``ski -> i
    /// ```
    pub fn gn_to_min_lam(&mut self, n: GN) -> Option<PLamExpr> {
        match self.decompose(n.clone()) {
            None => return
                Some(lazy_k_core::nm(&self.base[usize::try_from(n).unwrap()])),
            // I _
            Some((f1, _)) if f1 == self.i => return None,
            // S K _
            Some((f1, _)) if f1 == self.sk => return None,
            Some((f1, o1)) => {
                match self.decompose(f1.clone()) {
                    // K _ _
                    Some((f2, _)) if f2 == self.k => return None,
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

    /// ```
    /// use lazy_k::goedel_number::{GNBuilder, GN};
    /// use lazy_k::lazy_k_read::read_lazy_k;
    /// use std::convert::TryFrom;
    /// 
    /// fn n(num: u32) -> GN {
    ///     GN::try_from(num).unwrap()
    /// };
    /// let mut gnb = GNBuilder::new(vec!["I", "K", "S"]
    ///                         .into_iter().map(|x| x.to_string()).collect());
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("i").unwrap()), n(0));
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("k").unwrap()), n(1));
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("s").unwrap()), n(2));
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("`ii").unwrap()), n(3));
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("`ik").unwrap()), n(4));
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("`is").unwrap()), n(5));
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("`ki").unwrap()), n(6));
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("`kk").unwrap()), n(7));
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("`ks").unwrap()), n(8));
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("`si").unwrap()), n(9));
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("`sk").unwrap()), n(10));
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("`ss").unwrap()), n(11));
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("`i`ii").unwrap()), n(12));
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("`i`ik").unwrap()), n(13));
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("`i`is").unwrap()), n(14));
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("`i`ki").unwrap()), n(15));
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("``kss").unwrap()), n(56));
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("``ski").unwrap()), n(60));
    /// 
    /// let mut gnb = GNBuilder::new(vec!["iota".to_string()]);
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("*ii").unwrap()), n(1));
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("*i*ii").unwrap()), n(2));
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("**iii").unwrap()), n(3));
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("*i*i*ii").unwrap()), n(4));
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("*i**iii").unwrap()), n(5));
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("**ii*ii").unwrap()), n(6));
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("**i*iii").unwrap()), n(7));
    /// assert_eq!( gnb.lam_to_gn(&read_lazy_k("***iiii").unwrap()), n(8));
    /// 
    /// let mut gnb = GNBuilder::new(vec!["I", "K", "S"]
    ///                         .into_iter().map(|x| x.to_string()).collect());
    /// assert_eq!(gnb.lam_to_gn(&read_lazy_k("``s`k``s`si`kik").unwrap()),
    ///                                                 n(2_471_467));
    /// assert_eq!(gnb.lam_to_gn(&read_lazy_k("``s`k``s`si`sik").unwrap()),
    ///                                                 n(2_471_476));
    /// ```
    pub fn lam_to_gn(&mut self, lam: &PLamExpr) -> GN {
        match lam.extract() {
            LamExpr::Nm { name } => {
                for n in 0..self.base.len() {
                    if **name == self.base[n] {
                        return GN::try_from(n).unwrap();
                    }
                }
                panic!("lam_to_gn: Nm : {}", name);
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

    /// ```
    /// use lazy_k::lazy_k_core::{PLamExpr, i, k, s};
    /// use lazy_k::lazy_k_read::read_lazy_k;
    /// use lazy_k::goedel_number::{GNBuilder, GN};
    /// use num_traits::{Zero, One};
    ///
    /// fn str_to_gn(gnb: &mut GNBuilder, lam: &str) -> GN {
    ///     gnb.lam_to_gn(&read_lazy_k(lam).unwrap())
    /// }
    /// let mut gnb = GNBuilder::new(vec!["I", "K", "S"]
    ///                         .into_iter().map(|x| x.to_string()).collect());
    /// let a = str_to_gn(&mut gnb, "II");
    /// let b = str_to_gn(&mut gnb, "I");
    /// let mut yet = true;
    /// assert_eq!( gnb.beta_red_cc(&mut yet, a), Some(b) );
    /// 
    /// let a = str_to_gn(&mut gnb, "SKSK");
    /// let b = str_to_gn(&mut gnb, "K");
    /// let mut yet = true;
    /// assert_eq!( gnb.beta_red_cc(&mut yet, a), Some(b) );
    /// 
    /// let a = str_to_gn(&mut gnb, "KS(KS)");
    /// let b = str_to_gn(&mut gnb, "S");
    /// let mut yet = true;
    /// assert_eq!( gnb.beta_red_cc(&mut yet, a), Some(b) );
    /// 
    /// println!("Sxyz in unlambda style");
    /// let a = str_to_gn(&mut gnb, "```sski");
    /// let b = str_to_gn(&mut gnb, "``si`ki");
    /// let mut yet = true;
    /// if let Some(a_gn) = gnb.beta_red_cc(&mut yet, a.clone()) {
    ///     println!("a_gn = {}", gnb.gn_to_lam(a_gn).to_unlam().unwrap());
    /// }
    /// let mut yet = true;
    /// assert_eq!( gnb.beta_red_cc(&mut yet, a), Some(b) );
    /// 
    /// println!("2nd Sxyz isn't xlated.");
    /// let a = str_to_gn(&mut gnb, "`i ` ```sski ```sski");
    /// let b = str_to_gn(&mut gnb, "```si`ki```sski");
    /// let mut yet = true;
    /// if let Some(a_gn) = gnb.beta_red_cc(&mut yet, a.clone()) {
    ///     println!("a_gn = {}", gnb.gn_to_lam(a_gn).to_unlam().unwrap());
    /// }
    /// let mut yet = true;
    /// assert_eq!( gnb.beta_red_cc(&mut yet, a), Some(b) );
    /// 
    /// println!("after 1st Sxyz");
    /// let a = str_to_gn(&mut gnb, "`i ` ```sski ``ksi");
    /// let b = str_to_gn(&mut gnb, "```si`kis");
    /// let mut yet = true;
    /// assert_eq!( gnb.beta_red_cc(&mut yet, a), Some(b) );
    /// ```
    pub fn beta_red_cc(&mut self, not_reduce_s_yet: &mut bool, gn: GN) ->
                                                                Option<GN> {
        match self.decompose(gn) {
            None => None,

            // I o1 ==beta=> o1
            Some((f1, o1)) if f1 == self.i => match self.decompose(o1.clone()) {
                None => Some(o1),
                Some((f, o)) => {
                    let p = self.beta_red_cc(not_reduce_s_yet, f.clone());
                    let q = self.beta_red_cc(not_reduce_s_yet, o.clone());
                    match (p, q) {
                        (Some(f_n), Some(o_n)) => Some(self.compose(f_n, o_n)),
                        (Some(f_n), None     ) => Some(self.compose(f_n, o)),
                        (None,      Some(o_n)) => Some(self.compose(f,  o_n)),
                        (None,      None     ) => Some(o1),
                    }
                }
            }

            // (K|S) o1 ==beta=> (K|S) o1
            Some((f1, o1)) if (f1 == self.k) || (f1 == self.s) => {
                match self.beta_red_cc(not_reduce_s_yet, o1.clone()) {
                    None => None,
                    Some(o1n) => Some(f1 * o1n),
                }
            }

            // S K o1 ==beta=> I
            Some((f1, _o1)) if f1 == self.sk => Some(self.i.clone()),

            Some((f1, o1)) => match self.decompose(f1.clone()) {
                None => None,  // Never come here.

                // I o2 o1 ==beta=> o2 o1
                Some((f2, o2)) if f2 == self.i => {
                    let p = self.beta_red_cc(not_reduce_s_yet, o2.clone());
                    let q = self.beta_red_cc(not_reduce_s_yet, o1.clone());
                    match (p, q) {
                        (Some(o2n), Some(o1n)) => Some(self.compose(o2n, o1n)),
                        (Some(o2n), None     ) => Some(self.compose(o2n, o1)),
                        (None,      Some(o1n)) => Some(self.compose(o2,  o1n)),
                        (None,      None     ) => Some(self.compose(o2,  o1)),
                    }
                }

                // K o2 o1 ==beta=> o2
                Some((f2, o2)) if f2 == self.k => Some(o2),

                // S o2 o1 ==beta=> S o2 o1
                Some((f2, o2)) if f2 == self.s => {
                    let p = self.beta_red_cc(not_reduce_s_yet, o2.clone());
                    let q = self.beta_red_cc(not_reduce_s_yet, o1.clone());
                    match (p, q) {
                        (Some(o2n), Some(o1n)) => {
                                                let a = self.compose(f2, o2n);
                                                Some(self.compose(a, o1n))
                                            }
                        (Some(o2n), None     ) => {
                                                let a = self.compose(f2, o2n);
                                                Some(self.compose(a, o1))
                                            }
                        (None,      Some(o1n)) => {
                                                let a = self.compose(f2, o2);
                                                Some(self.compose(a, o1n))
                                            }
                        (None,      None     ) => None,
                    }
                }

                // S K o2 o1 ==beta=> o1
                Some((f2, _o2)) if f2 == self.sk => Some(o1),

                Some((f2, o2)) => match self.decompose(f2.clone()) {

                    // I o3 o2 o1 ==beta=> o3 o2 o1
                    Some((f3, o3)) if f3 == self.i => {
                        let a = self.compose(o3.clone(), o2);
                        let p = self.beta_red_cc(not_reduce_s_yet, a.clone());
                        let q = self.beta_red_cc(not_reduce_s_yet, o1.clone());
                        match (p, q) {
                        (Some(an), Some(o1n)) => Some(self.compose(an, o1n)),
                        (Some(an), None     ) => Some(self.compose(an, o1)),
                        (None,     Some(o1n)) => Some(self.compose(a, o1n)),
                        (None,     None     ) => Some(self.compose(a,  o1)),
                        }
                    }

                    // K o3 o2 o1 ==beta=> o3 o1
                    Some((f3, o3)) if f3 == self.k => {
                        let p = self.beta_red_cc(not_reduce_s_yet, o3.clone());
                        let q = self.beta_red_cc(not_reduce_s_yet, o1.clone());
                        match (p, q) {
                        (Some(o3n), Some(o1n)) => Some(self.compose(o3n, o1n)),
                        (Some(o3n), None     ) => Some(self.compose(o3n, o1)),
                        (None,      Some(o1n)) => Some(self.compose(o3, o1n)),
                        (None,      None     ) => Some(self.compose(o3,  o1)),
                        }
                    }

                    // S o3 o2 o1 ==beta=> o3 o1 (o2 o1)
                    Some((f3, o3)) if f3 == self.s => {
                        if *not_reduce_s_yet {
                            *not_reduce_s_yet = false;
                            let o31 = self.compose(o3, o1.clone());
                            let o21 = self.compose(o2, o1);
                            let p = self.beta_red_cc(not_reduce_s_yet,
                                                                o31.clone());
                            let q = self.beta_red_cc(not_reduce_s_yet,
                                                                o21.clone());
                            match (p, q) {
                                (Some(f), Some(o)) => Some(self.compose(f, o)),
                                (Some(f), None  ) => Some(self.compose(f, o21)),
                                (None,   Some(o)) => Some(self.compose(o31, o)),
                                (None,   None ) => Some(self.compose(o31, o21)),
                            }
                        } else {
                            let p = self.beta_red_cc(not_reduce_s_yet,
                                                                f1.clone());
                            let q = self.beta_red_cc(not_reduce_s_yet,
                                                                o1.clone());
                            match (p, q) {
                        (Some(f1n), Some(o1n)) => Some(self.compose(f1n, o1n)),
                        (Some(f1n), None     ) => Some(self.compose(f1n, o1)),
                        (None,      Some(o1n)) => Some(self.compose(f1, o1n)),
                        (None,      None     ) => None,
                            }
                        }
                    }

                    _ => {
                        let p = self.beta_red_cc(not_reduce_s_yet, f1.clone());
                        let q = self.beta_red_cc(not_reduce_s_yet, o1.clone());
                        match (p, q) {
                        (Some(f1n), Some(o1n)) => Some(self.compose(f1n, o1n)),
                        (Some(f1n), None     ) => Some(self.compose(f1n, o1)),
                        (None,      Some(o1n)) => Some(self.compose(f1, o1n)),
                        (None,      None     ) => None,
                        }
                    }
                }
            }
        }
    }

    pub fn beta_red_cc2(&mut self, not_reduce_s_yet: &mut bool, gn: GN) ->
                                                                Option<GN> {
        match self.decompose(gn) {
            None => None,

            // I o1 ==beta=> o1
            Some((f1, o1)) if f1 == self.i => match self.decompose(o1.clone()) {
                None => Some(o1),
                Some((f, o)) => {
                    let p = self.beta_red_cc(not_reduce_s_yet, f.clone());
                    let q = self.beta_red_cc(not_reduce_s_yet, o.clone());
                    match (p, q) {
                        (Some(f_n), Some(o_n)) => Some(self.compose(f_n, o_n)),
                        (Some(f_n), None     ) => Some(self.compose(f_n, o)),
                        (None,      Some(o_n)) => Some(self.compose(f,  o_n)),
                        (None,      None     ) => Some(o1),
                    }
                }
            }

            // S K o1 ==beta=> I
            Some((f1, _o1)) if f1 == self.sk => Some(self.i.clone()),

            Some((f1, o1)) => match self.decompose(f1.clone()) {
                None => None,  // Never come here.

                // K o2 o1 ==beta=> o2
                Some((f2, o2)) if f2 == self.k => Some(o2),

                // S K o2 o1 ==beta=> o1
                Some((f2, _o2)) if f2 == self.sk => Some(o1),

                Some((f2, o2)) => match self.decompose(f2.clone()) {

                    // S o3 o2 o1 ==beta=> o3 o1 (o2 o1)
                    Some((f3, o3)) if f3 == self.s => {
                        if *not_reduce_s_yet {
                            *not_reduce_s_yet = false;
                            let o31 = self.compose(o3, o1.clone());
                            let o21 = self.compose(o2, o1);
                            let p = self.beta_red_cc(not_reduce_s_yet,
                                                                o31.clone());
                            let q = self.beta_red_cc(not_reduce_s_yet,
                                                                o21.clone());
                            match (p, q) {
                                (Some(f), Some(o)) => Some(self.compose(f, o)),
                                (Some(f), None  ) => Some(self.compose(f, o21)),
                                (None,   Some(o)) => Some(self.compose(o31, o)),
                                (None,   None ) => Some(self.compose(o31, o21)),
                            }
                        } else {
                            let p = self.beta_red_cc(not_reduce_s_yet,
                                                                f1.clone());
                            let q = self.beta_red_cc(not_reduce_s_yet,
                                                                o1.clone());
                            match (p, q) {
                        (Some(f1n), Some(o1n)) => Some(self.compose(f1n, o1n)),
                        (Some(f1n), None     ) => Some(self.compose(f1n, o1)),
                        (None,      Some(o1n)) => Some(self.compose(f1, o1n)),
                        (None,      None     ) => None,
                            }
                        }
                    }

                    _ => {
                        let p = self.beta_red_cc(not_reduce_s_yet, f1.clone());
                        let q = self.beta_red_cc(not_reduce_s_yet, o1.clone());
                        match (p, q) {
                        (Some(f1n), Some(o1n)) => Some(self.compose(f1n, o1n)),
                        (Some(f1n), None     ) => Some(self.compose(f1n, o1)),
                        (None,      Some(o1n)) => Some(self.compose(f1, o1n)),
                        (None,      None     ) => None,
                        }
                    }
                }
            }
        }
    }
}

fn sub_rem<T: Ord + Sub<Output = T> + Clone>(n0: T, ns: &Vec<T>) -> (usize, T) {
    let mut f = 0;
    let mut t = ns.len() - 1;
    loop {
        match t - f {
            d if d == 0 => return (f, n0 - ns[f].clone()),
            d if d == 1 => return if n0 < ns[t] { (f, n0 - ns[f].clone()) }
                                            else { (t, n0 - ns[t].clone()) },
            _ => (),
        }
        let m = (f + t) / 2;
        match n0.cmp(&ns[m + 1]) {
            Ordering::Equal => return (m + 1, n0 - ns[m + 1].clone()),
            Ordering::Less   => t = m,
            Ordering::Greater => f = m,
        }
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

#[test]
fn test_sub_rem() {
    assert_eq!( sub_rem(0, &vec![0, 3]), (0, 0) );
    assert_eq!( sub_rem(1, &vec![0, 3]), (0, 1) );
    assert_eq!( sub_rem(2, &vec![0, 3]), (0, 2) );
    assert_eq!( sub_rem(4, &vec![0, 9, 12]), (0, 4) );
    assert_eq!( sub_rem(8, &vec![0, 9, 12]), (0, 8) );
    assert_eq!( sub_rem(9, &vec![0, 9, 12]), (1, 0) );
    assert_eq!( sub_rem(10, &vec![0, 9, 12]), (1, 1) );
    assert_eq!( sub_rem(11, &vec![0, 9, 12]), (1, 2) );
}

#[test]
fn test_read_n_to_unlam() {
    use super::lazy_k_read::read_lazy_k;
    let mut gnb = GNBuilder::new(vec!["I", "K", "S"]
                                .into_iter().map(|x| x.to_string()).collect());
    fn gn(a: i32) -> GN {
        match GN::try_from(a) {
            Ok(a2) => a2,
            _ => panic!("n"),
        }
    }
    fn check(gnb: &mut GNBuilder, n: &GN) {
        let ul = gnb.gn_to_lam(n.clone()); // PLamExpr
        let st = ul.to_unlam().unwrap();        // String
        let cc = read_lazy_k(&st).unwrap();     // PLamExpr
        let n2 = gnb.lam_to_gn(&cc);        // GN
        println!("Goedel number: {} <=> {} <=> {}", n.clone(), st, n2.clone());
        assert_eq!( n.clone(), n2 );
    }
    let mut n = gn(100);
    //for _ in 1..100 {
    for _ in 1..5 {
        check(&mut gnb, &n);
        n *= gn(100);
    }
}

