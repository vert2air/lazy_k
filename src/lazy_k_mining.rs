use std::ops::Mul;
use std::rc::Rc;

use super::lazy_k_core;
use super::lazy_k_core::{LamExpr, PLamExpr, i, k, s};
use super::lazy_k_goedel_number;
use super::lazy_k_goedel_number::{OurInt, our1};
use super::lazy_k_read::read_lazy_k;

/*
pub fn mine_ch_num(a: PAnaLam) -> Result<(u32, u32), String> {
    a.to_lam().get_num_n(5_000)
}

fn (f: OurInt, t: Option<OurInt>) {
    let mut a = f;
    PAnaLam::first_min_from(a).set_n()
    if 
}
*/

impl PLamExpr {

    fn is_min(&self) -> bool {
        match self.extract() {
            LamExpr::App { func: f1, oprd: o1, .. } => {
                f1.is_min() && o1.is_min() && match f1.extract() {
                    LamExpr::Nm { name } if **name == "I" => false,
                    LamExpr::Nm { name }                  => true,
                    LamExpr::App { func: f2, oprd: o2, .. } =>
                        match (f2.extract(), o2.extract()) {
                            (LamExpr::Nm { name }, _)
                                if &**name == "K" => false,
                            (LamExpr::Nm { name: n2 }, LamExpr::Nm { name: n3 })
                                if &**n2 == "S" && &**n3 == "K" => false,
                            _ => true,
                        },
                    _ => false,
                }
            }
            LamExpr::Nm { name } if **name == "I" => true,
            LamExpr::Nm { name } if **name == "K" => true,
            LamExpr::Nm { name } if **name == "S" => true,
            _ => false,
        }
    }

    fn first_min_from(n: OurInt) -> Self {
        let an = lazy_k_goedel_number::n_to_unlam(n);
        if an.is_min() {
            an
        } else {
            an.next_min()
        }
    }

    fn first_min_size(n: usize) -> Self {
        let mut res = i();
        for _ in 1 .. (n + 1)/2 {
            res = k() * res
        }
        res
    }

    fn next_min(&self) -> Self {
        fn otherwise(f1: &PLamExpr, o1: &PLamExpr) -> PLamExpr {
            let f1_n = f1.next_min();
            let o1_n = o1.next_min();
            if f1.is_min() && o1_n.len() == o1.len() {
                f1.clone() * o1_n
            } else if f1_n.len() == f1.len() {
                f1_n * PLamExpr::first_min_size(o1.len())
            } else if f1_n.len() < 1 + f1.len() + o1.len() {
                f1_n.clone()
                    * PLamExpr::first_min_size(f1.len() + o1.len() - f1_n.len())
            } else {
                PLamExpr::first_min_size(f1.len() + o1.len() + 1 + 2)
            }
        }
        match self.extract() {
            LamExpr::App { func: f1, oprd: o1, .. } => {
                let a = match &*f1.extract() {
                    LamExpr::Nm { name } if **name == "I" =>
                        k() * Self::first_min_size(self.len() - 2),
                    LamExpr::App { func: f2, oprd: o2, .. } =>
                        match (&*f2.extract(), &*o2.extract()) {
                            (LamExpr::Nm { name }, _) if &**name == "K" =>
                                s() * Self::first_min_size(o2.len())
                                    * Self::first_min_size(o1.len()),
                            (LamExpr::Nm { name: n2 }, LamExpr::Nm { name: n3 })
                                if &**n2 == "S" && &**n3 == "K" =>
                                    s() * s() * Self::first_min_size(o1.len()),
                            _ => otherwise(f1, o1),
                        },
                    _ => otherwise(f1, o1),
                };
                a.try_min()
            }
            LamExpr::Nm { name } if **name == "I" => k(),
            LamExpr::Nm { name } if **name == "K" => s(),
            LamExpr::Nm { name } if **name == "S" => k() * i(),
            _ => panic!("next_min"),
        }
    }

    fn try_min(&self) -> Self {
        match self.extract() {
            LamExpr::Nm {..} => (*self).clone(),
            LamExpr::App {..} if self.is_min() => self.clone(),
            _ => self.next_min(),
        }
    }

}


#[test]
fn test_first_min_size() {
    assert_eq!(PLamExpr::first_min_size(1), read_lazy_k("i").unwrap());
    assert_eq!(PLamExpr::first_min_size(3), read_lazy_k("`ki").unwrap());
    assert_eq!(PLamExpr::first_min_size(5), read_lazy_k("`k`ki").unwrap());
    assert_eq!(PLamExpr::first_min_size(7), read_lazy_k("`k`k`ki").unwrap());
}

#[test]
fn test_next_min() {
    let a = read_lazy_k("i").unwrap();
    let a = a.next_min(); assert_eq!(a, read_lazy_k("k").unwrap());
    let a = a.next_min(); assert_eq!(a, read_lazy_k("s").unwrap());
    let a = a.next_min(); assert_eq!(a, read_lazy_k("`ki").unwrap());
    let a = a.next_min(); assert_eq!(a, read_lazy_k("`kk").unwrap());
    let a = a.next_min(); assert_eq!(a, read_lazy_k("`ks").unwrap());
    let a = a.next_min(); assert_eq!(a, read_lazy_k("`si").unwrap());
    let a = a.next_min(); assert_eq!(a, read_lazy_k("`sk").unwrap());
    let a = a.next_min(); assert_eq!(a, read_lazy_k("`ss").unwrap());
    let a = a.next_min(); assert_eq!(a, read_lazy_k("`k`ki").unwrap());
    let a = a.next_min(); assert_eq!(a, read_lazy_k("`k`kk").unwrap());
    let a = a.next_min(); assert_eq!(a, read_lazy_k("`k`ks").unwrap());
    let a = a.next_min(); assert_eq!(a, read_lazy_k("`k`si").unwrap());
    let a = a.next_min(); assert_eq!(a, read_lazy_k("`k`sk").unwrap());
    let a = a.next_min(); assert_eq!(a, read_lazy_k("`k`ss").unwrap());
    let a = a.next_min(); assert_eq!(a, read_lazy_k("`s`ki").unwrap());
}
