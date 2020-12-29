use std::ops::Mul;
use std::rc::Rc;

use super::lazy_k_core;
use super::lazy_k_core::{LamExpr, PLamExpr};
use super::lazy_k_goedel_number;
use super::lazy_k_goedel_number::{OurInt, our1};
use super::lazy_k_read::read_lazy_k;

#[derive(Eq, PartialEq)]
enum AnaLam {
    Comb {
        size: usize,
        is_min: bool,
        n: Option<OurInt>,
        comb: Rc<String>,
    },
    App {
        size: usize,
        is_min: bool,
        n: Option<OurInt>,
        func: PAnaLam,
        oprd: PAnaLam,
    },
}

struct PAnaLam(Rc<AnaLam>);

fn nm(n: &str) -> PAnaLam {
    PAnaLam(Rc::new(AnaLam::Comb {
        size: 1, is_min: true, n: Some(our1()), comb: Rc::new(n.to_string())
    }))
}
fn i() -> PAnaLam { nm("I") }
fn k() -> PAnaLam { nm("K") }
fn s() -> PAnaLam { nm("S") }

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
impl PAnaLam {

    fn new_from_lam(lam: &PLamExpr) -> Self {
        match lam.extract() {
            LamExpr::App  { func: f1, oprd: o1, .. } =>
                Self::new_from_lam(f1) * Self::new_from_lam(o1),
            LamExpr::Nm { name } if **name == "I" => i(),
            LamExpr::Nm { name } if **name == "K" => k(),
            LamExpr::Nm { name } if **name == "S" => s(),
            _ => panic!("new_from_lam"),
        }
    }

    fn first_min_from(n: OurInt) -> Self {
        let an = Self::new_from_lam(&lazy_k_goedel_number::n_to_unlam(n));
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
        fn otherwise(f1: &PAnaLam, o1: &PAnaLam) -> PAnaLam {
            let f1_n = f1.next_min();
            let o1_n = o1.next_min();
            if f1.is_min() && o1_n.len() == o1.len() {
                f1.clone() * o1_n
            } else if f1_n.len() == f1.len() {
                f1_n * PAnaLam::first_min_size(o1.len())
            } else if f1_n.len() < 1 + f1.len() + o1.len() {
                f1_n.clone()
                    * PAnaLam::first_min_size(f1.len() + o1.len() - f1_n.len())
            } else {
                PAnaLam::first_min_size(f1.len() + o1.len() + 1 + 2)
            }
        }
        match &*self.0 {
            AnaLam::App  { func: f1, oprd: o1, .. } => {
                let a = match &*f1.0 {
                    AnaLam::Comb { comb, .. } if **comb == "I" =>
                        k() * Self::first_min_size(self.len() - 2),
                    AnaLam::App { func: f2, oprd: o2, .. } =>
                        match (&*f2.0, &*o2.0) {
                            (AnaLam::Comb { comb, .. }, _) if &**comb == "K" =>
                                s() * Self::first_min_size(o2.len())
                                    * Self::first_min_size(o1.len()),
                            (AnaLam::Comb { comb: c2, .. },
                                                AnaLam::Comb { comb: c3, .. })
                                if &**c2 == "S" && &**c3 == "K" =>
                                    s() * s() * Self::first_min_size(o1.len()),
                            _ => otherwise(f1, o1),
                        },
                    _ => otherwise(f1, o1),
                };
                a.try_min()
            }
            AnaLam::Comb { comb, .. } if **comb == "I" => k(),
            AnaLam::Comb { comb, .. } if **comb == "K" => s(),
            AnaLam::Comb { comb, .. } if **comb == "S" => k() * i(),
            _ => panic!("next_min"),
        }
    }

    fn try_min(&self) -> Self {
        match &*self.0 {
            AnaLam::Comb {..} => (*self).clone(),
            AnaLam::App { is_min, ..} if *is_min => self.clone(),
            _ => self.next_min(),
        }
    }

    fn len(&self) -> usize {
        match *self.0 {
            AnaLam::Comb { size, .. } => size,
            AnaLam::App  { size, .. } => size,
        }
    }

    fn is_min(&self) -> bool {
        match *self.0 {
            AnaLam::Comb { is_min, .. } => is_min,
            AnaLam::App  { is_min, .. } => is_min,
        }
    }

    fn set_n(mut self) -> Self {
        match &*self.0 {
            AnaLam::Comb {..} => (),   // Comb's n is always not None.
            AnaLam::App  { size, is_min, n, func, oprd } if *n == None => {
                let (_, gn) = lazy_k_goedel_number::lam_to_n(&self.to_lam());
                self.0 = Rc::new(AnaLam::App {
                    n: Some(gn),
                    size: *size, is_min: *is_min,
                    func: func.clone(), oprd: oprd.clone()
                });
            },
            _ => (),
        };
        self
    }

    fn to_lam(&self) -> PLamExpr {
        match &*self.0 {
            AnaLam::Comb { comb, .. } => lazy_k_core::nm( comb ),
            AnaLam::App  { func, oprd, .. } => func.to_lam() * oprd.to_lam(),
        }
    }
}

impl PartialEq for PAnaLam {
    fn eq(&self, rhs: &PAnaLam) -> bool {
        *self.0 == *rhs.0
    }
}

impl Eq for PAnaLam {}

impl Clone for PAnaLam {
    fn clone(&self) -> Self {
        PAnaLam(Rc::clone(&self.0))
    }
}

impl Mul for PAnaLam {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        let min = self.is_min() && rhs.is_min()
                && match self.to_lam().extract() {
                    LamExpr::Nm { name } if **name == "I" => false,
                    LamExpr::App { func: f1, oprd: o1, .. } =>
                        match (f1.extract(), o1.extract()) {
                            (LamExpr::Nm { name }, _) if **name == "K" => false,
                            (LamExpr::Nm { name: n1 }, LamExpr::Nm { name: n2})
                                if **n1 == "S" && **n2 == "K" => false,
                            _ => true,
                        }
                    _ => true,
                };
        PAnaLam(Rc::new(AnaLam::App {
            size: 1 + self.len() + rhs.len(),
            is_min: min,
            n: None,
            func: self,
            oprd: rhs,
        }))
    }
}

#[test]
fn test_first_min_size() {
    assert_eq!(PAnaLam::first_min_size(1).to_lam(), read_lazy_k("i").unwrap());
    assert_eq!(PAnaLam::first_min_size(3).to_lam(),
                                            read_lazy_k("`ki").unwrap());
    assert_eq!(PAnaLam::first_min_size(5).to_lam(),
                                            read_lazy_k("`k`ki").unwrap());
    assert_eq!(PAnaLam::first_min_size(7).to_lam(),
                                            read_lazy_k("`k`k`ki").unwrap());
}

#[test]
fn test_next_min() {
    let a = PAnaLam::new_from_lam(&read_lazy_k("i").unwrap());
    let a = a.next_min(); assert_eq!(a.to_lam(), read_lazy_k("k").unwrap());
    let a = a.next_min(); assert_eq!(a.to_lam(), read_lazy_k("s").unwrap());
    let a = a.next_min(); assert_eq!(a.to_lam(), read_lazy_k("`ki").unwrap());
    let a = a.next_min(); assert_eq!(a.to_lam(), read_lazy_k("`kk").unwrap());
    let a = a.next_min(); assert_eq!(a.to_lam(), read_lazy_k("`ks").unwrap());
    let a = a.next_min(); assert_eq!(a.to_lam(), read_lazy_k("`si").unwrap());
    let a = a.next_min(); assert_eq!(a.to_lam(), read_lazy_k("`sk").unwrap());
    let a = a.next_min(); assert_eq!(a.to_lam(), read_lazy_k("`ss").unwrap());
    let a = a.next_min(); assert_eq!(a.to_lam(), read_lazy_k("`k`ki").unwrap());
    let a = a.next_min(); assert_eq!(a.to_lam(), read_lazy_k("`k`kk").unwrap());
    let a = a.next_min(); assert_eq!(a.to_lam(), read_lazy_k("`k`ks").unwrap());
    let a = a.next_min(); assert_eq!(a.to_lam(), read_lazy_k("`k`si").unwrap());
    let a = a.next_min(); assert_eq!(a.to_lam(), read_lazy_k("`k`sk").unwrap());
    let a = a.next_min(); assert_eq!(a.to_lam(), read_lazy_k("`k`ss").unwrap());
    let a = a.next_min(); assert_eq!(a.to_lam(), read_lazy_k("`s`ki").unwrap());
}
