use std::ops::Mul;
use std::rc::Rc;

use super::lazy_k_core;
use super::lazy_k_core::{LamExpr, PLamExpr, i, k, s};
use super::lazy_k_goedel_number;
use super::lazy_k_goedel_number::{OurInt, our1};
use super::lazy_k_read::read_lazy_k;

pub fn mine_ch_num(a: PLamExpr) -> Result<(u32, u32), String> {
    a.get_num_n(5_000)
}
/*
fn (f: OurInt, t: Option<OurInt>) {
    let mut a = f;
    PAnaLam::first_min_from(a).set_n()
    if 
}
*/

//struct PLamExprIter<F: Fn(&PLamExpr) -> Option<PLamExpr>> {
struct PLamExprIter {
    next_one: Option<PLamExpr>,
    last_one: Option<PLamExpr>,
    //next: F,
    next: fn(&PLamExpr) -> PLamExpr,
    to_one: Option<PLamExpr>,
}


//impl PLamExpr<F> {
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

    fn first_size(n: usize) -> Self {
        let mut res = i();
        for _ in 1 .. (n + 1)/2 {
            res = i() * res
        }
        res
    }

    fn first_min_size(n: usize) -> Self {
        let mut res = i();
        for _ in 1 .. (n + 1)/2 {
            res = k() * res
        }
        res
    }

    fn next_min(last: &PLamExpr) -> PLamExpr {
        fn otherwise(f1: &PLamExpr, o1: &PLamExpr) -> PLamExpr {
            let f1_n = PLamExpr::next_min(f1);
            let o1_n = PLamExpr::next_min(o1);
            if f1.is_min() && o1_n.len() == o1.len() {
                f1.clone() * o1_n
            } else if f1_n.len() < 1 + f1.len() + o1.len() {
                f1_n.clone()
                    * PLamExpr::first_min_size(f1.len() + o1.len() - f1_n.len())
            } else {
                PLamExpr::first_min_size(f1.len() + o1.len() + 1 + 2)
            }
        }
        match last.extract() {
            LamExpr::App { func: f1, oprd: o1, .. } => {
                let a = match &*f1.extract() {
                    LamExpr::Nm { name } if **name == "I" =>
                        k() * PLamExpr::first_min_size(last.len() - 2),
                    LamExpr::App { func: f2, oprd: o2, .. } =>
                        match (&*f2.extract(), &*o2.extract()) {
                            (LamExpr::Nm { name }, _) if &**name == "K" =>
                                s() * PLamExpr::first_min_size(o2.len())
                                    * PLamExpr::first_min_size(o1.len()),
                            (LamExpr::Nm { name: n2 }, LamExpr::Nm { name: n3 })
                                if &**n2 == "S" && &**n3 == "K" => s() * s()
                                        * PLamExpr::first_min_size(o1.len()),
                            _ => otherwise(f1, o1),
                        },
                    _ => otherwise(f1, o1),
                };
                //a.try_min()
                match a.extract() {
                    LamExpr::Nm {..} => a.clone(),
                    LamExpr::App {..} if a.is_min() => a.clone(),
                    _ => PLamExpr::next_min(&a),
                }
            }
            LamExpr::Nm { name } if **name == "I" => k(),
            LamExpr::Nm { name } if **name == "K" => s(),
            LamExpr::Nm { name } if **name == "S" => k() * i(),
            _ => panic!("next_min"),
        }
    }
    /*
    fn try_min(&self) -> PLamExpr {
        match self.extract() {
            LamExpr::Nm {..} => (*self).clone(),
            LamExpr::App {..} if self.is_min() => self.clone(),
            _ => self.next_min(),
        }
    }
    */
}

//impl PLamExprIter<F: Fn(&PLamExpr) -> Option<PLamExpr>> {
//impl PLamExprIter<F> {
impl PLamExprIter {

    pub fn new(f: OurInt, t: Option<OurInt>) -> Self {
        //PLamExprIter::<F> {
        PLamExprIter {
            next_one: Some(lazy_k_goedel_number::n_to_unlam(f)),
            last_one: None,
            next: PLamExprIter::next_all,
            to_one: match t {
                Some(t) => Some(lazy_k_goedel_number::n_to_unlam(t)),
                None => None,
            },
        }
    }

    pub fn new_min(f: OurInt, t: Option<OurInt>) -> Self {
        let an = lazy_k_goedel_number::n_to_unlam(f);
        let oto = match t {
            Some(t) => Some(lazy_k_goedel_number::n_to_unlam(t)),
            None => None,
        };
        if an.is_min() {
            //PLamExprIter::<F> {
            PLamExprIter {
                next_one: Some(an),
                last_one: None,
                next: PLamExpr::next_min,
                to_one: oto,
            }
        } else {
            //PLamExprIter::<F> {
            PLamExprIter {
                next_one: Some(PLamExpr::next_min(&an)),
                last_one: None,
                next: PLamExpr::next_min,
                to_one: oto,
            }
        }
    }

    pub fn new_min_size(n: usize, t: Option<OurInt>) -> Self {
        let mut res = i();
        for _ in 1 .. (n + 1)/2 {
            res = k() * res
        }
        //PLamExprIter::<F> {
        PLamExprIter {
            next_one: Some(res),
            last_one: None,
            next: PLamExpr::next_min,
            to_one: match t {
                Some(t) => Some(lazy_k_goedel_number::n_to_unlam(t)),
                None => None,
            },
        }
    }

    fn next_all(last: &PLamExpr) -> PLamExpr {
        match last.extract() {
            LamExpr::App { func: f1, oprd: o1, .. } => {
                let f1_n = PLamExprIter::next_all(f1);
                let o1_n = PLamExprIter::next_all(o1);
                if o1_n.len() == o1.len() {
                    f1.clone() * o1_n
                } else if f1_n.len() < 1 + f1.len() + o1.len() {
                    f1_n.clone()
                        * PLamExpr::first_size(f1.len() + o1.len() - f1_n.len())
                } else {
                    PLamExpr::first_size(f1.len() + o1.len() + 1 + 2)
                }
            }
            LamExpr::Nm { name } if **name == "I" => k(),
            LamExpr::Nm { name } if **name == "K" => s(),
            LamExpr::Nm { name } if **name == "S" => i() * i(),
            _ => panic!("next_all"),
        }
    }

}

//impl Iterator for PLamExprIter<F: Fn(&PLamExpr) -> Option<PLamExpr>> {
impl Iterator for PLamExprIter {
    type Item = PLamExpr;

    fn next(&mut self) -> Option<Self::Item> {
        let new_last = match (self.next_one.clone(), self.last_one.clone()) {
            (Some(n), None) if n.is_min() => n,
            (Some(n), None) => PLamExpr::next_min(&n),
            (None, Some(l)) => PLamExpr::next_min(&l),
            (None, None) => return None,
            _ => panic!("PLamExprIter::next"),
        };
        match self.to_one.clone() {
            Some(to) if new_last >= to => {
                self.next_one = None;
                self.last_one = None;
                None
            },
            _ => {
                self.next_one = None;
                self.last_one = Some(new_last.clone());
                Some(new_last)
            },
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
