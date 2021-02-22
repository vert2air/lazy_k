use std::fmt;
use std::ops::Mul;
use std::rc::Rc;

use super::rev_iter::RevIter;
use super::traverse_tree::BinaryTree;

#[derive(Eq, PartialEq)]
pub enum LamExpr {
    V  {
        idx: u32,       // De Bruijn index. 1, 2, 3, ... 0 isn't used.
    },
    L {                         // Lambda expression
        size: usize,
        lexp: PLamExpr,
    },
    App {                       // Application
        size: usize,
        func: PLamExpr,
        oprd: PLamExpr,
    },
    Nm {                        // for Combinator notation
        name: Rc<String>,
    },
    Jot {                       // Jot
        size: usize,
        jot: Rc<String>,
    },
}

impl Clone for LamExpr {
    fn clone(&self) -> Self {
        match self {
            LamExpr::V { idx } => LamExpr::V { idx: *idx },
            LamExpr::L { size, lexp } =>
                                LamExpr::L { size: *size, lexp: lexp.clone() },
            LamExpr::App { size, func, oprd } =>
                            LamExpr::App { size: *size, func: func.clone(),
                                                        oprd: oprd.clone() },
            LamExpr::Nm  { name } => LamExpr::Nm { name: name.clone() },
            LamExpr::Jot { size, jot } =>
                                LamExpr::Jot { size: *size, jot: jot.clone() },
        }
    }
}

impl fmt::Debug for LamExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            LamExpr::V { idx } =>
                f.debug_struct("LamExpr::V")
                    .field("idx", &idx)
                    .finish(),
            LamExpr::L { size, lexp } =>
                f.debug_struct("LamExpr::L")
                    .field("size", &size)
                    .field("lexp", &lexp)
                    .finish(),
            LamExpr::App { size, func, oprd } =>
                f.debug_struct("LamExpr::App")
                    .field("size", &size)
                    .field("func", &func)
                    .field("oprd", &oprd)
                    .finish(),
            LamExpr::Nm { name } =>
                f.debug_struct("LamExpr::Nm")
                    .field("name", &name)
                    .finish(),
            LamExpr::Jot { size, jot } =>
                f.debug_struct("LamExpr::Jot")
                    .field("size", &size)
                    .field("jot", &jot)
                    .finish(),
        }
    }
}

impl ToString for LamExpr {
    fn to_string(&self) -> String {
        match self {
            LamExpr::V { idx } => format!(" {}", idx),
            LamExpr::L { lexp, .. } => format!("\\ {}", lexp.to_string()),
            LamExpr::App { func, oprd, .. } => {
                    let func = match *func.0 {
                        LamExpr::L {..} => format!("({})", func.to_string()),
                        _ => func.to_string(),
                    };
                    let oprd = match *oprd.0 {
                        LamExpr::V {..} => oprd.to_string(),
                        LamExpr::Nm {..} => oprd.to_string(),
                        _ => format!("({})", oprd.to_string()),
                    };
                    format!("{}{}", func, oprd)
                },
            LamExpr::Nm { name } if **name == "I" => "I".to_string(),
            LamExpr::Nm { name } if **name == "K" => "K".to_string(),
            LamExpr::Nm { name } if **name == "S" => "S".to_string(),
            LamExpr::Nm { name } if **name == "plus1" => "+".to_string(),
            LamExpr::Nm { name } => format!("<{}>", **name),
            _ => "".to_string(),
        }
    }
}

#[derive(Eq, PartialEq, Debug)]
pub enum LamExprStyle {
    Lambda,
    CC,
    Iota,
    Jot,
}

pub struct PLamExpr(Rc<LamExpr>);

// n: "I", "K", or "S" for Combinator and Unlamda style,
//     or "iota" for Iota Style.
pub fn nm(n: &str) -> PLamExpr {
    PLamExpr(Rc::new(LamExpr::Nm { name: Rc::new(n.to_string()) }))
}
pub fn i()    -> PLamExpr { nm("I") }
pub fn k()    -> PLamExpr { nm("K") }
pub fn s()    -> PLamExpr { nm("S") }
pub fn iota() -> PLamExpr { nm("iota") }
pub fn lam_i()    -> PLamExpr { la( v(1) ) }
pub fn lam_k()    -> PLamExpr { la( la( v(2) ) ) }
pub fn lam_s()    -> PLamExpr { la( la( la( (v(3)*v(1)) * (v(2)*v(1)) ) ) ) }
pub fn lam_iota() -> PLamExpr { la( v(1) * lam_s() * lam_k() ) }

pub fn v(i: u32) -> PLamExpr {
    assert!( i != 0, "De Bruijn index should take positive number." );
    PLamExpr(Rc::new(LamExpr::V { idx: i }))
}

pub fn la(e: PLamExpr) -> PLamExpr {
    PLamExpr(Rc::new(LamExpr::L { size: 1 + e.len(), lexp: (&e).clone(), }))
}

pub fn jot(j: &str) -> PLamExpr {
    match j.to_string().chars()
            .filter(|c| { *c == '0' || *c == '1' }).collect::<String>() {
        e if e.len() > 0 =>
            PLamExpr(Rc::new(LamExpr::Jot { size: e.len(), jot: Rc::new(e) })),
        _ => panic!("Unexpected String for Jot style"),
    }
}

impl PLamExpr {

    pub fn new(a: &LamExpr) -> PLamExpr {
        PLamExpr(Rc::new(a.clone()))
    }

    pub fn extract(&self) -> &LamExpr {
        &*self.0
    }

    pub fn len(&self) -> usize {
        match *self.0 {
            LamExpr::L { size, .. } => size,
            LamExpr::App { size, .. } => size,
            LamExpr::Jot { size, .. } => size,
            _ => 1,
        }
    }

    /// ```
    /// use crate::lazy_k::lazy_k_core::{i, k, s, iota, v, la, jot};
    /// use crate::lazy_k::lazy_k_core::LamExprStyle::{Lambda, CC, Iota, Jot};
    ///
    /// assert_eq!( ( s() * k() * k() * s() ).check_style(),      Some(CC));
    /// assert_eq!( jot("11100").check_style(),                   Some(Jot));
    /// assert_eq!( la( v(1) * la( v(1) * v(2) ) ).check_style(), Some(Lambda));
    /// assert_eq!( ( iota() * (iota() * iota()) ).check_style(), Some(Iota));
    ///
    /// assert_eq!( ( k() * la( v(1) * s() ) ).check_style(),    None);
    /// assert_eq!( (jot("11100") * jot("11100")).check_style(), None);
    /// ```
    pub fn check_style(&self) -> Option<LamExprStyle> {
        match &*self.0 {
            LamExpr::Nm { name }
                if **name == "I" || **name == "K" || **name == "S" =>
                                Some(LamExprStyle::CC),
            LamExpr::Nm { name } if **name == "iota" =>
                                Some(LamExprStyle::Iota),
            LamExpr::Jot {..} => Some(LamExprStyle::Jot),
            LamExpr::V {..}   => Some(LamExprStyle::Lambda),
            LamExpr::L {..}   => Some(LamExprStyle::Lambda),
            LamExpr::App { func, oprd, .. } => {
                let f = func.check_style();
                let o = oprd.check_style();
                if f == o && f != Some(LamExprStyle::Jot) {
                    f
                } else {
                    None
                }
            },
            _ => None,
        }
    }

    /// ```
    /// use crate::lazy_k::lazy_k_core::{PLamExpr, i, k, s};
    /// fn test_eq(a: std::result::Result<String, String>, b: &str) {
    ///     assert_eq!( a, Ok(b.to_string()));
    /// }
    ///
    /// test_eq( ( i()*k()*( s()*i() ) ).to_cc(), "IK(SI)" );
    /// ```
    pub fn to_cc(&self) -> Result<String, String> {
        match &*self.0 {
            LamExpr::Nm { name } if **name == "I" => Ok("I".to_string()),
            LamExpr::Nm { name } if **name == "K" => Ok("K".to_string()),
            LamExpr::Nm { name } if **name == "S" => Ok("S".to_string()),
            LamExpr::App { func, oprd, .. } => {
                match func.to_cc() {
                    Ok(fc) =>
                        match oprd.to_cc() {
                            Ok(op) =>
                                match *oprd.0 {
                                    LamExpr::App {..} =>
                                         Ok(format!("{}({})", fc, op)),
                                    _ => Ok(format!("{}{}",   fc, op)),
                                },
                            Err(e) => Err(e),
                        },
                    Err(e) => Err(e),
                }
            },
            LamExpr::Nm { name } =>
                Err(format!("to_cc: Unknown Combinator Name: {}", name)),
            _ => Err(format!("to_cc: Non-SKI LamExpr: {:?}", self))
        }
    }

    /// ```
    /// use crate::lazy_k::lazy_k_core::{PLamExpr, i, k, s};
    /// fn test_eq(a: std::result::Result<String, String>, b: &str) {
    ///     assert_eq!( a, Ok(b.to_string()));
    /// }
    ///
    /// test_eq( ( i()*k()*( s()*i() ) ).to_unlam(), "``ik`si" );
    /// ```
    pub fn to_unlam(&self) -> Result<String, String> {
        Ok(self.clone().fold("".to_string(),
                    PLamExpr::to_unlam_pre, PLamExpr::id_1, PLamExpr::id_2))
    }
    fn to_unlam_pre(sum: String, n: PLamExpr, _dummy: u8) -> String {
        let sum = match &*n.0 {
            LamExpr::Nm { name } if **name == "I" => format!("{}i", sum),
            LamExpr::Nm { name } if **name == "K" => format!("{}k", sum),
            LamExpr::Nm { name } if **name == "S" => format!("{}s", sum),
            LamExpr::App {..} => format!("{}`", sum),
            x => format!("{}<Unexpected:{:?}>", sum, x),
        };
        sum
    }
    fn id_1(sum: String, _: PLamExpr, _dummy: u16) -> String { sum }
    fn id_2(sum: String, _: PLamExpr, _dummy: u32) -> String { sum }

    /// ```
    /// use crate::lazy_k::lazy_k_core::{PLamExpr, i, k, s};
    /// fn test_eq(a: std::result::Result<String, String>, b: String) {
    ///     assert_eq!( a, Ok(b));
    /// }
    ///
    /// test_eq( ( i()*k()*( s()*i() ) ).to_iota(),
    ///     format!("{}{}{}{}{}{}{}",
    ///             "*", "*", "*ii", "*i*i*ii", "*", "*i*i*i*ii", "*ii") );
    /// ```
    pub fn to_iota(&self) -> Result<String, String> {
        match &*self.0 {
            LamExpr::Nm { name } if **name == "I" => Ok("*ii".to_string()),
            LamExpr::Nm { name } if **name == "K" => Ok("*i*i*ii".to_string()),
            LamExpr::Nm { name } if **name == "S" =>
                                                    Ok("*i*i*i*ii".to_string()),
            LamExpr::App { func, oprd, .. } => {
                match func.to_iota() {
                    Ok(fc) =>
                        match oprd.to_iota() {
                            Ok(op) => Ok(format!("*{}{}", fc, op)),
                            Err(e) => Err(e),
                        },
                    Err(e) => Err(e),
                }
            },
            LamExpr::Nm { name } =>
                Err(format!("to_iota: Unknown Combinator Name: {}", name)),
            _ => Err(format!("to_iota: Non-SKI LamExpr: {:?}", self))
        }
    }

    /// ```
    /// use crate::lazy_k::lazy_k_core::{PLamExpr, i, k, s};
    /// fn test_eq(a: std::result::Result<String, String>, b: String) {
    ///     assert_eq!( a, Ok(b));
    /// }
    ///
    /// test_eq( ( i()*k()*( s()*i() ) ).to_jot(),
    ///     format!("{}{}{}{}{}{}{}",
    ///             "1", "1", "11111111100000", "11100",
    ///                  "1", "11111000", "11111111100000") );
    /// ```
    pub fn to_jot(&self) -> Result<String, String> {
        match &*self.0 {
            LamExpr::Nm { name } if **name == "I" =>
                                            Ok("11111111100000".to_string()),
            LamExpr::Nm { name } if **name == "K" => Ok("11100".to_string()),
            LamExpr::Nm { name } if **name == "S" => Ok("11111000".to_string()),
            LamExpr::App { func, oprd, .. } => {
                match func.to_jot() {
                    Ok(fc) =>
                        match oprd.to_jot() {
                            Ok(op) => Ok(format!("1{}{}", fc, op)),
                            Err(e) => Err(e),
                        },
                    Err(e) => Err(e),
                }
            },
            LamExpr::Nm { name } =>
                Err(format!("to_jot: Unknown Combinator Name: {}", name)),
            _ => Err(format!("to_jot: Non-SKI LamExpr: {:?}", self))
        }
    }


    /// ```
    /// use crate::lazy_k::lazy_k_core::{PLamExpr, iota, k, s };
    /// use crate::lazy_k::lazy_k_core::{lam_iota, lam_k, lam_s};
    ///
    /// assert_eq!( (s() * k() * (iota() * iota())).to_lambda(),
    ///         lam_s() * lam_k() * (lam_iota() * lam_iota()) );
    /// ```
    pub fn to_lambda(&self) -> Self {
        match &*self.0 {
            LamExpr::V { idx }                    => v(*idx),
            LamExpr::Nm { name } if **name == "I" => lam_i(),
            LamExpr::Nm { name } if **name == "K" => lam_k(),
            LamExpr::Nm { name } if **name == "S" => lam_s(),
            LamExpr::Nm { name } if **name == "iota" => lam_iota(),
            LamExpr::Nm {..} => panic!("can't xlate to_lambda: Nm"),
            LamExpr::Jot { jot, .. }        => Self::jot_to_lambda(&**jot),
            LamExpr::L { lexp, .. }         => la( lexp.to_lambda() ),
            LamExpr::App { func, oprd, .. } =>
                                    func.to_lambda() * oprd.to_lambda(),
        }
    }

    fn jot_to_lambda(jot: &str) -> Self {
        jot.chars().fold( lam_i(), |acc, j| {
            match j {
                '0' => acc * lam_s() * lam_k(),
                '1' => la( la( acc * ( v(2) * v(1) ))),
                _ => acc,
            }
        })
    }

    /// ```
    /// use crate::lazy_k::lazy_k_core::{PLamExpr, v, la};
    ///
    /// // (\xy.xy)(\x.x) --Beta-> \y.(\x.x)y
    /// assert_eq!( PLamExpr::beta_red( &(
    ///                 la( la( v(2) * v(1) ) ) * la( v(1) )
    ///             ) ),
    ///             Some( la( la(v(1)) * v(1) ) )
    /// );
    ///
    /// // \y.(\x.x)y --Beta-> \y.y
    /// assert_eq!( PLamExpr::beta_red( & la( la(v(1)) * v(1) ) ),
    ///             Some( la(v(1)) )
    /// );
    /// ```

    pub fn beta_red(org: &Self) -> Option<Self> {
        org.clone().apply_first(|x: Self| -> Option<Self> {
            match &*x.0 {
                LamExpr::App { func, oprd, .. } =>
                    match &*func.0 {
                        LamExpr::L { lexp, ..  } =>
                            Some(comple(|x| { x.subst(1, oprd)}, lexp)),
                        _ => None,
                    },
                _ => None,
            }
        })
    }

    fn subst(&self, thr: u32, e: &PLamExpr) -> Option<PLamExpr> {
        match &*self.0 {
            LamExpr::V { idx } if *idx == thr => Some(e.clone()),
            LamExpr::V { idx } if *idx >  thr => Some(v(idx - 1)),
            LamExpr::V {..}                   => None,
            LamExpr::L { lexp, .. }           =>
                ap(la, lexp.subst(thr + 1, &comple(|x| x.deepen(1), e))),
            LamExpr::App { func, oprd, .. } =>
                Self::merge_app(|x| { x.subst(thr, e) }, func, oprd),
            _ => None,
        }
    }

    fn deepen(&self, thr: u32) -> Option<PLamExpr> {
        match &*self.0 {
            LamExpr::V { idx } if *idx >= thr => Some(v(idx + 1)),
            LamExpr::V {..}                   => None,
            LamExpr::L { lexp, .. }           => ap(la, lexp.deepen(thr + 1)),
            LamExpr::App { func, oprd, .. }   =>
                Self::merge_app(|x| { x.deepen(thr + 1) }, func, oprd),
            _ => None,
        }
    }

    /// Apply beta reduction for Unlambda or Combinator Calculation style
    /// only 1 time.
    /// Check only simple "I", "K" and "S".
    /// ```
    /// use crate::lazy_k::lazy_k_core::{PLamExpr, i, k, s};
    ///
    /// assert_eq!( PLamExpr::beta_red_cc2( &(i() * i()) ), Some(i()) );
    /// assert_eq!( PLamExpr::beta_red_cc2( &(s() * k() * k() * s()) ),
    ///                                 Some( k() * s() * (k() * s()) ) );
    /// assert_eq!( PLamExpr::beta_red_cc2(&( k() * s() * (k() * s()) )),
    ///                                 Some(s()) );
    /// ```
    pub fn beta_red_cc2(org: &Self) -> Option<Self> {
        org.clone().apply_first(|x: Self| -> Option<Self> {
            match &*x.0 {
                LamExpr::App { func: f1, oprd: o1, .. } => match &*f1.0 {
                    LamExpr::Nm { name } if **name == "I" => Some(o1.clone()),
                    LamExpr::App { func: f2, oprd: o2, .. } => match &*f2.0 {
                        LamExpr::Nm { name } if **name == "K" =>
                            Some(o2.clone()),
                        LamExpr::App { func: f3, oprd: o3, .. } => match &*f3.0 {
                            LamExpr::Nm { name } if **name == "S" =>
                                Some( (o3.clone() * o1.clone())
                                    * (o2.clone() * o1.clone()) ),
                            _ => None,
                        },
                        _ => None,
                    },
                    _ => None,
                },
                LamExpr::Nm {..} => None,
                _ => None,
            }
        })
    }

    /// Apply beta reduction for Unlambda or Combinator Calculation style.
    /// Check simple "I", "K" and "S", and "S K x".
    /// Traversal of Expression Tree and beta-Reduction of each node are
    /// separated.
    /// ```
    /// use crate::lazy_k::lazy_k_core::{PLamExpr, i, k, s};
    ///
    /// assert_eq!( PLamExpr::beta_red_cc( &(i() * i()) ), Some(i()) );
    /// assert_eq!( PLamExpr::beta_red_cc( &(s() * k() * k() * s()) ),
    ///                                                     Some(s()) );
    /// assert_eq!( PLamExpr::beta_red_cc(&( k() * s() * (k() * s()) )),
    ///                                                     Some(s()) );
    /// ```
    pub fn beta_red_cc(org: &Self) -> Option<Self> {
        let mut not_do_reduct_s_yet = true;
        let pre = move |a: PLamExpr, _dummy: u8| -> Option<PLamExpr> {
            match &*a.0 {
                LamExpr::App { func: f1, oprd: o1, .. } => match &*f1.0 {
                    LamExpr::Nm { name } if **name == "I" => Some(o1.clone()),
                    LamExpr::App { func: f2, oprd: o2, .. } => match &*f2.0 {
                        LamExpr::Nm { name } if **name == "K" =>
                            // K o2 o1 ==beta=> o2
                            Some(o2.clone()),
                        LamExpr::App { func: f3, oprd: o3, .. } => match &*f3.0 {
                            LamExpr::Nm { name } if **name == "S" => match &*o3.0 {
                                LamExpr::Nm { name } if **name == "K" =>
                                    // S K o2 o1 ==beta=> o1
                                    Some(o1.clone()),
                                _ => {
                                    // S o3 o2 o1
                                    if not_do_reduct_s_yet {
                                        not_do_reduct_s_yet = false;
                                        Some(o3.clone() * o1.clone()
                                                * (o2.clone() * o1.clone()) )
                                    } else {
                                        None
                                    }
                                }
                            }
                            _ => None,
                        }
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            }
        };
        let (new, _) = org.clone().map_preorder(pre);
        new
    }

    /// Apply beta reduction for Unlambda or Combinator Calculation style.
    /// Check simple "I", "K" and "S", and "S K x", and others.
    /// Traversal of Expression Tree is performed by recursive call.
    /// ```
    /// use crate::lazy_k::lazy_k_core::{PLamExpr, i, k, s};
    ///
    /// let mut not_yet = true;
    /// assert_eq!( ( &(i() * i()) ).beta_red_cc3(&mut not_yet), Some(i()) );
    /// let mut not_yet = true;
    /// assert_eq!( ( &(s() * k() * k() * s()) ).beta_red_cc3(&mut not_yet),
    ///                                                     Some(s()) );
    /// let mut not_yet = true;
    /// assert_eq!( (&( k() * s() * (k() * s()) )).beta_red_cc3(&mut not_yet),
    ///                                                     Some(s()) );
    /// ```
    pub fn beta_red_cc3(&self, not_yet: &mut bool) -> Option<Self> {
        match &*self.0 {
            LamExpr::App { func: f1, oprd: o1, .. } => match &*f1.0 {

                // I o1 ==beta=> o1
                LamExpr::Nm { name } if **name == "I" => {
                    let o1n = o1.clone().beta_red_cc3(not_yet);
                    match o1n {
                        None      => Some(o1.clone()),
                        Some(o1s) => Some(o1s),
                    }
                }

                // (K|S) o1 ==beta=> (K|S) o1
                LamExpr::Nm { name } if **name == "K" || **name == "S" => {
                    let o1n = o1.clone().beta_red_cc3(not_yet);
                    match o1n {
                        None      => None,
                        Some(o1s) => Some(f1.clone() * o1s),
                    }
                }

                LamExpr::App { func: f2, oprd: o2, .. } => match &*f2.0 {
                    // I o2 o1 ==beta=> o2 o1
                    LamExpr::Nm { name } if **name == "I" => {
                        let o2n = o2.clone().beta_red_cc3(not_yet);
                        let o1n = o1.clone().beta_red_cc3(not_yet);
                        match (o2n, o1n) {
                            (Some(o2s), Some(o1s)) => Some(o2s * o1s),
                            (Some(o2s), None     ) => Some(o2s * o1.clone()),
                            (None,  Some(o1s)) => Some(o2.clone() * o1s),
                            (None,  None     ) => Some(o2.clone() * o1.clone()),
                        }
                    }

                    // K o2 o1 ==beta=> o2
                    LamExpr::Nm { name } if **name == "K" => {
                        let o2n = o2.clone().beta_red_cc3(not_yet);
                        match o2n {
                            None      => Some(o2.clone()),
                            Some(o2s) => Some(o2s),
                        }
                    }

                    // S K o1 ==beta=> I

                    // S o2 o1 ==beta=> S o2 o1
                    LamExpr::Nm { name } if **name == "S" => {
                        let o2n = o2.clone().beta_red_cc3(not_yet);
                        let o1n = o1.clone().beta_red_cc3(not_yet);
                        match (o2n, o1n) {
                            (Some(o2s), Some(o1s)) =>
                                            Some(f2.clone() * o2s * o1s),
                            (Some(o2s), None) =>
                                            Some(f2.clone() * o2s * o1.clone()),
                            (None, Some(o1s)) =>
                                            Some(f2.clone() * o2.clone() * o1s),
                            (None, None     ) => None,
                        }
                    }

                    LamExpr::App { func: f3, oprd: o3, .. } => match &*f3.0 {

                        // I o3 o2 o1 ==beta=> o3 o2 o1
                        LamExpr::Nm { name } if **name == "I" => {
                            let o32 = o3.clone() * o2.clone();
                            let o32n = o32.clone().beta_red_cc3(not_yet);
                            let o1n = o1.clone().beta_red_cc3(not_yet);
                            match (o32n, o1n) {
                                (Some(o32s), Some(o1s)) => Some(o32s * o1s),
                                (Some(o32s), None ) => Some(o32s * o1.clone()),
                                (None,   Some(o1s)) => Some(o32  * o1s),
                                (None,   None     ) => None,
                            }
                        }

                        // K o3 o2 o1 ==beta=> o3 o1
                        LamExpr::Nm { name } if **name == "K" => {
                            let o3n = o3.clone().beta_red_cc3(not_yet);
                            let o1n = o1.clone().beta_red_cc3(not_yet);
                            match (o3n, o1n) {
                                (Some(o3s), Some(o1s)) => Some(o3s * o1s),
                                (Some(o3s), None    ) => Some(o3s * o1.clone()),
                                (None,     Some(o1s)) => Some(o3.clone() * o1s),
                                (None,      None     ) => None,
                            }
                        }

                        LamExpr::Nm { name } if **name == "S" => match &*o3.0 {

                            // S K o2 o1 ==beta=> o1
                            LamExpr::Nm { name } if **name == "K" => {
                                let o1n = o1.clone().beta_red_cc3(not_yet);
                                match o1n {
                                    None      => Some(o1.clone()),
                                    Some(o1s) => Some(o1s),
                                }
                            }

                            // S o3 o2 o1 ==beta=> o3 o1 (o2 o1)
                            _ => {
                                let s_red = *not_yet;
                                let mut all_none = true;
                                *not_yet = false;
                                let o3c = match o3.clone().beta_red_cc3(
                                                                    not_yet) {
                                    None => o3.clone(),
                                    Some(o3s) => {
                                        all_none = false;
                                        o3s
                                    }
                                };
                                let o2c = match o2.clone().beta_red_cc3(
                                                                    not_yet) {
                                    None => o2.clone(),
                                    Some(o2s) => {
                                        all_none = false;
                                        o2s
                                    }
                                };
                                let o1c = match o1.clone().beta_red_cc3(
                                                                    not_yet) {
                                    None => o1.clone(),
                                    Some(o1s) => {
                                        all_none = false;
                                        o1s
                                    }
                                };
                                if s_red {
                                    Some(o3c * o1c.clone() * (o2c * o1c) )
                                } else {
                                    if all_none {
                                        None
                                    } else {
                                        Some(f3.clone() * o3c * o2c * o1c)
                                    }
                                }
                            }
                        }

                        // f3 o3 o2 o1
                        _ => {
                            let f1n = f1.clone().beta_red_cc3(not_yet);
                            let o1n = o1.clone().beta_red_cc3(not_yet);
                            match (f1n, o1n) {
                                (Some(f1s), Some(o1s)) => Some(f1s * o1s),
                                (Some(f1s), None    ) => Some(f1s * o1.clone()),
                                (None,     Some(o1s)) => Some(f1.clone() * o1s),
                                (None,     None     ) => None,
                            }
                        }
                    }
                    _ => None,  // f2 is Non-CC element.
                },
                _ => None,  // f1 is Non-CC element.
            },
            _ => None,  // org is not App
        }
    }

    // Abstruction Elimination
    /// ```
    /// use crate::lazy_k::lazy_k_core::{PLamExpr, la, v, i, k, s};
    /// fn test_sm(a: PLamExpr, b: PLamExpr) {
    ///     assert_eq!( PLamExpr::abst_elim( &a ), Some( b ) );
    /// }
    ///
    /// assert_eq!( PLamExpr::abst_elim(&i()), None );
    /// assert_eq!( PLamExpr::abst_elim(&v(2)), None );
    /// test_sm( v(1)*v(2), v(1)*v(2) );
    /// test_sm( la(v(1)) , i() );
    /// test_sm( la(v(2)) , k()*v(1) );
    /// test_sm( la(v(1)*v(1)) , s()*i()*i() );
    /// test_sm( la( la( v(1) * v(2) ) ), (s()*(k()*(s()*i())))*k() );
    /// ```
    pub fn abst_elim(org: &Self) -> Option<PLamExpr> {
        match &*org.0 {
            LamExpr::Nm  {..} => None,   // Rule 1
            LamExpr::V   {..} => None,   // Rule 1
            LamExpr::Jot {..} => None,   // Rule 1
            LamExpr::App { func, oprd, ..} =>
                Self::merge_app(|x| Self::abst_elim(x), func, oprd), // Rule 2

            // Rule 3. T[\x.E] => K T[E] if x is NOT free in E
            LamExpr::L { lexp, .. } if ! lexp.has_var(1) => {
                            let lexp = comple(|x| Self::abst_elim(x), lexp);
                            let lexp = comple(|x| x.shallow(1), &lexp);
                            Some(k() * lexp)
                        },
            LamExpr::L { lexp, .. } => match &*lexp.0 {

                // variation of Rule 3
                LamExpr::Nm {..} => Some(k() * lexp.clone()),
                LamExpr::Jot {..} => Some(k() * lexp.clone()),

                // Rule 4
                LamExpr::V { idx } if *idx == 1 => Some(i()),
                LamExpr::V {..}                 => panic!("out of rule 4"),

                // Rule 5
                LamExpr::L { lexp: inn, .. } if inn.has_var(2) => {
                            let lexp = comple(|x| Self::abst_elim(x), lexp);
                            Some( comple(|x| Self::abst_elim(&x), &la(lexp)) )
                        },
                LamExpr::L {..}                => panic!("out of rule 5"),

                LamExpr::App { func, oprd, .. } => match &*oprd.0 {
                    // Eta reduction
                    LamExpr::V { idx } if *idx == 1 && ! func.has_var(1) =>
                            Some( comple(|x| x.shallow(1), &func) ),

                    // Rule 6
                    _ => {
                        let oprd = Self::clone(oprd);
                        let oprd = comple(|x| Self::abst_elim(&x), &la(oprd));
                        let func = Self::clone(func);
                        let func = comple(|x| Self::abst_elim(&x), &la(func));
                        Some( s() * func * oprd )
                    },
                },
            },
        }
    }

    fn has_var(&self, thr: u32) -> bool {
        match &*self.0 {
            LamExpr::V { idx }              => *idx == thr,
            LamExpr::L { lexp, .. }         => lexp.has_var(thr + 1),
            LamExpr::App { func, oprd, .. } =>
                                        func.has_var(thr) || oprd.has_var(thr),
            _ => false,
        }
    }

    fn shallow(&self, thr: u32) -> Option<PLamExpr> {
        match &*self.0 {
            LamExpr::V { idx } if *idx > thr => Some(v(*idx - 1)),
            LamExpr::V {..}                  => None,
            LamExpr::L { lexp, .. }          => ap(la, lexp.shallow(thr + 1)),
            LamExpr::App { func, oprd, .. }  =>
                            Self::merge_app(|x| x.shallow(thr), func, oprd),
            _ => None,
        }
    }

    fn merge_app<'a, F>(f: F, x: &'a PLamExpr, y: &'a PLamExpr)
            -> Option<PLamExpr>
                where F: Fn(&PLamExpr) -> Option<PLamExpr> {
        let xs = Self::clone(x);
        let ys = Self::clone(y);
        match f(&xs) {
            Some(xx) => match f(&ys) {
                Some(yy) => Some(xx * yy),
                None    => Some(xx * Self::clone(y)),
            },
            None => match f(&ys) {
                Some(yy) => Some(Self::clone(x) * yy),
                None    => Some(Self::clone(x) * Self::clone(y)),
            },
        }
    }

    /// ```
    /// use crate::lazy_k::lazy_k_core::{PLamExpr, la, v, s, k, i};
    ///
    /// let chnum = k() * i();
    /// assert_eq!( chnum.get_num(), Some(0) );
    /// let chnum = i();
    /// assert_eq!( chnum.get_num(), Some(1) );
    ///
    /// let chnum = PLamExpr::abst_elim(&la(la( v(1) )));
    /// assert_eq!( chnum.map_or(i(), |x| x).get_num(), Some(0) );
    /// let chnum = PLamExpr::abst_elim(&la(la( (  v(2) * v(1)   ) ) ));
    /// assert_eq!( chnum.map_or(i(), |x| x).get_num(), Some(1) );
    /// let chnum = PLamExpr::abst_elim(&la(la( ( v(2) * ( v(2) * v(1) ) ) ) ));
    /// assert_eq!( chnum.map_or(i(), |x| x).get_num(), Some(2) );
    /// ```
    pub fn get_num(&self) -> Option<u32> {
        let cn = step_n(5_000, ChNumEval::to_ch_num_eval(self.clone()),
                                |x| x.eval_cc());
        match &*cn.0.0 {
            LamExpr::V { idx } => Some(*idx),
            _ => None,
        }
    }

    /// ```
    /// use crate::lazy_k::lazy_k_core::{PLamExpr, la, v, s, k, i};
    ///
    /// let chnum = k() * i();
    /// assert_eq!( chnum.get_num_n(5), Ok((0, 3)) );
    /// let chnum = i();
    /// assert_eq!( chnum.get_num_n(5), Ok((1, 3)) );
    ///
    /// let chnum = PLamExpr::abst_elim(&la(la( v(1) )));
    /// assert_eq!( chnum.map_or(i(), |x| x).get_num_n(5), Ok((0, 3)) );
    /// let chnum = PLamExpr::abst_elim(&la(la( (  v(2) * v(1)   ) ) ));
    /// assert_eq!( chnum.map_or(i(), |x| x).get_num_n(5), Ok((1, 3)) );
    /// let chnum = PLamExpr::abst_elim(&la(la( ( v(2) * ( v(2) * v(1) ) ) ) ));
    /// assert_eq!( chnum.map_or(i(), |x| x).get_num_n(6), Ok((2, 2)) );
    /// let chnum = PLamExpr::abst_elim(&la(la( ( v(2) * ( v(2) * v(1) ) ) ) ));
    /// assert_eq!( chnum.map_or(i(), |x| x).get_num_n(2),
    ///                 Err("Time Limit : c = 0 / 2 : size = 9".to_string()) );
    /// ```
    pub fn get_num_n(&self, lmt: u32) -> Result<(u32, u32), String> {
        match apply_fully(lmt, ChNumEval::to_ch_num_eval(self.clone()),
                                |x| x.eval_cc(), PLamExpr::get_num_n_chk) {
            Ok((chnum, c)) => match &*chnum.0.0 {
                LamExpr::V { idx } => Ok((*idx, c)),
                _ => Err("".to_string()),
            },
            Err((v, c, msg)) =>
                Err(format!("{} : c = {} / {} : size = {}",
                                            msg, c, lmt, v.get_lam().len())),
        }
    }

    fn get_num_n_chk(cn: &ChNumEval) -> Option<String> {
        if cn.clone().get_lam().len() > 10_000_000 {
            Some("Space Limit".to_string())
        } else {
            None
        }
    }
}

fn comple<F, T>(f: F, a: &T) -> T
        where F: Fn(&T) -> Option<T>, T: Clone {
    match f(a) {
        Some(x) => x,
        None    => T::clone(a),
    }
}

fn ap<F, T>(f: F, x: Option<T>) -> Option<T>
        where F: Fn(T) -> T {
    match x {
        Some(x) => Some(f(x)),
        None => None,
    }
}

/// ```
/// use crate::lazy_k::lazy_k_core::step_n;
///
/// fn dec(x: &u32) -> Option<u32> {
///     if(*x > 0) {
///         Some(x - 1)
///     } else {
///         None
///     }
/// }
/// assert_eq!( step_n( 2, 10, dec), 8 );
/// assert_eq!( step_n(12, 10, dec), 0 );
/// ```
pub fn step_n<F, T>(cnt_max: u32, init: T, f: F) -> T
        where F: Fn(&T) -> Option<T> {
    let mut a = init;
    for _ in 0..cnt_max {
        match f(&a) {
            Some(a1) => a = a1,
            None => break,
        }
    }
    a
}

/// ```
/// use crate::lazy_k::lazy_k_core::apply_fully;
///
/// fn dec(x: &u32) -> Option<u32> {
///     if(*x > 1) {
///         Some(x - 1)
///     } else {
///         None
///     }
/// }
/// fn check(x: &u32) -> Option<String> {
///     if *x % 10 == 0 {
///         Some("Error: X0".to_string())
///     } else {
///         None
///     }
/// }
/// assert_eq!( apply_fully( 7, 12, dec, check),
///                                 Err((11, 6, "Error: X0".to_string()) ));
/// assert_eq!( apply_fully( 3, 15, dec, check),
///                                 Err((12, 0, "Time Limit".to_string() ) ));
/// assert_eq!( apply_fully( 9,  8, dec, check), Ok((1, 2) ));
/// ```
pub fn apply_fully<F, G, T>(cnt_max: u32, init: T, mut apply: F, mut check: G)
                        -> Result<(T, u32), (T, u32, String)>
        where F: FnMut(&T) -> Option<T>, G: FnMut(&T) -> Option<String> {
    let mut a = init;
    for c in RevIter::new(cnt_max, 1) {
        match apply( &a ) {
            None     => return Ok((a, c)),
            Some(a1) => match check( &a1 ) {
                None      => a = a1,
                Some(msg) => return Err((a, c, msg)),
            }
        }
    }
    Err((a, 0, "Time Limit".to_string()))
}

impl Clone for PLamExpr {
    fn clone(&self) -> Self {
        PLamExpr(Rc::clone(&self.0))
    }
}

impl PartialEq for PLamExpr {
    fn eq(&self, rhs:&PLamExpr) -> bool {
        if self.len() != rhs.len() {
            return false;
        }
        match (&*self.0, &*rhs.0) {
            (LamExpr::V { idx: mv }, LamExpr::V { idx: ov }) =>
                                                    mv == ov,
            (LamExpr::L { lexp: me, .. }, LamExpr::L { lexp: oe, .. }) =>
                                                    me == oe,
            (LamExpr::App { func: mf, oprd: mo, .. },
             LamExpr::App { func: of, oprd: oo, .. }) =>
                                                    (mf == of) && (mo == oo),
            (LamExpr::Nm { name: mn }, LamExpr::Nm { name: on }) =>
                                                    mn == on,
            (LamExpr::Jot { jot: mj, .. }, LamExpr::Jot { jot: oj, .. }) =>
                                                    mj == oj,
            _ => false,
        }
    }
}

impl Eq for PLamExpr {}

impl Mul for PLamExpr {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        PLamExpr(Rc::new(LamExpr::App {
            size: 1 + self.len() + rhs.len(),
            func: self,
            oprd: rhs,
        }))
    }
}

impl ToString for PLamExpr {

    /// ```
    /// use crate::lazy_k::lazy_k_core::{LamExpr, la, v, ChNumEval, s, k, i};
    ///
    /// assert_eq!(la(v(1)*la(v(1)*v(2))*v(1)).to_string(), "\\  1(\\  1 2) 1");
    /// ```
    fn to_string(&self) -> String {
        (*self.0).to_string()
    }
}

impl fmt::Debug for PLamExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &*self.0 {
            LamExpr::V { idx } =>
                f.debug_struct("PLamExpr<Rc<LamExpr::V>>")
                    .field("idx", &idx)
                    .finish(),
            LamExpr::L { size, lexp } =>
                f.debug_struct("PLamExpr<Rc<LamExpr::L>>")
                    .field("size", &size)
                    .field("lexp", &lexp)
                    .finish(),
            LamExpr::App { size, func, oprd } =>
                f.debug_struct("PLamExpr<Rc<LamExpr::App>>")
                    .field("size", &size)
                    .field("func", &func)
                    .field("oprd", &oprd)
                    .finish(),
            LamExpr::Nm { name } =>
                f.debug_struct("PLamExpr<Rc<LamExpr::Nm>>")
                    .field("name", &name)
                    .finish(),
            LamExpr::Jot { size, jot } =>
                f.debug_struct("PLamExpr<Rc<LamExpr::Jot>>")
                    .field("size", &size)
                    .field("jot", &jot)
                    .finish(),
        }
    }
}

#[derive(Eq, PartialEq, Clone, Debug)]
pub struct ChNumEval(PLamExpr);

impl ChNumEval {

    pub fn new(a: PLamExpr) -> ChNumEval {
        ChNumEval(a)
    }

    pub fn get_lam(self) -> PLamExpr {
        PLamExpr(Rc::new((*self.0.0).clone()))
    }

    pub fn get_lam2(self) -> LamExpr {
        (*PLamExpr(Rc::new((*self.0.0).clone())).0).clone()
    }

    pub fn to_ch_num_eval(e: PLamExpr) -> ChNumEval {
        let v0 = PLamExpr(Rc::new(LamExpr::V { idx: 0 }));
        ChNumEval( e * nm("plus1") * v0 )
    }

    pub fn eval_cc(&self) -> Option<Self> {
        let mut not_do_beta_reduction_yet = true;
        let pre = move |a: PLamExpr, _dummy: u8| -> Option<PLamExpr> {
            match &*a.0 {
                LamExpr::App { func: f1, oprd: o1, .. } => match &*f1.0 {
                    LamExpr::Nm { name } if **name == "I" => Some(o1.clone()),
                    LamExpr::Nm { name } if **name == "plus1" => match &*o1.0 {
                        LamExpr::V { idx } => Some( v(*idx + 1) ),
                        _ => None,
                    }
                    LamExpr::App { func: f2, oprd: o2, .. } => match &*f2.0 {
                        LamExpr::Nm { name } if **name == "K" =>
                            // K o2 o1 ==beta=> o2
                            Some(o2.clone()),
                        LamExpr::App { func: f3, oprd: o3, .. } => match &*f3.0 {
                            LamExpr::Nm { name } if **name == "S" => match &*o3.0 {
                                LamExpr::Nm { name } if **name == "K" =>
                                    // S K o2 o1 ==beta=> o1
                                    Some(o1.clone()),
                                _ => {
                                    // S o3 o2 o1
                                    if not_do_beta_reduction_yet {
                                        not_do_beta_reduction_yet = false;
                                        Some(o3.clone() * o1.clone()
                                                * (o2.clone() * o1.clone()) )
                                    } else {
                                        None
                                    }
                                }
                            }
                            _ => None,
                        }
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            }
        };
        let (new, _) = self.0.clone().map_preorder(pre);
        match new {
            Some(rt) => Some(ChNumEval(rt)),
            None => None,
        }
    }

    pub fn to_unlam(&self) -> Result<String, String> {
        match &*self.0.0 {
            LamExpr::Nm { name } if **name == "I" => Ok("i".to_string()),
            LamExpr::Nm { name } if **name == "K" => Ok("k".to_string()),
            LamExpr::Nm { name } if **name == "S" => Ok("s".to_string()),
            LamExpr::Nm { name } if **name == "plus1" => Ok("(++)".to_string()),
            LamExpr::App { func, oprd, .. } => {
                match Self::new(func.clone()).to_unlam() {
                    Ok(fc) =>
                        match Self::new(oprd.clone()).to_unlam() {
                            Ok(op) => Ok(format!("`{}{}", fc, op)),
                            Err(e) => Err(e),
                        },
                    Err(e) => Err(e),
                }
            },
            LamExpr::V { idx } => Ok(format!("({})", idx)),
            LamExpr::Nm { name } =>
                Err(format!("to_unlam: Unknown Combinator Name: {}", name)),
            _ => Err(format!("to_unlam: Non-SKI LamExpr: {:?}", self))
        }
    }

}


#[test]
fn test_subst() {
    assert_eq!( v(1).subst( 2, &v(4)), None);
    assert_eq!( v(2).subst( 2, &v(4)), Some(v(4)));
    assert_eq!( v(3).subst( 2, &v(4)), Some(v(2)));
    assert_eq!( la( v(1) * v(2) ).subst(1, &v(3)), Some(la( v(1) * v(4) )) );
    assert_eq!(   ( v(1) * v(2) ).subst(1, &v(3)), Some(    v(3) * v(1) )  );
}

#[test]
fn test_eval_cc() {
    use super::lazy_k_read::read_lazy_k;
    let o = ChNumEval::to_ch_num_eval(i());
    let a = o.clone().eval_cc();
    let o = a.clone().map_or(o, |x| x);
    let a = o.clone().eval_cc();
    let o = a.clone().map_or(o, |x| x);
    assert_eq!( o.0, v(1) ); 

    fn test(src: &str, dst: &str) {
        let s = ChNumEval::new(read_lazy_k(src).unwrap());
        let a = match s.eval_cc() {
            Some(r) => r.to_unlam().unwrap(),
            None => "None".to_string(),
        };
        assert_eq!(a, dst);
    }
    test("`ik", "k");
    test("``ksi", "s");
    test("```sskk",   "``sk`kk");
    test("```sski",   "``si`ki");
    test("`i`i```sski", "`i``si`ki");
    test("`i ` ```sski ```sski", "```si`ki```sski"); // 2nd Sxyz isn't xlated.
    test("`i ` ```sski ``ksi", "```si`kis"); // after 1st Sxyz
}

#[test]
fn test_ChNumEval_to_unlam() {
    fn test_eq(a: std::result::Result<String, String>, b: &str) {
        assert_eq!( a, Ok(b.to_string()));
    }
    fn v(n: u32) -> PLamExpr {
        PLamExpr::new(&LamExpr::V{ idx: n })
    }
    fn p1() -> PLamExpr {
       PLamExpr::new(&LamExpr::Nm{ name: Rc::new("plus1".to_string()) })
    }
    test_eq( ChNumEval( i()*k()*( s()*i() ) ).to_unlam(), "``ik`si" );
    test_eq( ChNumEval( i()*v(5)*( p1()*i() ) ).to_unlam(), "``i(5)`(++)i" );
}

