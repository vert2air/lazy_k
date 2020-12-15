use std::ops::Mul;
use std::rc::Rc;

#[derive(Debug)]
pub enum LamExpr {
    V  {
        idx: u32,       // De Bruijn index
    },
    L {                         // Lambda expression
        size: u32,
        lexp: Rc<LamExpr>,
    },
    App {                       // Application
        size: u32,
        func: Rc<LamExpr>,
        oprd: Rc<LamExpr>,
    },
    Nm {                        // for Combinator notation
        name: Rc<String>,
    },
    Jot {                       // Jot
        size: u32,
        jot: Rc<String>,
    },
}

pub fn v(i: u32) -> LamExpr {
    LamExpr::V { idx: i }
}

pub fn la(e: LamExpr) -> LamExpr {
    LamExpr::L { size: 1 + e.len(), lexp: Rc::new(e) }
}

impl LamExpr {
    fn len(&self) -> u32 {
        match self {
            LamExpr::L { size, .. } => *size,
            LamExpr::App { size, .. } => *size,
            LamExpr::Jot { size, .. } => *size,
            _ => 1,
        }
    }

    pub fn to_cc(&self) -> Result<String, String> {
        match self {
            LamExpr::Nm { name } if **name == "I" => Ok("I".to_string()),
            LamExpr::Nm { name } if **name == "K" => Ok("K".to_string()),
            LamExpr::Nm { name } if **name == "S" => Ok("S".to_string()),
            LamExpr::App { func, oprd, .. } => {
                match (**func).to_cc() {
                    Ok(fc) =>
                        match (**oprd).to_cc() {
                            Ok(op) =>
                                match **oprd {
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

    pub fn to_unlam(&self) -> Result<String, String> {
        match self {
            LamExpr::Nm { name } if **name == "I" => Ok("i".to_string()),
            LamExpr::Nm { name } if **name == "K" => Ok("k".to_string()),
            LamExpr::Nm { name } if **name == "S" => Ok("s".to_string()),
            LamExpr::App { func, oprd, .. } => {
                match (**func).to_unlam() {
                    Ok(fc) =>
                        match (**oprd).to_unlam() {
                            Ok(op) => Ok(format!("`{}{}", fc, op)),
                            Err(e) => Err(e),
                        },
                    Err(e) => Err(e),
                }
            },
            LamExpr::Nm { name } =>
                Err(format!("to_unlam: Unknown Combinator Name: {}", name)),
            _ => Err(format!("to_unlam: Non-SKI LamExpr: {:?}", self))
        }
    }

    pub fn to_iota(&self) -> Result<String, String> {
        match self {
            LamExpr::Nm { name } if **name == "I" => Ok("*ii".to_string()),
            LamExpr::Nm { name } if **name == "K" => Ok("*i*i*ii".to_string()),
            LamExpr::Nm { name } if **name == "S" => Ok("*i*i*i*ii".to_string()),
            LamExpr::App { func, oprd, .. } => {
                match (**func).to_iota() {
                    Ok(fc) =>
                        match (**oprd).to_iota() {
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

    pub fn to_jot(&self) -> Result<String, String> {
        match self {
            LamExpr::Nm { name } if **name == "I" => Ok("11111111100000".to_string()),
            LamExpr::Nm { name } if **name == "K" => Ok("11100".to_string()),
            LamExpr::Nm { name } if **name == "S" => Ok("11111000".to_string()),
            LamExpr::App { func, oprd, .. } => {
                match (**func).to_jot() {
                    Ok(fc) =>
                        match (**oprd).to_jot() {
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
    /// use crate::lazy_k::lazy_k_core::{v,la};
    ///
    /// // (\xy.xy)(\x.x) --Beta-> \y.(\x.x)y
    /// assert_eq!( ( la( la( v(2) * v(1) ) ) * la( v(1) ) ).beta_red(),
    ///             Some( la( la(v(1)) * v(1) ) ) );
    ///
    /// // \y.(\x.x)y --Beta-> \y.y
    /// assert_eq!( la( la(v(1)) * v(1) ).beta_red(), Some(la(v(1))) );
    /// ```
    pub fn beta_red(&self) -> Option<Self> {
        match self {
            LamExpr::L { lexp, ..} => ap(la, lexp.beta_red()),
            LamExpr::App { func, oprd, .. } =>
                match &**func {
                    LamExpr::L { lexp, ..  } =>
                        Some(comple(|x| { x.subst(1, (**oprd).clone()) },
                                    (**lexp).clone())),
                    _ => match func.beta_red() {
                            Some(f2) => Some(f2 * (**oprd).clone()),
                            None => ap(|x| { (**func).clone() * x},
                                        oprd.beta_red()),
                        }
                },
            _ => None,
        }
    }

    fn subst(&self, thr: u32, e: LamExpr) -> Option<LamExpr> {
        match self {
            LamExpr::V { idx } if idx == &thr => Some(e),
            LamExpr::V { idx } if idx > &thr =>
                                            Some(LamExpr::V { idx: idx - 1}),
            LamExpr::V {..}              => None,
            LamExpr::L { lexp, .. } =>
                ap(la, lexp.subst(&thr + 1, comple(|x| x.deepen(1), e))),
            LamExpr::App { func, oprd, .. } =>
                Self::merge_app(move |x| { x.subst(thr, e.clone()) },
                                    (&**func).clone(), (&**oprd).clone()),
            _ => None,
        }
    }

    fn deepen(&self, thr: u32) -> Option<LamExpr> {
        match self {
            LamExpr::V { idx } if idx >= &thr =>
                                    Some(LamExpr::V { idx: idx + 1 }),
            LamExpr::V {..}         => None,
            LamExpr::L { lexp, .. } => ap(la, lexp.deepen(&thr + 1)),
            LamExpr::App { func, oprd, .. } =>
                Self::merge_app(move |x| { x.deepen(&thr + 1) },
                                    (&(**func)).clone(), (&(**oprd)).clone()),
            _ => None,
            
        }
    }

    /// ```
    /// use std::rc::Rc;
    /// use crate::lazy_k::lazy_k_core::LamExpr::Nm;
    /// let i = Nm { name: Rc::new("I".to_string()) };
    /// let k = Nm { name: Rc::new("K".to_string()) };
    /// let s = Nm { name: Rc::new("S".to_string()) };
    ///
    /// assert_eq!( ( i.clone() * i.clone() ).beta_red_cc(), Some(i.clone()) );
    /// ```
    pub fn beta_red_cc(&self) -> Option<Self> {
        match self {
            LamExpr::App { func: f1, oprd: o1, .. } =>
                match &**f1 {
                    LamExpr::Nm { name } if **name == "I" =>
                        Some((**o1).clone()),
                    LamExpr::App { func: f2, oprd: o2, .. } =>
                        match &**f2 {
                            LamExpr::Nm { name } if **name == "K" =>
                                Some((**o2).clone()),
                            LamExpr::App { func: f3, oprd: o3, .. } =>
                                match &**f3 {
                                    LamExpr::Nm { name } if **name == "S" =>
                                        Some(((**o3).clone() * (**o1).clone())
                                            * ((**o2).clone() * (**o1).clone())),
                                    _ => LamExpr::mlr(f1, o1),
                                },
                            _ => LamExpr::mlr(f1, o1),
                        },
                    _ => LamExpr::mlr(f1, o1),
                },
            LamExpr::Nm {..} => None,
            _ => None,
        }
    }

    fn mlr(f: &LamExpr, o: &LamExpr) -> Option<LamExpr> {
        match f.beta_red_cc() {
            Some(f_r) => Some(f_r * o.clone()),
            None => {
                match o.beta_red_cc() {
                    Some(o_r) => Some(f.clone() * o_r),
                    None => None,
                }
            }
        }
    }

    fn merge_app<F>(f: F, x: LamExpr, y: LamExpr) -> Option<LamExpr>
                where F: Fn(LamExpr) -> Option<LamExpr> {
        let xs = x.clone();
        let ys = y.clone();
        match f(xs) {
            Some(xx) => match f(ys) {
                Some(yy) => Some(xx * yy),
                None    => Some(xx * y.clone()),
            },
            None => match f(ys) {
                Some(yy) => Some(x.clone() * yy),
                None    => Some(x.clone() * y.clone()),
            },
        }
    }
}

fn comple<F, T>(f: F, a: T) -> T
        where F: Fn(T) -> Option<T>,
              T: Clone {
    match f(a.clone()) {
        Some(x) => x,
        None    => a,
    }
}

fn ap<F, T>(f: F, x: Option<T>) -> Option<T>
        where F: Fn(T) -> T {
    match x {
        Some(x) => Some(f(x)),
        None => None,
    }
}

impl PartialEq for LamExpr {
    fn eq(&self, rhs:&LamExpr) -> bool {
        if self.len() != rhs.len() {
            return false;
        }
        match (self, rhs) {
            (LamExpr::V { idx: mv }, LamExpr::V { idx: ov }) =>
                                                mv == ov,
            (LamExpr::L { lexp: me, .. }, LamExpr::L { lexp: oe, .. }) =>
                                                me == oe,
            (LamExpr::App { func: mf, oprd: mo, .. },
             LamExpr::App { func: of, oprd: oo, .. }) =>
                                                (*mf == *of) && (*mo == *oo),
            (LamExpr::Nm { name: mn }, LamExpr::Nm { name: on }) =>
                                                mn == on,
            (LamExpr::Jot { jot: mj, .. }, LamExpr::Jot { jot: oj, .. }) =>
                                                mj == oj,
            _ => false,
        }
    }
}

impl Mul for LamExpr {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        LamExpr::App {
            size: 1 + self.len() + rhs.len(),
            func: Rc::new(self),
            oprd: Rc::new(rhs),
        }
    }
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
            LamExpr::Nm { name } => LamExpr::Nm { name: name.clone() },
            LamExpr::Jot { size, jot } =>
                LamExpr::Jot { size: *size, jot: jot.clone() },
        }
    }
}

impl ToString for LamExpr {
    fn to_string(&self) -> String {
        match self {
            LamExpr::V { idx } => format!(" {}", idx),
            LamExpr::L { lexp, .. } =>
                    format!("\\ {}", (*lexp.clone()).to_string()),
            LamExpr::App { func, oprd, .. } => {
                    let func = match *func.clone() {
                        LamExpr::L {..} => format!("({})", func.to_string()),
                        _ => func.to_string(),
                    };
                    let oprd = match *oprd.clone() {
                        LamExpr::V {..} => oprd.to_string(),
                        LamExpr::Nm {..} => oprd.to_string(),
                        _ => format!("({})", oprd.to_string()),
                    };
                    format!("{}{}", func, oprd)
                },
            _ => "".to_string(),
        }
    }
}

#[test]
fn test_subst() {
    assert_eq!( v(1).subst( 2, v(4)), None);
    assert_eq!( v(2).subst( 2, v(4)), Some(v(4)));
    assert_eq!( v(3).subst( 2, v(4)), Some(v(2)));
    assert_eq!( la( v(1) * v(2) ).subst(1, v(3)), Some(la( v(1) * v(4) )) );
    assert_eq!(   ( v(1) * v(2) ).subst(1, v(3)), Some(    v(3) * v(1) )  );
}

