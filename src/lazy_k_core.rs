use std::fmt;
use std::ops::Mul;
use std::rc::Rc;

pub enum LamExpr {
    V  {
        idx: u32,       // De Bruijn index. 1, 2, 3, ... 0 isn't used.
    },
    L {                         // Lambda expression
        size: u32,
        lexp: PLamExpr,
    },
    App {                       // Application
        size: u32,
        func: PLamExpr,
        oprd: PLamExpr,
    },
    Nm {                        // for Combinator notation
        name: Rc<String>,
    },
    Jot {                       // Jot
        size: u32,
        jot: Rc<String>,
    },
}

pub struct PLamExpr(Rc<LamExpr>);

pub fn v(i: u32) -> PLamExpr {
    assert!( i != 0, "De Bruijn index should take positive number." );
    PLamExpr(Rc::new(LamExpr::V { idx: i }))
}

pub fn la(e: PLamExpr) -> PLamExpr {
    PLamExpr(Rc::new(LamExpr::L {
                    size: 1 + e.len(),
                    lexp: PLamExpr::clone(&e),
                }))
}

// n: "I", "K", or "S" for Combinator and Unlamda style,
//     or "iota" for Iota Style.
pub fn nm(n: &str) -> PLamExpr {
    PLamExpr(Rc::new(LamExpr::Nm { name: Rc::new(n.to_string()) }))
}
pub fn i() -> PLamExpr { nm("I") }
pub fn k() -> PLamExpr { nm("K") }
pub fn s() -> PLamExpr { nm("S") }
pub fn iota() -> PLamExpr { nm("iota") }

impl PLamExpr {

    // The cost of Cloning of PLamExpr is very low.
    // So we should take "PLamExpr::clone(&x)" style insted of "x.clone()".
    pub fn clone(a: &PLamExpr) -> PLamExpr {
        PLamExpr(Rc::clone(&a.0))
    }

    fn len(&self) -> u32 {
        match *self.0 {
            LamExpr::L { size, .. } => size,
            LamExpr::App { size, .. } => size,
            LamExpr::Jot { size, .. } => size,
            _ => 1,
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
        match &*self.0 {
            LamExpr::Nm { name } if **name == "I" => Ok("i".to_string()),
            LamExpr::Nm { name } if **name == "K" => Ok("k".to_string()),
            LamExpr::Nm { name } if **name == "S" => Ok("s".to_string()),
            LamExpr::App { func, oprd, .. } => {
                match func.to_unlam() {
                    Ok(fc) =>
                        match oprd.to_unlam() {
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
            LamExpr::Nm { name } if **name == "S" => Ok("*i*i*i*ii".to_string()),
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
        match &*org.0 {
            LamExpr::L { lexp, ..} => ap(la, Self::beta_red(lexp)),
            LamExpr::App { func, oprd, .. } =>
                match &*func.0 {
                    LamExpr::L { lexp, ..  } =>
                        Some(comple(|x| { x.subst(1, oprd)}, lexp)),
                    _ => Self::lor(|x| Self::beta_red(x), func, oprd),
                },
            _ => None,
        }
    }

    fn subst(&self, thr: u32, e: &PLamExpr) -> Option<PLamExpr> {
        match &*self.0 {
            LamExpr::V { idx } if *idx == thr => Some(Self::clone(e)),
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

    /// ```
    /// use crate::lazy_k::lazy_k_core::{PLamExpr, i, k, s};
    ///
    /// assert_eq!( PLamExpr::beta_red_cc( &(i() * i()) ), Some(i()) );
    ///
    /// assert_eq!( PLamExpr::beta_red_cc( &(s() * k() * k() * s()) ),
    ///                 Some( k() * s() * (k() * s()) ) );
    ///
    /// assert_eq!( PLamExpr::beta_red_cc(&( k() * s() * (k() * s()) )),
    ///                 Some(s()) );
    /// ```
    pub fn beta_red_cc(org: &Self) -> Option<PLamExpr> {
        match &*org.0 {
            LamExpr::App { func: f1, oprd: o1, .. } =>
                match &*f1.0 {
                    LamExpr::Nm { name } if **name == "I" =>
                        Some(Self::clone(o1)),
                    LamExpr::App { func: f2, oprd: o2, .. } =>
                        match &*f2.0 {
                            LamExpr::Nm { name } if **name == "K" =>
                                Some(Self::clone(o2)),
                            LamExpr::App { func: f3, oprd: o3, .. } =>
                                match &*f3.0 {
                                    LamExpr::Nm { name } if **name == "S" =>
                                        Some((Self::clone(o3) * Self::clone(o1))
                                           * (Self::clone(o2) * Self::clone(o1))
                                        ),
                                    _ => Self::lor(|x| Self::beta_red_cc(x),
                                                                        f1, o1),
                                },
                            _ => Self::lor(|x| Self::beta_red_cc(x), f1, o1),
                        },
                    _ => Self::lor(|x| Self::beta_red_cc(x), f1, o1),
                },
            LamExpr::Nm {..} => None,
            _ => None,
        }
    }

    // leftmost-outermost reduction
    fn lor<F>(red: F, func: &Self, oprd: &Self) -> Option<Self>
            where F: Fn(&Self) -> Option<Self> {
        match red(func) {
            Some(f_r) => Some(f_r * Self::clone(oprd)),
            None => ap(|x| { Self::clone(func) * Self::clone(&x) }, red(oprd)),
        }
    }

    // Abstruction Elimination
    /// ```
    /// use crate::lazy_k::lazy_k_core::{PLamExpr, la, v, i, k, s};
    /// fn test_sm(a: PLamExpr, b: PLamExpr) {
    ///     assert_eq!( PLamExpr::abst_elim( &a ), Some( b ) );
    /// }
    ///
    /// let quiz = la( la( v(1) * v(2) ) );
    /// if let Some(a) = PLamExpr::abst_elim( &quiz ) {
    ///     //assert_eq!( a.to_string(), "if-clause".to_string());
    /// } else {
    ///     //assert_eq!( quiz.to_string(), "else-clause".to_string());
    /// }
    /// assert_eq!( PLamExpr::abst_elim(&i()), None );
    /// assert_eq!( PLamExpr::abst_elim(&v(2)), None );
    /// test_sm( v(1)*v(2), v(1)*v(2) );
    /// test_sm( la(v(1)) , i() );
    /// test_sm( la(v(2)) , k()*v(1) );
    /// test_sm( la(v(1)*v(1)) , s()*i()*i() );
    /// test_sm( la( la( v(1) * v(2) ) ),
    ///                         (s()*(k()*(s()*i())))*(s()*(k()*k())*i()) );
    /// ```
    pub fn abst_elim(org: &Self) -> Option<PLamExpr> {
        match &*org.0 {
            LamExpr::Nm  {..} => None,   // Rule 1
            LamExpr::V   {..} => None,   // Rule 1
            LamExpr::Jot {..} => None,   // Rule 1
            LamExpr::App { func, oprd, ..} =>
                Self::merge_app(|x| Self::abst_elim(&x), func, oprd), // Rule 2

            // Rule 3. T[\x.E] => K T[E] if x is NOT free in E
            LamExpr::L { lexp, .. } if ! lexp.has_var(1) => {
                            let lexp = comple(|x| Self::abst_elim(&x), &lexp);
                            let lexp = comple(|x| x.shallow(1), &lexp);
                            Some(k() * lexp)
                        },
            LamExpr::L { lexp, .. } => match &*lexp.0 {

                // variation of Rule 3
                LamExpr::Nm {..} => Some(k() * Self::clone(lexp)),
                LamExpr::Jot {..} => Some(k() * Self::clone(lexp)),

                // Rule 4
                LamExpr::V { idx } if *idx == 1 => Some(i()),
                LamExpr::V {..}                 => panic!("out of rule 4"),

                // Rule 5
                LamExpr::L { lexp: inn, .. } if inn.has_var(2) => {
                            let lexp = comple(|x| Self::abst_elim(&x), &lexp);
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

    fn merge_app<F>(f: F, x: &PLamExpr, y: &PLamExpr) -> Option<PLamExpr>
                where F: Fn(PLamExpr) -> Option<PLamExpr> {
        let xs = Self::clone(x);
        let ys = Self::clone(y);
        match f(xs) {
            Some(xx) => match f(ys) {
                Some(yy) => Some(xx * yy),
                None    => Some(xx * Self::clone(y)),
            },
            None => match f(ys) {
                Some(yy) => Some(Self::clone(x) * yy),
                None    => Some(Self::clone(x) * Self::clone(y)),
            },
        }
    }
}

fn comple<F>(f: F, a: &PLamExpr) -> PLamExpr
        where F: Fn(&PLamExpr) -> Option<PLamExpr> {
    match f(a) {
        Some(x) => x,
        None    => PLamExpr::clone(a),
    }
}

fn ap<F, T>(f: F, x: Option<T>) -> Option<T>
        where F: Fn(T) -> T {
    match x {
        Some(x) => Some(f(x)),
        None => None,
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
    fn to_string(&self) -> String {
        match &*self.0 {
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
            _ => "".to_string(),
        }
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

#[test]
fn test_subst() {
    assert_eq!( v(1).subst( 2, &v(4)), None);
    assert_eq!( v(2).subst( 2, &v(4)), Some(v(4)));
    assert_eq!( v(3).subst( 2, &v(4)), Some(v(2)));
    assert_eq!( la( v(1) * v(2) ).subst(1, &v(3)), Some(la( v(1) * v(4) )) );
    assert_eq!(   ( v(1) * v(2) ).subst(1, &v(3)), Some(    v(3) * v(1) )  );
}

