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

impl LamExpr {
    fn len(&self) -> u32 {
        match self {
            LamExpr::L { size, .. } => *size,
            LamExpr::App { size, .. } => *size,
            LamExpr::Jot { size, .. } => *size,
            _ => 1,
        }
    }

    fn lc(self) -> Self {
        LamExpr::L { size: 1 + self.len(), lexp: Rc::new(self) }
    }

    pub fn beta_red(&self) -> Option<Self> {
        match self {
            LamExpr::L { lexp, ..} => ap(Self::lc, lexp.beta_red()),
            //LamExpr::App { func: LamExpr::L { lexp, ..  }, oprd, .. } =>
            //    Some(comple(|x| x.subst(1, oprd), lexp)),
            //LamExpr::App { func, oprd, .. } =>
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
                ap(Self::lc, lexp.subst(&thr + 1, comple(|x| x.deepen(1), e))),
            LamExpr::App { func, oprd, .. } =>
                Self::merge_app(move |x| { x.subst(thr, e.clone()) },
                                    (&(**func)).clone(), (&(**oprd)).clone()),
            _ => None,
        }
    }

    fn deepen(&self, thr: u32) -> Option<LamExpr> {
        match self {
            LamExpr::V { idx } if idx >= &thr =>
                                    Some(LamExpr::V { idx: idx + 1 }),
            LamExpr::V {..}         => None,
            LamExpr::L { lexp, .. } => ap(Self::lc, lexp.deepen(&thr + 1)),
            LamExpr::App { func, oprd, .. } =>
                Self::merge_app(move |x| { x.deepen(&thr + 1) },
                                    (&(**func)).clone(), (&(**oprd)).clone()),
            _ => None,
            
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

fn ap<T>(f: fn(T) -> T, x: Option<T>) -> Option<T> {
    match x {
        Some(x) => Some(f(x)),
        None => None,
    }
}


impl Mul for LamExpr {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        LamExpr::App {
            size: self.len() + rhs.len(),
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
