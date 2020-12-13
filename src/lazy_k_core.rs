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
            LamExpr::L { lexp, ..} => match lexp.beta_red() {
                    Some(br) => Some(br.lc()),
                    None => None,
                }
            //LamExpr::App { func: LamExpr::L { lexpr, ..  }, oprd } =>
            _ => Some(LamExpr::V{ idx: 0 }),    // ToDo
        }
    }

//    fn subst(&self, vIdx: u32, e: LamExpr) -> Option<LamExpr> {
//        match self {
//            LamExpr::V { v } if v == vIdx => Some(e),
//            LamExpr::V { v } if v >  vIdx => Some(LamExpr::V { idx: v - 1}),
//            LamExpr::V { v }              => None,
//            LamExpr::L { lexp, .. } => {
//                    
//                }
//
//        }
//    }

    fn deepen(&self, vIdx: u32) -> Option<LamExpr> {
        match self {
            LamExpr::V { v } if v >= vIdx => Some(LamExpr::V { idx: v + 1 }),
            LamExpr::V { v }              => None,
            LamExpr::L { lexp, .. } => ap(lc, lexp.deepen(vIdx + 1)),
            LamExpr::App { func, oprd, .. } =>
                merge_app(|e| deepen(vIdx + 1, e), func, oprd),
            _ => None,
            
        }
    }

    fn merge_app(f: fn(&LamExpr) -> Option<LamExpr>, x: &LamExpr, y: &LamExpr)
        -> Option<LamExpr> {
        match f(x) {
            Some(xx) => match f(y) {
                Some(yy) => Some(xx * yy),
                None    => Some(xx * y.clone()),
            },
            None => match f(y) {
                Some(yy) => Some(x.clone() * yy),
                None    => Some(x.clone() * y.clone()),
            },
        }
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
                    if let Ok(v) = Rc::try_unwrap(lexp.clone()) {
                        format!("\\ {}", v.to_string())
                    } else {
                        String::from("unexpected")
                    }
            LamExpr::App { func, oprd, .. } => {
                    let func = match Rc::try_unwrap(func.clone()) {
                        Ok(LamExpr::L {..}) =>
                                format!("({})", func.to_string()),
                        _ => func.to_string(),
                    };
                    let oprd = match Rc::try_unwrap(oprd.clone()) {
                        Ok(LamExpr::V {..}) => oprd.to_string(),
                        Ok(LamExpr::Nm {..}) => oprd.to_string(),
                        _ => format!("({})", oprd.to_string()),
                    };
                    format!("{}{}", func, oprd)
                },
            _ => "".to_string(),
        }
    }
}
