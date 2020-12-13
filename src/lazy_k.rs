use std::ops::Mul;
use std::rc::Rc;

#[derive(Debug)]
enum LamExpr {
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
