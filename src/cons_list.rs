use std::rc::Rc;

pub enum ConsList<T> {
    Cons { head: T, tail: Rc<ConsList<T>> },
    Nil,
}

impl<T: Clone> ConsList<T> {

    pub fn empty() -> Self {
        ConsList::Nil
    }

    pub fn is_empty(&self) -> bool {
        match self {
            ConsList::Nil => true,
            _ => false,
        }
    }

    pub fn head(&self) -> T {
        match &self {
            ConsList::Cons { head, .. } => head.clone(),
            ConsList::Nil => panic!("ConsList::head"),
        }
    }

    pub fn tail(&self) -> ConsList<T> {
        match &self {
            ConsList::Cons { tail, .. } => (**tail).clone(),
            ConsList::Nil => ConsList::Nil,
        }
    }

    pub fn cons(self, head: T) -> Self {
        ConsList::Cons {
            head: head,
            tail: Rc::new(self.clone()),
        }
    }

    pub fn to_vec(self) -> Vec<T> {
        let mut v = vec![];
        let mut p = self;
        while ! p.is_empty() {
            v.push(p.head());
            p = p.tail();
        }
        v
    }

    pub fn iter(&self) -> ConsListIter<T> {
        ConsListIter(self.clone())
    }

}

impl<T: Clone> Clone for ConsList<T> {
    fn clone(&self) -> Self {
        match self {
            ConsList::Cons{ head, tail } =>
                ConsList::Cons{ head: head.clone(), tail: Rc::clone(tail) },
            ConsList::Nil => ConsList::Nil,
        }
    }
}

pub struct ConsListIter<T> (ConsList<T>);

impl<T: Clone> Iterator for ConsListIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.0.is_empty() {
            None
        } else {
            let ret = self.0.head();
            self.0 = self.0.tail();
            Some(ret)
        }
    }
}

#[test]
fn test_ConsList() {
    assert_eq!( ConsList::empty().cons(1).cons(2).cons(3).head(), 3);
    assert_eq!( ConsList::empty().cons(1).cons(2).cons(3).tail().to_vec(),
                vec![2, 1] )
}

/*
impl<T> Mul for ConsList<T> {
    type Output = Self;

    // I don't know, but head is expected to have type of ConsList<T>
    fn mul(self, head: T) -> Self::Output {
        Self::new(RConsList::Cons {
            head: head,
            tail: ConsList(self.0.clone())
        })
    }
}
*/
