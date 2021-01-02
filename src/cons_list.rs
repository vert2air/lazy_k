use std::rc::Rc;

enum RConsList<T> {
    Cons { head: T, tail: ConsList<T> },
    Nil,
}

pub struct ConsList<T>(Rc<RConsList<T>>);

impl<T: Clone> ConsList<T> {

    fn new(rcl: RConsList<T>) -> Self {
        ConsList(Rc::new(rcl))
    }

    pub fn empty() -> Self {
        ConsList(Rc::new(RConsList::Nil))
    }

    pub fn is_empty(&self) -> bool {
        match &*self.0 {
            RConsList::Nil => true,
            _ => false,
        }
    }

    pub fn head(&self) -> T {
        match &*self.0 {
            RConsList::Cons { head, .. } => head.clone(),
            RConsList::Nil => panic!("ConsList::head"),
        }
    }

    pub fn tail(&self) -> ConsList<T> {
        match &*self.0 {
            RConsList::Cons { tail, .. } => ConsList(tail.0.clone()),
            RConsList::Nil => ConsList(self.0.clone()),
        }
    }

    pub fn cons(&self, head: T) -> Self {
        Self::new(RConsList::Cons {
            head: head,
            tail: ConsList(self.0.clone())
        })
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

impl<T> Clone for ConsList<T> {
    fn clone(&self) -> Self {
        ConsList( self.0.clone() )
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
