use std::ops::AddAssign;
use std::ops::SubAssign;
use num_traits::One;

pub struct RevIter<T> {
    next: T,
    to: T,
}

impl<T> RevIter<T> {
    pub fn new(from: T, to: T) -> Self {
        RevIter{ next: from, to: to }
    }
}

impl<T: Clone + Ord + AddAssign + SubAssign + One> Iterator for RevIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let cur = self.next.clone();
        if cur > self.to {
            self.next -= One::one();
            Some(cur)
        } else if cur == self.to {
            if self.next >= One::one() {
                self.next -= One::one();
            } else {
                self.to += One::one();
            }
            Some(cur)
        } else {
            None
        }
    }
}

#[test]
fn test_rev_iter() {
    let mut it = RevIter::new(1u32, 0u32);
    assert_eq!( it.next(), Some(1) );
    assert_eq!( it.next(), Some(0) );
    assert_eq!( it.next(), None );
    let mut it = RevIter::new(0, 0);
    assert_eq!( it.next(), Some(0) );
    assert_eq!( it.next(), None );
    let mut it = RevIter::new(-1, 0);
    assert_eq!( it.next(), None );
}

