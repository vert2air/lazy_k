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

impl<T: Clone + Ord + SubAssign + One> Iterator for RevIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let cur = self.next.clone();
        if cur >= self.to {
            self.next -= One::one();
            Some(cur)
        } else {
            None
        }
    }
}

