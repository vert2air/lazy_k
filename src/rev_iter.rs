
pub struct RevIter {
    next: u32,
    to: u32,
}

impl RevIter {
    pub fn new(from: u32, to: u32) -> Self {
        RevIter{ next: from, to: to }
    }
}

impl Iterator for RevIter {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        let cur = self.next;
        if cur >= self.to {
            self.next -= 1;
            Some(cur)
        } else {
            None
        }
    }
}

