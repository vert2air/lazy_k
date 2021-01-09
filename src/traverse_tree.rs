use super::lazy_k_core::{LamExpr, PLamExpr};
use super::cons_list::ConsList;

/// a: Common for both L and R. Attributes of the Node.
/// r: Right child when down to Left child.
/// l: Left child when down to Right child.
#[derive(Clone)]
pub enum BTPathInfo<A: Clone, T: Clone + ?Sized> {
    L { a: A, r: Option<T> },
    R { a: A, l: Option<T> },
}

#[derive(Clone)]
enum FoldStack<T> {
    Pre(T),
    Mid(T),
    Post(T),
    Child(T),
}

pub trait BinaryTree<A> where A: Clone, Self: Clone {
    fn disassemble(self) -> (A, Option<Self>, Option<Self>);
    fn make_node(self, pi: BTPathInfo<A, Self>) -> Self;

    /// Traverse the binary tree in Preorder,
    /// and search the node at which function f returns Some(_) value.
    /// At the time found such a first node,
    /// replace the node with the value enveloped by Some(),
    /// and returns whole modified tree wrapped Some().
    /// When not found such a node, returns None.
    fn apply_first<F>(self, f: F) -> Option<Self>
                where F: Fn(Self) -> Option<Self>, Self: std::marker::Sized {
        let mut task = ConsList::empty().cons((self, ConsList::empty()));
        while ! task.is_empty() {
            let (tgt, parents): (Self, ConsList<BTPathInfo<A, Self>>)
                                                            = task.head();
            task = task.tail();
            match f(tgt.clone()) {
                Some(a) => {
                    let mut ans = a;
                    for pi in parents.iter() {
                        ans = ans.make_node(pi);
                    }
                    // discards all the value in task
                    for (_o, l) in task.iter() {
                        for _e in l.iter() {
                        }
                    }
                    return Some(ans);
                }
                None => {
                    let (a, lc, rc) = tgt.disassemble();
                    if let Some(rcs) = rc.clone() {
                        task = task.cons( (rcs.clone(), parents.clone().cons(
                                BTPathInfo::R { a: a.clone(), l: lc.clone() })))
                    }
                    // task's head is left to traverse in preorder
                    if let Some(lcs) = lc {
                        task = task.cons( (lcs.clone(), parents.clone().cons(
                                BTPathInfo::L { a: a,         r: rc })))
                    }
                }
            }
        }
        None
    }

    fn fold<R, F, G, H>(self, ini: R, pre: F, mid: G, post: H) -> R
                where F: Fn(R, Self, u8) -> R, G: Fn(R, Self, u16) -> R,
                                                H: Fn(R, Self, u32) -> R {
        let mut sum = ini;
        let mut task = ConsList::empty().cons(FoldStack::Child(self));
        while ! task.is_empty() {
            let tgt = task.head();
            task = task.tail();
            match tgt {
                FoldStack::Pre(n)  => sum = pre(sum, n, 0),
                FoldStack::Mid(n)  => sum = mid(sum, n, 0),
                FoldStack::Post(n) => sum = post(sum, n, 0),
                FoldStack::Child(c) => {
                    let (_, left, right) = c.clone().disassemble();
                    task = task.cons(FoldStack::Post(c.clone()));
                    if let Some(r) = right {
                        task = task.cons(FoldStack::Child(r));
                    }
                    task = task.cons(FoldStack::Mid(c.clone()));
                    if let Some(l) = left {
                        task = task.cons(FoldStack::Child(l));
                    }
                    task = task.cons(FoldStack::Pre(c));
                }
            }
        }
        sum
    }
}

impl BinaryTree<()> for PLamExpr {

    fn disassemble(self) -> ((), Option<Self>, Option<Self>) {
        match self.extract() {
            LamExpr::App { func, oprd, .. } =>
                ((), Some(func.clone()), Some(oprd.clone())),
            _ => ((), None, None),
        }
    }
    fn make_node(self, pi: BTPathInfo<(), Self>) -> Self {
        match pi {
            BTPathInfo::L { r: oprd, .. } => self.clone() * oprd.unwrap(),
            BTPathInfo::R { l: func, .. } => func.unwrap() * self.clone(),
        }
    }

}


/*
fn map()
    for all

fn fold()
    for all

fn find_first()
        where P(): -> bool
    until first Some()

fn apply_first()
    until first Some()

fn all() -> bool
        where P(): -> bool
    // until first false
    match find_first( !P ) {
        None -> true,
        Some(_) -> false,
    }

fn or() -> bool
    // until first true
    match find_first( P ) {
        Some(_) -> true,
        None -> false,
    }
*/
