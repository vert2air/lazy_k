use super::lazy_k_core::{LamExpr, PLamExpr, la};
use super::cons_list::ConsList;

/// a: Common for both L and R. Attributes of the Node.
/// r: Right child when down to Left child.
/// l: Left child when down to Right child.
#[derive(Clone)]
pub enum BTPathInfo<A: Clone, T: Clone + Sized> {
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

#[derive(Clone)]
pub enum MapStack<T: Clone + Sized> {
    Pre { root: T },
    GoL { root: T, left: Option<T> },
    Mid { root: T, left: Option<T> },
    GoR { root: T, left: Option<T>, right: Option<T> },
    Post { root: T, left: Option<T>, right: Option<T> },
}

pub trait BinaryTree<A> where A: Clone, Self: Clone {
    fn disassemble(self) -> (A, Option<Self>, Option<Self>);
    fn make_node(self, pi: BTPathInfo<A, Self>) -> Self;

    fn map<F, G, H>(self, pre: F, mid: G, post: H) -> Self
                                    where F: Fn(Self, u8) -> Option<Self>,
                                        G: Fn(Self, u16) -> Option<Self>,
                                        H: Fn(Self, u32) -> Option<Self> {
        let mut stack = ConsList::empty();
        stack = stack.cons(MapStack::Pre { root: self });
        while ! stack.is_empty() {
            let h = stack.head();
            stack = stack.tail();
            match h {
                MapStack::Pre { root } => {
                    let rt = match pre(root.clone(), 0) {
                        Some(root2_some) => {
                            stack = BinaryTree::update_root(stack,
                                                    Some(root2_some.clone()));
                            root2_some
                        }
                        None => root,
                    };
                    let (_a, ol, _or) = rt.clone().disassemble();
                    stack = match ol.clone() {
                        Some(l) =>
                            stack.cons(MapStack::GoL { root: rt, left: ol })
                                .cons(MapStack::Pre { root: l }),
                        None =>
                            stack.cons(MapStack::Mid { root: rt, left: ol }),
                    }
                }
                MapStack::Mid { root, left } => {
                    let rt = match mid(root.clone(), 0) {
                        Some(root2_some) => {
                            stack = BinaryTree::update_root(stack,
                                                    Some(root2_some.clone()));
                            root2_some
                        }
                        None => root,
                    };
                    let (_a, ol, or) = rt.clone().disassemble();
                    stack = match or.clone() {
                        Some(r) =>
                            stack.cons(MapStack::GoR { root: rt, left: ol,
                                                                right: or })
                                .cons(MapStack::Pre { root: r }),
                        None =>
                            stack.cons(MapStack::Post { root: rt, left: ol,
                                                                right: or }),
                    }
                }
                MapStack::Post { root, left, right } => {
                    let rt = match post(root.clone(), 0) {
                        Some(root2_some) => {
                            stack = BinaryTree::update_root(stack,
                                                    Some(root2_some.clone()));
                            root2_some
                        }
                        None => root,
                    };
                    if stack.is_empty() {
                        return rt;
                    } else {
                        let h = stack.head();
                        stack = stack.tail();
                        stack = match h {
                            MapStack::GoL { root, .. } =>
                                stack.cons(MapStack::Mid { root: root,
                                                left: Some(rt) }),
                            MapStack::GoR { root, left, .. } =>
                                stack.cons(MapStack::Post { root: root,
                                                left: left, right: Some(rt) }),
                            _ => panic!("BinaryTree::map :Neither GoL nor GoR"),
                        }
                    }
                }
                _ => panic!("BinaryTree::map : Unexpected GoL or GoR"),
            }
        }
        panic!("BinaryTree::map : unexpected empty stack")
    }

    /// This is a private function to be designed to use from BinaryTree::map()
    /// only. Don't use this in other case.
    fn update_root(stack: ConsList<MapStack<Self>>, n: Option<Self>) 
                        -> ConsList<MapStack<Self>> {
        if ! stack.is_empty() {
            let h = stack.head();
            let st = stack.tail();
            match h {
                MapStack::GoL { root, left } =>
                    st.cons( MapStack::GoL { root, left: n } ),
                MapStack::GoR { root, left, right } =>
                    st.cons( MapStack::GoR { root, left, right: n } ),
                _ => panic!("BinaryTree::update_root"),
            }
        } else {
            stack
        }
    }

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

#[derive(Clone, Eq, PartialEq)]
pub enum NodeType { App, Lam, Leaf }

impl BinaryTree<NodeType> for PLamExpr {

    fn disassemble(self) -> (NodeType, Option<Self>, Option<Self>) {
        match self.extract() {
            LamExpr::App { func, oprd, .. } =>
                (NodeType::App, Some(func.clone()), Some(oprd.clone())),
            LamExpr::L { lexp, .. } =>
                (NodeType::Lam, Some(lexp.clone()), None),
            _ => (NodeType::Leaf, None, None),
        }
    }
    fn make_node(self, pi: BTPathInfo<NodeType, Self>) -> Self {
        match pi {
            BTPathInfo::L { a: nt, r: oprd, .. } => match nt {
                NodeType::App => self.clone() * oprd.unwrap(),
                NodeType::Lam => la(self),
                _ => panic!("NodeType::make_node"),
            }
            BTPathInfo::R { a: _, l: func, .. } => func.unwrap() * self.clone(),
        }
    }

}


/*
fn map()
    for all

fn find_first()
        where P(): -> bool
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
