use lazy_k::lazy_k_core;

fn main() {
    println!("Hello, world!");
    println!("{:?}", lazy_k_core::LamExpr::V { idx: 0 });
}
