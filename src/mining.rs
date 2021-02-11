use super::lazy_k_core::{PLamExpr, i};
use super::goedel_number::GN;
use super::iter::{PLamExprIter, LEIterType};

pub fn mine_ch_num(a: PLamExpr) -> Result<(u32, u32), String> {
    a.get_num_n(5_000)
}

pub fn mining(f: GN, t: Option<GN>) {
    let it = PLamExprIter::new(LEIterType::Min, f, t);
    let mut pre = i();
    for e in it {
        match mine_ch_num(e.clone()) {
            Ok((num, _c)) => {
                println!("Found {} = {}", num, e.to_unlam().unwrap())
            }
            Err(_msg) => {
                //println!("Error : {}: {}", e.to_unlam().unwrap(), msg)
            }
        }
        pre = e;
    };
}

