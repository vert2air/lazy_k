extern crate num_traits;
use std::convert::TryFrom;

use lazy_k::lazy_k_core;
use lazy_k::lazy_k_goedel_number;
use lazy_k::lazy_k_goedel_number::OurInt;
use lazy_k::lazy_k_mining;

fn main() {
    println!("Hello, world!");
    //let f = OurInt::try_from(1).unwrap();
    let f = OurInt::try_from(2_471_450).unwrap();
    //let to = Some(OurInt::try_from(100).unwrap());
    let to = Some(OurInt::try_from(5_471_450).unwrap());
    lazy_k_mining::mining(f, to);
}
