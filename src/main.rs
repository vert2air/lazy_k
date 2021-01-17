extern crate num_traits;
use std::convert::TryFrom;
use std::env;

use lazy_k::lazy_k_core;
use lazy_k::lazy_k_goedel_number;
use lazy_k::lazy_k_goedel_number::OurInt;
use lazy_k::lazy_k_mining;


fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() <= 1 {
        match &args[1] {
            x if x == "gn_to_unlam" && args.len() == 3 =>
                lazy_k::gn_to_unlam(&args[2]),
            x if x == "unlam_to_gn" && args.len() == 3 =>
                lazy_k::unlam_to_gn(&args[2]),
            x if x == "minging" =>
                lazy_k::mining_between(args),
            _ => println!("gn_to_unlam, unlam_to_gn, mining"),
        }

    }
}

