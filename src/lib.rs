use num_bigint::BigInt;
use std::convert::TryFrom;

use lazy_k_goedel_number::{OurInt, n_to_unlam};

pub mod lazy_k_core;
pub mod lazy_k_read;
pub mod lazy_k_interpreter;
pub mod lazy_k_goedel_number;
pub mod lazy_k_mining;

pub fn gn_to_unlam(gn_str: &str) {
    println!("{}", n_to_unlam(str_to_bigint(gn_str)).to_unlam().unwrap());
}

fn str_to_bigint(s: &str) -> BigInt {
    match BigInt::parse_bytes(s.as_bytes(), 10) {
        Some(bi) => bi,
        None => panic!("cannot convert to BigInt: {}", s),
    }
}

pub fn unlam_to_gn(unlam: &str) {
    match lazy_k_read::read_lazy_k(unlam) {
        Ok(expr) => {
            let (_, gn) = lazy_k_goedel_number::lam_to_n(&expr);
            println!("{}", gn)
        }
        Err(msg) => println!("read_lazy_k Error: {}", msg),
    }
}

pub fn mining_between(args: Vec<String>) {
    if args.len() == 2 {
        //let f = OurInt::try_from(1).unwrap();
        let f = OurInt::try_from(2_471_450).unwrap();
        //let to = Some(OurInt::try_from(100).unwrap());
        let to = Some(OurInt::try_from(5_471_450).unwrap());
        lazy_k_mining::mining(f, to);
    } else if args.len() == 3 {
        let from = str_to_bigint(&args[2]);
        lazy_k_mining::mining(from, None);
    } else if args.len() == 4 {
        let from = str_to_bigint(&args[2]);
        let to   = str_to_bigint(&args[3]);
        lazy_k_mining::mining(from, Some(to));
    } else {
    }
}
