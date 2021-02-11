use std::convert::TryFrom;
use std::fs;

use goedel_number::{GNBuilder, GN};

pub mod lazy_k_core;
pub mod iter;
pub mod lazy_k_read;
pub mod interpreter;
pub mod goedel_number;
pub mod mining;
pub mod cons_list;
pub mod rev_iter;
pub mod traverse_tree;
pub mod experiment;

pub fn gn_to_unlam(gn_str: &str) {
    let mut gnb = GNBuilder::new(vec!["I", "K", "S"]
                                .into_iter().map(|x| x.to_string()).collect());
    println!("{}", gnb.gn_to_lam(str_to_bigint(gn_str)).to_unlam().unwrap());
}

fn str_to_bigint(s: &str) -> GN {
    match GN::parse_bytes(s.as_bytes(), 10) {
        Some(bi) => bi,
        None => panic!("cannot convert to Goedel Number: {}", s),
    }
}

pub fn unlam_to_gn(unlam: &str) {
    let mut gnb = GNBuilder::new(vec!["I", "K", "S"]
                                .into_iter().map(|x| x.to_string()).collect());
    match lazy_k_read::read_lazy_k(unlam) {
        Ok(expr) => {
            let gn = gnb.lam_to_gn(&expr);
            println!("{}", gn)
        }
        Err(msg) => println!("read_lazy_k Error: {}", msg),
    }
}

pub fn interpreter_lazy_k(prog_fn: &str, arg_fn: &str) {
    let prog_str = fs::read_to_string(prog_fn).unwrap();
    let prog = lazy_k_read::read_lazy_k(&prog_str).unwrap();
    let arg_str = fs::read_to_string(arg_fn).unwrap();
    let arg = lazy_k_read::read_lazy_k(&arg_str).unwrap();
    let _ = interpreter::exec_lazy_k(prog * arg);
}

pub fn mining_between(args: Vec<String>) {
    let (from, to) = match args.len() {
        2 => {
            (
                //GN::try_from(1).unwrap()
                GN::try_from(2_471_450).unwrap()
            ,
                //Some(OurInt::try_from(100).unwrap())
                Some(GN::try_from(5_471_450).unwrap())
            )
        }
        3 => ( str_to_bigint(&args[2]), None ),
        4 => ( str_to_bigint(&args[2]), Some( str_to_bigint(&args[3]) ) ),
        _ => return
    };
    mining::mining(from, to);
}

