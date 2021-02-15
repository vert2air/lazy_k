use num_traits::{Zero, One};
use std::collections::BTreeMap;
use std::convert::TryFrom;
use std::fs;

use super::lazy_k_read;
use super::lazy_k_core;
use super::lazy_k_core::{PLamExpr, LamExpr};
use super::goedel_number::{GNBuilder, GN};

pub fn experiment(args: Vec<String>) {
    let prog = fs::read_to_string(&args[2]).unwrap();
    let p = lazy_k_read::read_lazy_k(&prog).unwrap();
    let data = fs::read_to_string(&args[3]).unwrap();
    let d = lazy_k_read::read_lazy_k(&data).unwrap();
    let w = p * d;

    //ana_tree(w.clone());
    println!("start!!");
    gn_beta_red(w.clone());

    println!("next!!");
    match lazy_k_core::apply_fully(50, w, |x| PLamExpr::beta_red_cc(&x), |_| None) {
        Err((r, c, msg)) => {
            //ana_tree(r.clone());
            println!("Tree Done!!");
            println!("Err! ({}): {}, {}", c, msg, r.len());
            match lazy_k_core::apply_fully(50, r,
                                |x| PLamExpr::beta_red_cc(&x), |_| None) {
                Err((r, _, _)) => //ana_tree(r.clone()),
                    println!("next Err!!"),
                _ => ()
            }
        }
        _ => ()
    }
}

fn gn_beta_red(e: PLamExpr) {
    let mut gnb = GNBuilder::new(vec!["I", "K", "S"]
                                .into_iter().map(|x| x.to_string()).collect());
    let gn = gnb.lam_to_gn(&e);
    println!("translated to GN!!");
    let foo = |n: &GN| {
        let mut yet = true;
        gnb.beta_red_cc(&mut yet, n.clone())
    };
    match lazy_k_core::apply_fully(50, gn, foo, |_| None) {
        Ok((r, c)) => {
            println!("GN OK Done");
            let a = gnb.gn_to_lam(r);
            println!("OK! ({}): {}", c, a.len());
        }
        Err((r, c, msg)) => {
            println!("GN NG Done");
            let a = gnb.gn_to_lam(r);
            println!("NG! ({}): {}, {}", c, msg, a.len());
        }
    }
}

fn ana_tree(e: PLamExpr) {
    let mut gnb = GNBuilder::new(vec!["I", "K", "S"]
                                .into_iter().map(|x| x.to_string()).collect());
    let mut map:BTreeMap<GN, u32> = BTreeMap::new();
    ana_subtree(&mut gnb, &mut map, &e);
    for (k, v) in map.iter() {
        if k < &GN::try_from(4_000_000_000u32).unwrap() {
            let le = gnb.gn_to_lam(k.clone());
            println!("gn: {} {} => {}", k, le.to_unlam().unwrap(), v);
        } else {
            println!("gn: {} => {}", k, v);
        }
    }
}

fn ana_subtree(gnb: &mut GNBuilder, map: &mut BTreeMap<GN, u32>, e: &PLamExpr) {
    match &*e.extract() {
        LamExpr::Nm { name } if **name == "I" => inc(map, Zero::zero()),
        LamExpr::Nm { name } if **name == "K" => inc(map, One::one()),
        LamExpr::Nm { name } if **name == "S" =>
                                inc(map, GN::try_from(2).unwrap()),
        LamExpr::App { func, oprd, .. } => {
            let gn = gnb.lam_to_gn(&e);
            inc(map, gn);
            ana_subtree(gnb, map, func);
            ana_subtree(gnb, map, oprd);
        },
        _ => panic!("ana_subtree"),
    }
}

fn inc(map: &mut BTreeMap<GN, u32>, idx: GN) {
    match map.get(&idx) {
        Some(c) => map.insert(idx, c + 1),
        None    => map.insert(idx, 1),
    };
}

