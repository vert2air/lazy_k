extern crate num_traits;
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() > 1 {
        match &args[1] {
            x if x == "gn_to_unlam" && args.len() == 3 =>
                lazy_k::gn_to_unlam(&args[2]),
            x if x == "unlam_to_gn" && args.len() == 3 =>
                lazy_k::unlam_to_gn(&args[2]),
            x if x == "lazy_k" && args.len() == 4 =>
                lazy_k::interpreter_lazy_k(&args[2], &args[3]),
            x if x == "mining" =>
                lazy_k::mining_between(args),
            x if x == "experiment" =>
                lazy_k::experiment::experiment(args),
            _ => usage(),
        }
    } else {
        usage();
    }
}

fn usage() {
    println!("Usage:");
    println!("    gn_to_unlam <goedel_number>");
    println!("    unlam_to_gn <Unlambda_style_LazyK_expression>");
    println!("    lazy_k <program> <argument>");
    println!("    mining <starting_goedel_number> [<end_goedel_number>]");
    println!("    experiment <Lazy K expression file name>");
}

