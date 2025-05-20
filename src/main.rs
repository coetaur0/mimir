use std::{env, process};

use mim::compile;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        println!("Not enough arguments: expected the path to a source file.");
        process::exit(1)
    }

    compile(&args[1]);
}
