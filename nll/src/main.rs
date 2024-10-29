#![feature(conservative_impl_trait)]
#![feature(rustc_encodable_decodable)]

#[macro_use]
extern crate lazy_static;

extern crate docopt;
extern crate lalrpop_intern;
extern crate graph_algorithms;
extern crate nll_repr;
extern crate rustc_serialize;

use docopt::Docopt;
use nll_repr::repr::*;
use std::env::args;
use std::error::Error;
use std::fs::File;
use std::io::Read;
use std::process;

#[macro_use]
mod log;
mod borrowck;
mod env;
mod errors;
use self::env::Environment;
mod infer;
mod loans_in_scope;
mod liveness;
mod graph;
mod region;
mod regionck;
use self::graph::FuncGraph;

fn main() {
    let args: Args = Docopt::new(USAGE)
        .and_then(|d| d.argv(args()).decode())
        .unwrap_or_else(|e| e.exit());

    let mut errors = 0;
    for input in &args.arg_inputs {
        match process_input(&args, input) {
            Ok(()) => { }
            Err(err) => {
                println!("{}: {}", input, err);
                errors += 1;
            }
        }
    }
    if errors > 0 {
        process::exit(1);
    }
}

fn process_input(args: &Args, input: &str) -> Result<(), Box<Error>> {
    let mut file_text = String::new();
    let mut file = try!(File::open(input));
    if file.read_to_string(&mut file_text).is_err() {
        return try!(Err(String::from("not UTF-8")));
    }
    let func = try!(Func::parse(&file_text));
    let graph = FuncGraph::new(func);
    graph::with_graph(&graph, || {
        let env = Environment::new(&graph);

        if args.flag_dominators {
            env.dump_dominators();
        }

        println!("Testing `{}`...", input);
        try!(regionck::region_check(&env));
        Ok(())
    })
}

const USAGE: &'static str = "
Usage: nll [options] <inputs>...

Options:
  --help
  --dominators
  --post-dominators
";

#[derive(Debug, RustcDecodable)]
struct Args {
    arg_inputs: Vec<String>,
    flag_dominators: bool,
    flag_post_dominators: bool,
    flag_help: bool,
}
