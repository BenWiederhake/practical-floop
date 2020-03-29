#![feature(int_error_matching)]

#[macro_use]
extern crate lazy_static;

mod exec;
mod parse;
mod resolve;
mod token;

use std::convert::{TryFrom};
//use std::fs;

use num_bigint::{BigUint};

pub type Natural = BigUint;

pub use token::{nat, ParseIdent, Token, Tokenizer};
pub use parse::{ParseBlock, ParseStatement};
pub use resolve::{Resolver};
pub use exec::{VarId, PloopBlock, PloopStatement, Environment, Configuration};

fn main() {
    let sample_prog = PloopBlock::try_from("
        subtract 0x5 from v0 into v1
        add 0x5 to v1 into v1
        add 0x0 to v2 into v0
        loop v1 do
            add 0x2 to v0 into v0
        end
        # This implements:
        # x1 = min(5, x0)
        # x0 = 2 * x1
    ").unwrap();

    let mut conf = Configuration::from_input(nat(7), &sample_prog);
    println!("Initial configuration: {:?}", conf);
    conf.run();
    println!("Done");
}
