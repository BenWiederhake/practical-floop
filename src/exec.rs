use std::collections::{BTreeMap};
use std::convert::{TryFrom};
use std::io::{Error, Result};
use std::ops::{Deref, Index, IndexMut};
use std::rc::{Rc};

use num_traits::identities::{Zero};
use num_traits::ops::checked::{CheckedSub};

use super::{Natural, nat, Tokenizer};
use super::{ParseBlock};
use super::{Resolver};

// TODO: Can this be done without lazy_static?
lazy_static! {
    static ref THE_ZERO: Natural = Natural::zero();
}

#[derive(Clone, Copy, Debug, Ord, Eq, PartialOrd, PartialEq)]
pub struct VarId(pub u32);

// TODO: Is the `Rc` here *actually* a good idea?
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PloopBlock(Rc<Vec<PloopStatement>>);

impl PloopBlock {
    /* Cannot impl TryFrom<> for a trait. */
    pub fn try_from_iter<I: Iterator<Item = Result<char>>>(iter: I) -> Result<PloopBlock> {
        let token_iter = Tokenizer::new(iter);
        let parsed_block = ParseBlock::try_from_iter(token_iter)?;
        Ok(PloopBlock::from(&parsed_block))
    }
}

impl From<&ParseBlock> for PloopBlock {
    fn from(block: &ParseBlock) -> PloopBlock {
        let mut r = Resolver::new();
        r.reserve_static(block);
        r.resolve_remaining(block)
    }
}

impl From<&[PloopStatement]> for PloopBlock {
    fn from(statements: &[PloopStatement]) -> PloopBlock {
        PloopBlock(Rc::new(Vec::from(statements)))
    }
}

impl TryFrom<&str> for PloopBlock {
    type Error = Error;

    fn try_from(string: &str) -> Result<PloopBlock> {
        PloopBlock::try_from_iter(string.chars().map(|c| Ok(c)))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PloopStatement {
    AddToInto(Natural, VarId, VarId),
    SubtractFromInto(Natural, VarId, VarId),
    LoopDo(VarId, PloopBlock),
    DoTimes(Natural, PloopBlock),
    WhileDo(VarId, PloopBlock),
    // calc
    // if
    // for _ in _ do __ end
    // split into
}

impl PloopStatement {
    fn apply(self, conf: &mut Configuration) {
        // TODO: Assertions would need a return value of sorts
        use PloopStatement::*;
        match self {
            AddToInto(amount, src, dst) => {
                println!("AddToInto: {:?} {:?} {:?}", amount, src, dst);
                if src == dst {
                    conf.state[&dst] += amount;
                } else {
                    conf.state[&dst] = conf.state[&src].clone() + amount;
                }
            },
            SubtractFromInto(amount, src, dst) => {
                println!("SubtractFromInto: {:?} {:?} {:?}", amount, src, dst);
                if conf.state[&src] <= amount {
                    conf.state[&dst].set_zero();
                } else if src == dst {
                    conf.state[&dst] -= amount;
                } else {
                    conf.state[&dst] = conf.state[&src].clone() - amount;
                }
            },
            LoopDo(var, block) => {
                println!("LoopDo: {:?} {:?}", var, block);
                conf.push(DoTimes(conf.state[&var].clone(), block));
            },
            DoTimes(mut amount, block) => {
                println!("DoTimes: {:?} {:?}", amount, block);
                if !amount.is_zero() {
                    amount = amount.checked_sub(&nat(1)).unwrap();
                    conf.push(DoTimes(amount, block.clone()));
                    conf.push_all(&block);
                }
            }
            WhileDo(var, block) => {
                println!("WhileDo: {:?} {:?}", var, block);
                if !conf.state[&var].is_zero() {
                    conf.push(WhileDo(var, block.clone()));
                    conf.push_all(&block);
                }
            },
        }
    }
}

// TODO: Consider a splay tree, as accesses are going to be repetitive.
#[derive(Clone, Debug)]
pub struct Environment(BTreeMap<VarId, Natural>);

impl Environment {
    pub fn new(input: Natural) -> Environment {
        let mut map = BTreeMap::new();
        map.insert(VarId(0), input);
        Environment(map)
    }
}

impl Index<&VarId> for Environment {
    type Output = Natural;

    fn index(&self, varid: &VarId) -> &Self::Output {
        self.0.get(varid).unwrap_or(&THE_ZERO)
    }
}

impl IndexMut<&VarId> for Environment {
    fn index_mut(&mut self, varid: &VarId) -> &mut Self::Output {
        self.0.entry(*varid).or_default()
    }
}

#[derive(Clone, Debug)]
pub struct Configuration {
    state: Environment,
    stack: Vec<PloopStatement>,
}

impl Configuration {
    pub fn from_input(input: Natural, program: &PloopBlock) -> Configuration {
        Configuration::from_state(Environment::new(input), program)
    }

    pub fn from_state(initial: Environment, program: &PloopBlock) -> Configuration {
        let mut cfg = Configuration {
            state: initial,
            stack: Vec::with_capacity(program.0.len()),
        };
        cfg.push_all(program);
        cfg
    }

    fn push(&mut self, statement: PloopStatement) {
        self.stack.push(statement);
    }

    fn push_all(&mut self, block: &PloopBlock) {
        let mut statements : Vec<PloopStatement> = (*block.0).clone();
        statements.reverse();
        self.stack.extend_from_slice(&statements);
    }

    pub fn step(&mut self) {
        if let Some(statement) = self.stack.pop() {
            statement.apply(self);
        }
    }

    pub fn is_completed(&self) -> bool {
        self.stack.is_empty()
    }

    pub fn run(&mut self) {
        while !self.is_completed() {
            self.step();
            println!("Configuration afterwards: {:?}", self);
        }
        println!("Output is: {:?}", self.state[&VarId(0)]);
    }
}

impl Deref for Configuration {
    type Target = Environment;

    fn deref(&self) -> &Environment {
        &self.state
    }
}
