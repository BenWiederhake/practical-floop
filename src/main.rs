#![feature(int_error_matching)]

#[macro_use]
extern crate lazy_static;

mod token;

use std::collections::{BTreeMap, BTreeSet};
use std::io::{Error, ErrorKind, Result};
use std::iter::{Peekable};
use std::ops::{Deref, Index, IndexMut};
use std::rc::{Rc};
//use std::fs;

use num_bigint::{BigUint};
use num_traits::identities::{Zero};
use num_traits::ops::checked::{CheckedSub};

pub type Natural = BigUint;

pub use token::{natural, ParseId, Token, Tokenizer};

// TODO: Can this be done without lazy_static?
lazy_static! {
    static ref THE_ZERO: Natural = Natural::zero();
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseBlock(Vec<ParseStatement>);

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ParseStatement {
    AddToInto(Natural, ParseId, ParseId),
    SubtractFromInto(Natural, ParseId, ParseId),
    LoopDo(ParseId, ParseBlock),
    DoTimes(Natural, ParseBlock),
    WhileDo(ParseId, ParseBlock),
    // Calc
    // IfThen
    // IfElse
    // ForIn
    // SplitInto
}

struct Parser<I> {
    source: I,
    buf: Option<Token>,
}

impl<I: Iterator<Item = Result<Token>>> Parser<Peekable<I>> {
    fn new(iter: Peekable<I>) -> Parser<Peekable<I>> {
        Parser{ source: iter, buf: None }
    }

    // `Peekable` is *close* to what we need,
    // but we need the `io::Error` itself, and not a reference to it.
    // While I'm at it, transpose the return type:
    fn peek(&mut self) -> Result<Option<&Token>> {
        if self.buf.is_none() {
            self.buf = self.source.next().transpose()?;
        }
        Ok(self.buf.as_ref())
    }

    fn next(&mut self) -> Result<Option<Token>> {
        match self.buf.take() {
            Some(t) => Ok(Some(t)),
            None => self.source.next().transpose(),
        }
    }

    #[must_use]
    fn parse_expected(&mut self, expected: Token) -> Result<()> {
        match self.next()? {
            None => Err(Error::new(ErrorKind::UnexpectedEof,
                format!("Found EOF while expecting '{:?}' token.", expected))),
            Some(actual) if actual == expected => Ok(()),
            Some(actual) => Err(Error::new(ErrorKind::InvalidData,
                format!("Expected token '{:?}', found '{:?}' instead.", expected, actual))),
        }
    }

    fn parse_number(&mut self) -> Result<Natural> {
        match self.next()? {
            None => Err(Error::new(ErrorKind::UnexpectedEof,
                "Found EOF while expecting a number token.")),
            Some(Token::Number(nat)) => Ok(nat),
            Some(actual) => Err(Error::new(ErrorKind::InvalidData,
                format!("Expected number token, found '{:?}' instead.", actual))),
        }
    }

    fn parse_ident(&mut self) -> Result<ParseId> {
        match self.next()? {
            None => Err(Error::new(ErrorKind::UnexpectedEof,
                "Found EOF while expecting an ident token.")),
            Some(Token::Ident(id)) => Ok(id),
            Some(actual) => Err(Error::new(ErrorKind::InvalidData,
                format!("Expected ident token, found '{:?}' instead.", actual))),
        }
    }

    fn parse_statement(&mut self) -> Result<ParseStatement> {
        use ParseStatement::*;
        match self.next()?.expect("only call before EOF") {
            Token::Add => {
                let amount = self.parse_number()?;
                self.parse_expected(Token::To)?;
                let src = self.parse_ident()?;
                self.parse_expected(Token::Into)?;
                let dst = self.parse_ident()?;
                Ok(AddToInto(amount, src, dst))
            },
            Token::Subtract => {
                let amount = self.parse_number()?;
                self.parse_expected(Token::From)?;
                let src = self.parse_ident()?;
                self.parse_expected(Token::Into)?;
                let dst = self.parse_ident()?;
                Ok(SubtractFromInto(amount, src, dst))
            },
            Token::Loop => {
                let var = self.parse_ident()?;
                self.parse_expected(Token::Do)?;
                let block = self.parse_block(false)?;
                self.parse_expected(Token::End)?;
                Ok(LoopDo(var, block))
            },
            Token::Do => {
                let amount = self.parse_number()?;
                self.parse_expected(Token::Times)?;
                let block = self.parse_block(false)?;
                self.parse_expected(Token::End)?;
                Ok(DoTimes(amount, block))
            },
            Token::While => {
                let var = self.parse_ident()?;
                self.parse_expected(Token::Do)?;
                let block = self.parse_block(false)?;
                self.parse_expected(Token::End)?;
                Ok(WhileDo(var, block))
            },
            t => Err(Error::new(ErrorKind::InvalidData,
                format!("Cannot start statement with token '{:?}'.", t))),
        }
    }

    fn parse_block(&mut self, is_outermost: bool) -> Result<ParseBlock> {
        let mut statements = Vec::with_capacity(10);

        loop {
            match self.peek()? {
                None => {
                    if !is_outermost {
                        return Err(Error::new(ErrorKind::UnexpectedEof, "Found EOF while parsing block; missing 'end' token?"));
                    } else {
                        break;
                    }
                },
                Some(&Token::End) =>
                    if is_outermost {
                        return Err(Error::new(ErrorKind::InvalidData, "Unmatched 'end' token"));
                    } else {
                        break
                    }
                ,
                Some(_) => {},
            };
            statements.push(self.parse_statement()?);
        }

        Ok(ParseBlock(statements))
    }
}

pub fn parse<I: Iterator<Item = Result<Token>>>(iter: I) -> Result<ParseBlock> {
    parse_peekable(iter.peekable())
}

pub fn parse_peekable<I: Iterator<Item = Result<Token>>>(iter: Peekable<I>) -> Result<ParseBlock> {
    Parser::new(iter).parse_block(true)
}

#[cfg(test)]
mod test_parser {
    use super::*;

    fn parse_token_vec(vec: Vec<Token>) -> Result<ParseBlock> {
        parse(vec.into_iter().map(|t| Ok(t)))
    }

    #[test]
    fn test_empty() {
        use std::iter::empty;
        assert_eq!(parse(empty()).unwrap(), ParseBlock(vec![]));
    }

    #[test]
    fn test_simple() {
        use Token::*;
        use ParseStatement::*;
        let parse_result = parse_token_vec(vec![
            Add, Number(natural(100)),
            To, Ident(ParseId::FromNumber(1337)),
            Into, Ident(ParseId::FromString("foo".to_string())),
        ]);
        assert_eq!(parse_result.unwrap(), ParseBlock(vec![
            AddToInto(natural(100), ParseId::FromNumber(1337), ParseId::FromString("foo".to_string()))
        ]));
    }

    #[test]
    fn test_dotimes() {
        use Token::*;
        use ParseStatement::*;
        let parse_result = parse_token_vec(vec![
            Do, Number(natural(100)), Times,
            End,
        ]);
        assert_eq!(parse_result.unwrap(), ParseBlock(vec![
            DoTimes(natural(100), ParseBlock(vec![])),
        ]));
    }
}

pub struct Resolver {
    reserved: BTreeSet<VarId>,
    dict: BTreeMap<String, VarId>,
    first_unchecked: u32,
}

impl Resolver {
    pub fn new() -> Resolver {
        /* Note that this marks index 0 as "already reserved" in the eyes of
         * `reserve_any`. This is intentional, as variable 0 will be
         * considered input/output, and *really* should not be interfered with
         * by automatic assignment, even if it's not explicitly used for some
         * reason. */
        Resolver { reserved: BTreeSet::new(), dict: BTreeMap::new(), first_unchecked: 1 }
    }

    fn reserve_if_fixed(&mut self, ident: &ParseId) {
        if let &ParseId::FromNumber(n) = ident {
            self.reserved.insert(VarId(n));
        }
    }

    pub fn reserve_static(&mut self, root_block: &ParseBlock) {
        let mut statements : Vec<&ParseStatement> = root_block.0.iter().collect();

        while let Some(statement) = statements.pop() {
            match statement {
                ParseStatement::AddToInto(_nat, a, b) => {
                    self.reserve_if_fixed(&a);
                    self.reserve_if_fixed(&b);
                },
                ParseStatement::SubtractFromInto(_, a, b) => {
                    self.reserve_if_fixed(&a);
                    self.reserve_if_fixed(&b);
                },
                ParseStatement::LoopDo(a, subblock) => {
                    self.reserve_if_fixed(&a);
                    statements.extend(&subblock.0);
                },
                ParseStatement::DoTimes(_, subblock) => {
                    statements.extend(&subblock.0);
                },
                ParseStatement::WhileDo(a, subblock) => {
                    self.reserve_if_fixed(&a);
                    statements.extend(&subblock.0);
                },
            }
        }
    }

    fn reserve_any(&mut self) -> VarId {
        let chosen = (self.first_unchecked..).filter(|x| !self.reserved.contains(&VarId(*x))).next().unwrap();
        self.first_unchecked = chosen + 1;
        let is_new = self.reserved.insert(VarId(chosen));
        assert!(is_new);
        VarId(chosen)
    }

    fn resolve_ident(&mut self, ident: &ParseId) -> VarId {
        match ident {
            ParseId::FromNumber(var_index) => {
                assert!(self.reserved.contains(&VarId(*var_index)));
                VarId(*var_index)
            },
            ParseId::FromString(var_name) => {
                // TODO: Can `entry()` be used here somehow?
                if let Some(value) = self.dict.get(var_name) {
                    value.clone()
                } else {
                    let value = self.reserve_any();
                    // TODO: Get rid of the string clone?
                    self.dict.insert(var_name.clone(), value);
                    value
                }
            },
        }
    }

    pub fn resolve_remaining(&mut self, parent_block: &ParseBlock) -> PloopBlock {
        let mut resolved_statements = Vec::with_capacity(parent_block.0.len());
        for statement in &parent_block.0 {
            resolved_statements.push(match statement {
                ParseStatement::AddToInto(amount, src, dst) => {
                    PloopStatement::AddToInto(
                        amount.clone(),
                        self.resolve_ident(src),
                        self.resolve_ident(dst))
                },
                ParseStatement::SubtractFromInto(amount, src, dst) => {
                    PloopStatement::SubtractFromInto(
                        amount.clone(),
                        self.resolve_ident(src),
                        self.resolve_ident(dst))
                },
                ParseStatement::LoopDo(var, subblock) => {
                    PloopStatement::LoopDo(
                        self.resolve_ident(var),
                        self.resolve_remaining(subblock))
                },
                ParseStatement::DoTimes(amount, subblock) => {
                    PloopStatement::DoTimes(
                        amount.clone(),
                        self.resolve_remaining(subblock))
                },
                ParseStatement::WhileDo(var, subblock) => {
                    PloopStatement::WhileDo(
                        self.resolve_ident(var),
                        self.resolve_remaining(subblock))
                },
            });
        }

        PloopBlock(Rc::new(resolved_statements))
    }
}

pub fn resolve(block: ParseBlock) -> PloopBlock {
    let mut r = Resolver::new();
    r.reserve_static(&block);
    r.resolve_remaining(&block)
}

#[cfg(test)]
mod test_resolver {
    use super::*;

    #[test]
    fn test_empty() {
        let input = ParseBlock(vec![]);
        let actual = PloopBlock(Rc::new(vec![]));
        let expected = resolve(input);
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_idents_literal() {
        let input = ParseBlock(vec![
            ParseStatement::AddToInto(natural(42), ParseId::FromNumber(1337), ParseId::FromNumber(23)),
        ]);
        let actual = PloopBlock(Rc::new(vec![
            PloopStatement::AddToInto(natural(42), VarId(1337), VarId(23)),
        ]));
        let expected = resolve(input);
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_idents_named() {
        let input = ParseBlock(vec![
            ParseStatement::AddToInto(natural(42), ParseId::FromString("A".into()), ParseId::FromString("B".into())),
            ParseStatement::AddToInto(natural(47), ParseId::FromString("C".into()), ParseId::FromString("A".into())),
        ]);
        let actual = PloopBlock(Rc::new(vec![
            /* Note: `0` is reserved. */
            PloopStatement::AddToInto(natural(42), VarId(1), VarId(2)),
            PloopStatement::AddToInto(natural(47), VarId(3), VarId(1)),
        ]));
        let expected = resolve(input);
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_noninterference() {
        let input = ParseBlock(vec![
            ParseStatement::AddToInto(natural(42), ParseId::FromNumber(2), ParseId::FromString("A".into())),
            ParseStatement::AddToInto(natural(47), ParseId::FromString("B".into()), ParseId::FromNumber(3)),
        ]);
        let actual = PloopBlock(Rc::new(vec![
            /* Note: `0` is reserved. */
            PloopStatement::AddToInto(natural(42), VarId(2), VarId(1)),
            PloopStatement::AddToInto(natural(47), VarId(4), VarId(3)),
        ]));
        let expected = resolve(input);
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_recursion() {
        let input = ParseBlock(vec![
            ParseStatement::LoopDo(ParseId::FromNumber(2), ParseBlock(vec![
                ParseStatement::AddToInto(natural(5), ParseId::FromString("A".into()), ParseId::FromString("C".into())),
                ParseStatement::AddToInto(natural(9), ParseId::FromString("B".into()), ParseId::FromString("A".into())),
            ])),
            ParseStatement::WhileDo(ParseId::FromString("x".into()), ParseBlock(vec![
                ParseStatement::AddToInto(natural(8), ParseId::FromString("A".into()), ParseId::FromNumber(1)),
                ParseStatement::AddToInto(natural(4), ParseId::FromString("E".into()), ParseId::FromString("x".into())),
            ])),
        ]);
        let actual = PloopBlock(Rc::new(vec![
            /* Note: `0` is reserved. */
            PloopStatement::LoopDo(VarId(2), PloopBlock(Rc::new(vec![
                PloopStatement::AddToInto(natural(5), VarId(3), VarId(4)),
                PloopStatement::AddToInto(natural(9), VarId(5), VarId(3)),
            ]))),
            PloopStatement::WhileDo(VarId(6), PloopBlock(Rc::new(vec![
                PloopStatement::AddToInto(natural(8), VarId(3), VarId(1)),
                PloopStatement::AddToInto(natural(4), VarId(7), VarId(6)),
            ]))),
        ]));
        let expected = resolve(input);
        assert_eq!(expected, actual);
    }
}

#[derive(Clone, Copy, Debug, Ord, Eq, PartialOrd, PartialEq)]
pub struct VarId(u32);

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PloopBlock(Rc<Vec<PloopStatement>>);

impl PloopBlock {
    pub fn from_iter<I: Iterator<Item = Result<char>>>(iter: I) -> Result<PloopBlock> {
        let token_iter = Tokenizer::new(iter);
        let parsed_block = parse(token_iter)?;
        Ok(resolve(parsed_block))
    }

    pub fn from<S: Deref<Target=str>>(string: S) -> Result<PloopBlock> {
        PloopBlock::from_iter(string.chars().map(|c| Ok(c)))
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
                // FIXME
                let newval = conf.state[&src].clone() + &amount;
                conf.state[&dst] = newval;
            },
            SubtractFromInto(amount, src, dst) => {
                println!("SubtractFromInto: {:?} {:?} {:?}", amount, src, dst);
                // FIXME
                let newval = conf.state[&src].clone().checked_sub(&amount).unwrap_or(THE_ZERO.clone());
                conf.state[&dst] = newval;
            },
            LoopDo(var, block) => {
                println!("LoopDo: {:?} {:?}", var, block);
                conf.push(DoTimes(conf.state[&var].clone(), block));
            },
            DoTimes(mut amount, block) => {
                println!("DoTimes: {:?} {:?}", amount, block);
                if !amount.is_zero() {
                    amount = amount.checked_sub(&natural(1)).unwrap();
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

// Consider a splay tree, as accesses are going to be repetitive.
#[derive(Clone, Debug)]
pub struct Environment(BTreeMap<VarId, Natural>);

impl Environment {
    fn new(input: Natural) -> Environment {
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
    pub fn new(input: Natural, program: &PloopBlock) -> Configuration {
        let mut cfg = Configuration {
            state: Environment::new(input),
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

    pub fn step(&mut self) -> bool {
        if let Some(statement) = self.stack.pop() {
            statement.apply(self);
        }
        !self.stack.is_empty()
    }

    pub fn run(&mut self) {
        while self.step() {
            println!("Configuration afterwards: {:?}", self);
        }
        println!("Output is: {:?}", self.state[&VarId(0)]);
    }
}

fn main() {
    let sample_prog = PloopBlock::from("
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

    let mut conf = Configuration::new(natural(2), &sample_prog);
    println!("Initial configuration: {:?}", conf);
    conf.run();
    println!("Done");
}
