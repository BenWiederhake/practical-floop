#![feature(int_error_matching)]

use std::collections::{BTreeMap};
use std::io::{Error, ErrorKind, Result};
use std::num::{ParseIntError, IntErrorKind};
use std::ops::{Add, Sub, Index, IndexMut};
use std::rc::{Rc};
use std::str::{FromStr};

//use std::fs;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
// For now, always clone explicitly.
// This makes transition to "BigNum" easier, I hope?
struct Natural(u64);

/*impl Add<u64> for Natural {
    type Output = Natural;

    fn add(self, rhs: u64) -> Natural {
        Natural(self.0.checked_add(rhs).unwrap())
    }
}*/

impl Add<Natural> for Natural {
    type Output = Natural;

    fn add(self, rhs: Natural) -> Natural {
        Natural(self.0.checked_add(rhs.0).unwrap())
    }
}

/*impl Sub<u64> for Natural {
    type Output = Natural;

    fn sub(self, rhs: u64) -> Natural {
        Natural(self.0.saturating_sub(rhs))
    }
}*/

impl Sub<Natural> for Natural {
    type Output = Natural;

    fn sub(self, rhs: Natural) -> Natural {
        Natural(self.0.saturating_sub(rhs.0))
    }
}

impl Natural {
    fn decrement(&mut self) {
        self.0 = self.0.checked_sub(1).unwrap();
    }

    fn is_zero(&self) -> bool {
        self.0 == 0
    }
}

fn convert_int_error(e: ParseIntError) -> Error {
    use IntErrorKind::*;
    let msg : String = match e.kind() {
        Empty => "empty specifier".into(),
        InvalidDigit => format!("not a digit ({})", e),
        Overflow => format!("cannot handle large naturals yet (BUG) ({})", e),
        Underflow => format!("must be non-negative ({})", e),
        Zero => unreachable!(),
        _ => format!("unknown (BUG) ({})", e),  // unfixable
    };
    Error::new(ErrorKind::InvalidData, msg)
}

impl FromStr for Natural {
    type Err = Error;

    fn from_str(digits: &str) -> Result<Natural> {
        let radix = match digits.chars().next() {
            None => return Err(Error::new(ErrorKind::InvalidData,
                "Cannot parse natual '0'.  Did you mean '0x0'?")),
            Some('b') => 2,
            Some('o') => 8,
            Some('d') => 10,
            Some('x') => 16,
            Some(c) => return Err(Error::new(ErrorKind::InvalidData,
                format!("Unknown base '{}'", c))),
        };
        let result = u64::from_str_radix(&digits[1..], radix);
        let value = result.map_err(convert_int_error)?;
        Ok(Natural(value))
    }
}

#[cfg(test)]
mod test_natural {
    use super::*;

    #[test]
    fn test_add() {
        assert_eq!(Natural(42) + Natural(1337), Natural(42 + 1337));
        assert_eq!(Natural(0) + Natural(0), Natural(0));
    }

    #[test]
    fn test_sub() {
        assert_eq!(Natural(0) - Natural(0), Natural(0));
        assert_eq!(Natural(5) - Natural(3), Natural(2));
        assert_eq!(Natural(5) - Natural(55), Natural(0));
    }

    #[test]
    fn test_clonable() {
        let x = Natural(123);
        let y = x.clone() + Natural(321);
        let z = y.clone() - Natural(40);
        assert_eq!(x, Natural(123));
        assert_eq!(y, Natural(444));
        assert_eq!(z, Natural(404));
    }

    #[test]
    fn test_basic_parsing() {
        assert_eq!(Natural(0), "x0".parse().unwrap());
        assert_eq!(Natural(0x10), "x10".parse().unwrap());
        assert_eq!(Natural(1337), "x539".parse().unwrap());
        assert_eq!(Natural(0xFFFFFFFF), "xFFFFFFFF".parse().unwrap());
        assert_eq!(Natural(0xFFFFFFFFFFFFFFFF), "xFFFFFFFFFFFFFFFF".parse().unwrap());
        assert!("xG".parse::<Natural>().is_err());
    }

    #[test]
    #[ignore = "Currently fails because `Natural` uses a bounded-size implementation (u64)."]
    fn test_large_naturals() {
        assert!(!"x10000000000000000".parse::<Natural>().is_err());
        assert!(!"x100000000000000000000000000000000".parse::<Natural>().is_err());
    }
}

#[derive(Clone, Debug, Ord, Eq, PartialOrd, PartialEq)]
enum ParseId {
    FromNumber(u32),
    FromString(String),
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Token {
    Add,
    Number(Natural),
    To,
    Ident(ParseId),
    Into,
    // Ident
    // ---
    Subtract,
    // Number
    From,
    // Ident
    // Into
    // Ident
    // ---
    Loop,
    // Ident
    Do,
    // <Recursion>
    End,
    // ---
    // Do
    // Number
    Times,
    // <Recursion>
    // End
    // ---
    While,
    // Ident
    // Do
    // <Recursion>
    // End
    // ---
    // Calc,
    // Plus,
    // SatMinus,
    // Mult,
    // Div,
    // Mod,
    // Number
    // Ident
    // Into
    // Ident
    // ---
}

struct Tokenizer<I> {
    source: I,
    errored: bool,
    peeked_reverse: Vec<char>,
}

impl<I: Iterator> Tokenizer<I> {
    pub fn new(source: I) -> Tokenizer<I> {
        Tokenizer { source, errored: false, peeked_reverse: Vec::with_capacity(2) }
    }
}

impl<I: Iterator<Item = Result<char>>> Tokenizer<I> {
    // Heavily inspired by:
    // https://github.com/SerenityOS/serenity/blob/master/DevTools/IPCCompiler/main.cpp#L84

    // TODO: None of these functions should be called by the outside.

    fn try_consume_one(&mut self) -> Option<Result<char>> {
        if let Some(c) = self.peeked_reverse.pop() {
            return Some(Ok(c));
        }
        if self.errored {
            return None;
        }

        let result = self.source.next();
        self.errored = match result {
            None => true,
            Some(Err(_)) => true,
            Some(Ok(_)) => false,
        };
        result
    }

    fn consume_one(&mut self) -> Result<char> {
        self.try_consume_one().unwrap_or_else(
            || Err(Error::new(ErrorKind::UnexpectedEof, "Tried to consume non-existent char"))
        )
    }

    fn push(&mut self, c: char) {
        self.peeked_reverse.push(c);
    }

    fn consume_while<P: FnMut(char) -> bool>(&mut self, mut predicate: P) -> Result<String> {
        let mut builder = String::with_capacity(8);
        loop {
            let next = match self.try_consume_one() {
                None => break,
                Some(x) => x?,
            };
            if predicate(next) {
                builder.push(next)
            } else {
                self.push(next);
                break;
            }
        }
        // TODO: Is `shrink_to_fit` here harmful or beneficial?
        builder.shrink_to_fit();
        return Ok(builder)
    }

    fn consume_whitespace(&mut self) -> Result<()> {
        loop {
            self.consume_while(|c| c.is_whitespace())?;
            match self.try_consume_one() {
                None => break,
                Some(Err(e)) => return Err(e),
                Some(Ok('#')) => (),
                Some(Ok(c)) => {
                    self.push(c);
                    break;
                },
            }
            self.consume_while(|c| c != '\n')?;
            let _newline = self.consume_one()?;
            debug_assert!(_newline == '\n');
        }
        Ok(())
    }

    fn next_some(&mut self) -> Result<Token> {
        use Token::*;
        let word = self.consume_while(|c| !c.is_whitespace())?;
        match word.as_str() {
            "add"      => return Ok(Add     ),
            "to"       => return Ok(To      ),
            "into"     => return Ok(Into    ),
            "subtract" => return Ok(Subtract),
            "from"     => return Ok(From    ),
            "loop"     => return Ok(Loop    ),
            "do"       => return Ok(Do      ),
            "end"      => return Ok(End     ),
            "times"    => return Ok(Times   ),
            "while"    => return Ok(While   ),
            // "calc"     => return Ok(Calc    ),
            // "plus"     => return Ok(Plus    ),
            // "satminus" => return Ok(SatMinus),
            // "mult"     => return Ok(Mult    ),
            // "div"      => return Ok(Div     ),
            // "mod"      => return Ok(Mod     ),
            _ => {},
        }
        debug_assert!(!word.is_empty());

        match word.chars().next().unwrap() {
            'v' => Ok(Ident(ParseId::FromNumber(word[1..].parse().map_err(convert_int_error)?))),
            '_' => Ok(Ident(ParseId::FromString(word[1..].into()))),
            '0' => Ok(Number(word[1..].parse()?)),
            _ => Err(Error::new(ErrorKind::InvalidData,
                format!("Unknown token '{}'", word))),
        }
    }

    fn unfused_next(&mut self) -> Option<Result<Token>> {
        match self.consume_whitespace() {
            Ok(()) => { /* Continue. */ },
            Err(e) => return Some(Err(e)),
        }

        match self.try_consume_one() {
            None => return None,
            Some(Err(e)) => return Some(Err(e)),
            Some(Ok(c)) => self.push(c),
        };

        Some(self.next_some())
    }
}

impl<I: Iterator<Item = Result<char>>> Iterator for Tokenizer<I> {
    type Item = Result<Token>;

    fn next(&mut self) -> Option<Result<Token>> {
        let the_next = self.unfused_next();
        if let Some(Err(_)) = the_next {
            self.errored = true;
        }

        the_next
    }
}

#[cfg(test)]
mod test_tokenizer {
    use super::*;

    fn tokenize_string(s: &str) -> (Vec<Token>, Option<Error>) {
        let mut tokenizer = Tokenizer::new(s.chars().map(|c| Ok(c)));
        let mut tokens = Vec::with_capacity(10);
        let mut maybe_error = None;
        for r in &mut tokenizer {
            assert!(maybe_error.is_none());
            match r {
                Ok(t) => tokens.push(t),
                Err(e) => maybe_error = Some(e),
            }
        }
        assert!(tokenizer.next().is_none());
        assert!(tokenizer.next().is_none());
        assert!(tokenizer.next().is_none());

        (tokens, maybe_error)
    }

    #[test]
    fn test_empty() {
        let (tokens, maybe_error) = tokenize_string("");
        assert_eq!(tokens, vec![]);
        assert!(maybe_error.is_none());
    }

    #[test]
    fn test_simple() {
        use Token::*;
        let (tokens, maybe_error) = tokenize_string("add subtract end");
        assert_eq!(tokens, vec![Add, Subtract, End]);
        assert!(maybe_error.is_none());
    }

    #[test]
    fn test_whitespace() {
        use Token::*;
        let (tokens, maybe_error) = tokenize_string("  add   \n\t   \t\tsubtract\nend\tfrom # loop loop\tend\ntimes  ");
        assert_eq!(tokens, vec![Add, Subtract, End, From, Times]);
        assert!(maybe_error.is_none());
    }

    #[test]
    fn test_multiwhitespace() {
        use Token::*;
        let (tokens, maybe_error) = tokenize_string("add subtract\n# # into # into #\n\n# into\n#into#into\n#\n#\nend");
        assert_eq!(tokens, vec![Add, Subtract, End]);
        assert!(maybe_error.is_none());
    }

    #[test]
    fn test_unknown_token() {
        use Token::*;
        let (tokens, maybe_error) = tokenize_string("add strange");
        assert_eq!(tokens, vec![Add]);
        assert_eq!(maybe_error.unwrap().kind(), ErrorKind::InvalidData);
    }

    #[test]
    fn test_partial_token() {
        use Token::*;
        let (tokens, maybe_error) = tokenize_string("add fro");
        assert_eq!(tokens, vec![Add]);
        assert_eq!(maybe_error.unwrap().kind(), ErrorKind::InvalidData);
    }

    #[test]
    fn test_parsing() {
        use Token::*;
        let (tokens, maybe_error) = tokenize_string("do 0x64 from _thing end v1337 times");
        assert_eq!(tokens, vec![
            Do, Number(Natural(100)),
            From, Ident(ParseId::FromString("thing".to_string())),
            End, Ident(ParseId::FromNumber(1337)),
            Times
        ]);
        assert!(maybe_error.is_none());
    }

    #[test]
    fn test_partial_natural_0() {
        use Token::*;
        let (tokens, maybe_error) = tokenize_string("add 0 from");
        assert_eq!(tokens, vec![Add]);
        assert_eq!(maybe_error.unwrap().kind(), ErrorKind::InvalidData);
    }

    #[test]
    fn test_partial_natural_0x() {
        use Token::*;
        let (tokens, maybe_error) = tokenize_string("add 0x from");
        assert_eq!(tokens, vec![Add]);
        assert_eq!(maybe_error.unwrap().kind(), ErrorKind::InvalidData);
    }

    #[test]
    fn test_partial_variable_named() {
        use Token::*;
        let (tokens, maybe_error) = tokenize_string("add _ from");
        assert_eq!(tokens, vec![Add, Ident(ParseId::FromString("".to_string())), From]);
        assert!(maybe_error.is_none());
    }

    #[test]
    fn test_partial_variable_number() {
        use Token::*;
        let (tokens, maybe_error) = tokenize_string("add v from");
        assert_eq!(tokens, vec![Add]);
        assert_eq!(maybe_error.unwrap().kind(), ErrorKind::InvalidData);
    }
}

#[derive(Clone, Copy, Debug, Ord, Eq, PartialOrd, PartialEq)]
struct VarId(u32);

#[derive(Clone, Debug)]
struct PloopBlock(Rc<Vec<PloopStatement>>);

#[derive(Clone, Debug)]
enum PloopStatement {
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
                let newval = conf.state[&src].clone() + amount;
                conf.state[&dst] = newval;
            },
            SubtractFromInto(amount, src, dst) => {
                println!("SubtractFromInto: {:?} {:?} {:?}", amount, src, dst);
                let newval = conf.state[&src].clone() - amount;
                conf.state[&dst] = newval;
            },
            LoopDo(var, block) => {
                println!("LoopDo: {:?} {:?}", var, block);
                conf.push(DoTimes(conf.state[&var].clone(), block));
            },
            DoTimes(mut amount, block) => {
                println!("DoTimes: {:?} {:?}", amount, block);
                if !amount.is_zero() {
                    amount.decrement();
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
struct Environment(BTreeMap<VarId, Natural>);

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
        self.0.get(varid).unwrap_or(&Natural(0))
    }
}

impl IndexMut<&VarId> for Environment {
    fn index_mut(&mut self, varid: &VarId) -> &mut Self::Output {
        self.0.entry(*varid).or_default()
    }
}

#[derive(Clone, Debug)]
struct Configuration {
    state: Environment,
    stack: Vec<PloopStatement>,
}

impl Configuration {
    fn new(input: Natural, program: &PloopBlock) -> Configuration {
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

    fn step(&mut self) {
        let statement : PloopStatement = self.stack.pop().unwrap();
        statement.apply(self);
    }

    fn run(&mut self) {
        while !self.stack.is_empty() {
            self.step();
            println!("Configuration afterwards: {:?}", self);
        }
    }
}

fn main() {
    /*let data = fs::read_to_string("/etc/hosts").expect("Unable to read file");
    println!("{}", data);*/

    use PloopStatement::*;
    let sample_prog = PloopBlock(Rc::new(vec![
        SubtractFromInto(Natural(5), VarId(0), VarId(1)),
        AddToInto(Natural(5), VarId(1), VarId(1)),
        AddToInto(Natural(0), VarId(2), VarId(0)),
        LoopDo(VarId(1), PloopBlock(Rc::new(vec![
            AddToInto(Natural(2), VarId(0), VarId(0)),
        ]))),
        WhileDo(VarId(3), PloopBlock(Rc::new(vec![]))),
        // This implements:
        // x1 = min(5, x0)
        // x0 = 2 * x1
    ]));

    let mut conf = Configuration::new(Natural(7), &sample_prog);
    println!("Initial configuration: {:?}", conf);
    conf.run();
    println!("Done");
}
