#![feature(int_error_matching)]

use std::collections::{BTreeMap, BTreeSet};
use std::io::{Error, ErrorKind, Result};
use std::iter::{Peekable};
use std::num::{ParseIntError, IntErrorKind};
use std::ops::{Add, Deref, Sub, Index, IndexMut};
use std::rc::{Rc};
use std::str::{FromStr};

//use std::fs;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
// For now, always clone explicitly.
// This makes transition to "BigNum" easier, I hope?
struct Natural(u64);

impl Add<Natural> for Natural {
    type Output = Natural;

    fn add(self, rhs: Natural) -> Natural {
        Natural(self.0.checked_add(rhs.0).unwrap())
    }
}

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

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParseBlock(Vec<ParseStatement>);

#[derive(Clone, Debug, Eq, PartialEq)]
enum ParseStatement {
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

fn parse<I: Iterator<Item = Result<Token>>>(iter: I) -> Result<ParseBlock> {
    parse_peekable(iter.peekable())
}

fn parse_peekable<I: Iterator<Item = Result<Token>>>(iter: Peekable<I>) -> Result<ParseBlock> {
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
        //assert_eq!(parse_from_stream(vec![Add, Number(Natural(100)), To, Ident(ParseId::FromNumber(1337)), Into, Ident(ParseId::FromString("foo".to_string()))].iter().map(|t| Ok(t.clone()))).unwrap(), ParseBlock(vec![AddToInto(Natural(100), ParseId::FromNumber(1337), ParseId::FromString("foo".to_string()))]));
        let parse_result = parse_token_vec(vec![
            Add, Number(Natural(100)),
            To, Ident(ParseId::FromNumber(1337)),
            Into, Ident(ParseId::FromString("foo".to_string())),
        ]);
        assert_eq!(parse_result.unwrap(), ParseBlock(vec![
            AddToInto(Natural(100), ParseId::FromNumber(1337), ParseId::FromString("foo".to_string()))
        ]));
    }

    #[test]
    fn test_dotimes() {
        use Token::*;
        use ParseStatement::*;
        let parse_result = parse_token_vec(vec![
            Do, Number(Natural(100)), Times,
            End,
        ]);
        assert_eq!(parse_result.unwrap(), ParseBlock(vec![
            DoTimes(Natural(100), ParseBlock(vec![])),
        ]));
    }
}

struct Resolver {
    reserved: BTreeSet<VarId>,
    dict: BTreeMap<String, VarId>,
    first_unchecked: u32,
}

impl Resolver {
    fn new() -> Resolver {
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

    fn reserve_static(&mut self, root_block: &ParseBlock) {
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

    fn resolve_remaining(&mut self, parent_block: &ParseBlock) -> PloopBlock {
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

fn resolve(block: ParseBlock) -> PloopBlock {
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
            ParseStatement::AddToInto(Natural(42), ParseId::FromNumber(1337), ParseId::FromNumber(23)),
        ]);
        let actual = PloopBlock(Rc::new(vec![
            PloopStatement::AddToInto(Natural(42), VarId(1337), VarId(23)),
        ]));
        let expected = resolve(input);
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_idents_named() {
        let input = ParseBlock(vec![
            ParseStatement::AddToInto(Natural(42), ParseId::FromString("A".into()), ParseId::FromString("B".into())),
            ParseStatement::AddToInto(Natural(47), ParseId::FromString("C".into()), ParseId::FromString("A".into())),
        ]);
        let actual = PloopBlock(Rc::new(vec![
            /* Note: `0` is reserved. */
            PloopStatement::AddToInto(Natural(42), VarId(1), VarId(2)),
            PloopStatement::AddToInto(Natural(47), VarId(3), VarId(1)),
        ]));
        let expected = resolve(input);
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_noninterference() {
        let input = ParseBlock(vec![
            ParseStatement::AddToInto(Natural(42), ParseId::FromNumber(2), ParseId::FromString("A".into())),
            ParseStatement::AddToInto(Natural(47), ParseId::FromString("B".into()), ParseId::FromNumber(3)),
        ]);
        let actual = PloopBlock(Rc::new(vec![
            /* Note: `0` is reserved. */
            PloopStatement::AddToInto(Natural(42), VarId(2), VarId(1)),
            PloopStatement::AddToInto(Natural(47), VarId(4), VarId(3)),
        ]));
        let expected = resolve(input);
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_recursion() {
        let input = ParseBlock(vec![
            ParseStatement::LoopDo(ParseId::FromNumber(2), ParseBlock(vec![
                ParseStatement::AddToInto(Natural(5), ParseId::FromString("A".into()), ParseId::FromString("C".into())),
                ParseStatement::AddToInto(Natural(9), ParseId::FromString("B".into()), ParseId::FromString("A".into())),
            ])),
            ParseStatement::WhileDo(ParseId::FromString("x".into()), ParseBlock(vec![
                ParseStatement::AddToInto(Natural(8), ParseId::FromString("A".into()), ParseId::FromNumber(1)),
                ParseStatement::AddToInto(Natural(4), ParseId::FromString("E".into()), ParseId::FromString("x".into())),
            ])),
        ]);
        let actual = PloopBlock(Rc::new(vec![
            /* Note: `0` is reserved. */
            PloopStatement::LoopDo(VarId(2), PloopBlock(Rc::new(vec![
                PloopStatement::AddToInto(Natural(5), VarId(3), VarId(4)),
                PloopStatement::AddToInto(Natural(9), VarId(5), VarId(3)),
            ]))),
            PloopStatement::WhileDo(VarId(6), PloopBlock(Rc::new(vec![
                PloopStatement::AddToInto(Natural(8), VarId(3), VarId(1)),
                PloopStatement::AddToInto(Natural(4), VarId(7), VarId(6)),
            ]))),
        ]));
        let expected = resolve(input);
        assert_eq!(expected, actual);
    }
}

#[derive(Clone, Copy, Debug, Ord, Eq, PartialOrd, PartialEq)]
struct VarId(u32);

#[derive(Clone, Debug, Eq, PartialEq)]
struct PloopBlock(Rc<Vec<PloopStatement>>);

impl PloopBlock {
    fn from_iter<I: Iterator<Item = Result<char>>>(iter: I) -> Result<PloopBlock> {
        let token_iter = Tokenizer::new(iter);
        let parsed_block = parse(token_iter)?;
        Ok(resolve(parsed_block))
    }

    fn from<S: Deref<Target=str>>(string: S) -> Result<PloopBlock> {
        PloopBlock::from_iter(string.chars().map(|c| Ok(c)))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
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

    let mut conf = Configuration::new(Natural(7), &sample_prog);
    println!("Initial configuration: {:?}", conf);
    conf.run();
    println!("Done");
}
