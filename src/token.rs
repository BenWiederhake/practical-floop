use std::io::{Error, ErrorKind, Result};
use std::num::{IntErrorKind, ParseIntError};

use num_traits::{Num};

// Who you gonna call?!
use super::{Natural};

fn convert_num_error(e: ParseIntError) -> Error {
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

fn parse_natural(digits: &str) -> Result<Natural> {
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

    Natural::from_str_radix(&digits[1..], radix).map_err(
        |e| Error::new(ErrorKind::InvalidData, e)
    )
}

pub fn nat(n: u64) -> Natural {
    Natural::from(n)
}

#[cfg(test)]
mod test_natural {
    use super::*;
    use num_traits::ops::checked::{CheckedSub};

    #[test]
    fn test_add() {
        assert_eq!(nat(42) + &nat(1337), nat(42 + 1337));
        assert_eq!(nat(0) + &nat(0), nat(0));
    }

    #[test]
    fn test_sub() {
        assert_eq!(nat(0).checked_sub(&nat(0)), Some(nat(0)));
        assert_eq!(nat(5).checked_sub(&nat(3)), Some(nat(2)));
        assert_eq!(nat(5).checked_sub(&nat(55)), None);
    }

    #[test]
    fn test_clonable() {
        let x = nat(123);
        let y = x.clone() + &nat(321);
        let z = y.clone().checked_sub(&nat(40)).unwrap();
        assert_eq!(x, nat(123));
        assert_eq!(y, nat(444));
        assert_eq!(z, nat(404));
    }

    #[test]
    fn test_basic_parsing() {
        assert_eq!(nat(0), parse_natural("x0").unwrap());
        assert_eq!(nat(0x10), parse_natural("x10").unwrap());
        assert_eq!(nat(1337), parse_natural("x539").unwrap());
        assert_eq!(nat(0xFFFFFFFF), parse_natural("xFFFFFFFF").unwrap());
        assert_eq!(nat(0xFFFFFFFFFFFFFFFFu64), parse_natural("xFFFFFFFFFFFFFFFF").unwrap());
        assert!("xG".parse::<Natural>().is_err());
    }

    #[test]
    fn test_large_naturals() {
        assert!(!parse_natural("x10").is_err());
        assert!(!parse_natural("x10000000000000000").is_err());
        assert!(!parse_natural("x100000000000000000000000000000000").is_err());
    }
}

#[derive(Clone, Debug, Ord, Eq, PartialOrd, PartialEq)]
pub enum ParseIdent {
    FromNumber(u32),
    FromString(String),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Token {
    Add,
    Number(Natural),
    To,
    Ident(ParseIdent),
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

pub struct Tokenizer<I> {
    source: I,
    errored: bool,
    peeked_reverse: Vec<char>,
}

impl<I> Tokenizer<I> {
    pub fn new(source: I) -> Tokenizer<I> {
        Tokenizer { source, errored: false, peeked_reverse: Vec::with_capacity(2) }
    }
}

impl<I: Iterator<Item = Result<char>>> Tokenizer<I> {
    // Heavily inspired by:
    // https://github.com/SerenityOS/serenity/blob/master/DevTools/IPCCompiler/main.cpp#L84

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
            'v' => Ok(Ident(ParseIdent::FromNumber(word[1..].parse().map_err(convert_num_error)?))),
            '_' => Ok(Ident(ParseIdent::FromString(word[1..].into()))),
            '0' => Ok(Number(parse_natural(&word[1..])?)),
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
            Do, Number(nat(100)),
            From, Ident(ParseIdent::FromString("thing".to_string())),
            End, Ident(ParseIdent::FromNumber(1337)),
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
        assert_eq!(tokens, vec![Add, Ident(ParseIdent::FromString("".to_string())), From]);
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
