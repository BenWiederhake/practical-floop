use std::io::{Error, ErrorKind, Result};
use std::iter::{Peekable};

use super::{Natural, ParseId, Token};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseBlock(Vec<ParseStatement>);

impl ParseBlock {
    pub fn try_from_iter<I: Iterator<Item = Result<Token>>>(iter: I) -> Result<ParseBlock> {
        ParseBlock::try_from_peekable(iter.peekable())
    }

    pub fn try_from_peekable<I: Iterator<Item = Result<Token>>>(iter: Peekable<I>) -> Result<ParseBlock> {
        Parser::new(iter).parse_block(true)
    }

    pub fn statements(&self) -> &[ParseStatement] {
        &self.0
    }
}

impl From<&[ParseStatement]> for ParseBlock {
    fn from(statements: &[ParseStatement]) -> ParseBlock {
        ParseBlock(Vec::from(statements))
    }
}

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

#[cfg(test)]
mod test_parser {
    use super::*;
    use super::super::nat;

    fn parse_token_vec(vec: Vec<Token>) -> Result<ParseBlock> {
        ParseBlock::try_from_iter(vec.into_iter().map(|t| Ok(t)))
    }

    #[test]
    fn test_empty() {
        use std::iter::empty;
        assert_eq!(ParseBlock::try_from_iter(empty()).unwrap(), ParseBlock(vec![]));
    }

    #[test]
    fn test_simple() {
        use Token::*;
        use ParseStatement::*;
        let parse_result = parse_token_vec(vec![
            Add, Number(nat(100)),
            To, Ident(ParseId::FromNumber(1337)),
            Into, Ident(ParseId::FromString("foo".to_string())),
        ]);
        assert_eq!(parse_result.unwrap(), ParseBlock(vec![
            AddToInto(nat(100), ParseId::FromNumber(1337), ParseId::FromString("foo".to_string()))
        ]));
    }

    #[test]
    fn test_dotimes() {
        use Token::*;
        use ParseStatement::*;
        let parse_result = parse_token_vec(vec![
            Do, Number(nat(100)), Times,
            End,
        ]);
        assert_eq!(parse_result.unwrap(), ParseBlock(vec![
            DoTimes(nat(100), ParseBlock(vec![])),
        ]));
    }
}
