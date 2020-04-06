use num_traits::identities::Zero;
use std::io::{Error, ErrorKind, Result};
use std::iter::Peekable;

use super::{IdentToken, nat, Natural, Token};

enum CalcOrd {
    Cmp,
    Ne,
    Eq,
    Lt,
    Le,
    Gt,
    Ge,
}

enum BinaryCalcOperation {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    OrdQuery(CalcOrd),
    // FIXME: More!
}

impl BinaryCalcOperation {
    fn gen_code(self, lhs: &ParseIdent, rhs: &ParseIdent, dst: &ParseIdent, into: &mut Vec<ParseStatement>) {
        use BinaryCalcOperation::*;
        use ParseStatement::*;
        // See also exec::test::test_manual_*
        into.append(&mut match self {
            Add => vec![
                AddToInto(nat(0), lhs.clone(), dst.clone()),
                LoopDo(rhs.clone(), ParseBlock(vec![
                    AddToInto(nat(1), dst.clone(), dst.clone()),
                ])),
            ],
            Sub => vec![
                AddToInto(nat(0), lhs.clone(), dst.clone()),
                LoopDo(rhs.clone(), ParseBlock(vec![
                    SubtractFromInto(nat(1), dst.clone(), dst.clone()),
                ])),
            ],
            Mul => vec![
                unimplemented!(),
            ],
            Div => vec![
                unimplemented!(),
            ],
            Mod => vec![
                unimplemented!(),
            ],
            OrdQuery(_ord) => vec![
                unimplemented!(),
            ],
        });
    }
}

enum CalcExpression {
    Constant(Natural),
    Ident(ParseIdent),
    Binary(BinaryCalcOperation, Box<CalcExpression>, Box<CalcExpression>),
}

impl CalcExpression {
    fn gen_code(self, dst: &ParseIdent, into: &mut Vec<ParseStatement>) {
        self.gen_code_recursive(0, dst, into);
    }

    fn gen_code_recursive(self, mut stack_depth: u32, dst: &ParseIdent, into: &mut Vec<ParseStatement>) {
        use CalcExpression::*;
        match self {
            Constant(n) => {
                into.push(ParseStatement::AddToInto(n, ParseIdent::Dynamic(DynamicIdent::Zero), dst.clone()));
            }
            Ident(ident) => {
                into.push(ParseStatement::AddToInto(Natural::zero(), ident, dst.clone()));
            }
            Binary(op, lhs, rhs) => {
                let lhs_ident = ParseIdent::Dynamic(DynamicIdent::CalcIntermediate(stack_depth));
                stack_depth += 1;
                lhs.gen_code_recursive(stack_depth, &lhs_ident, into);

                let rhs_ident = ParseIdent::Dynamic(DynamicIdent::CalcIntermediate(stack_depth));
                stack_depth += 1;
                rhs.gen_code_recursive(stack_depth, &rhs_ident, into);

                op.gen_code(&lhs_ident, &rhs_ident, &dst, into);
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseBlock(Vec<ParseStatement>);

impl ParseBlock {
    pub fn try_from_iter<I: Iterator<Item = Result<Token>>>(iter: I) -> Result<ParseBlock> {
        ParseBlock::try_from_peekable(iter.peekable())
    }

    pub fn try_from_peekable<I: Iterator<Item = Result<Token>>>(
        iter: Peekable<I>,
    ) -> Result<ParseBlock> {
        Parser::new(iter).parse_block(true)
    }

    pub fn statements(&self) -> &[ParseStatement] {
        &self.0
    }

    // Collisions between `DynamicIdent`s may or may not be intentional,
    // so prevent the user from shooting their foot.
    // However, it's needed for `resolve`s tests.
    #[cfg(test)]
    pub fn from(statements: &[ParseStatement]) -> ParseBlock {
        ParseBlock(Vec::from(statements))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ParseStatement {
    AddToInto(Natural, ParseIdent, ParseIdent),
    SubtractFromInto(Natural, ParseIdent, ParseIdent),
    LoopDo(ParseIdent, ParseBlock),
    DoTimes(Natural, ParseBlock),
    WhileDo(ParseIdent, ParseBlock),
    // Calc
    // IfThen
    // IfElse
    // ForIn
    // SplitInto
}

#[derive(Clone, Debug, Ord, Eq, PartialOrd, PartialEq)]
pub enum DynamicIdent {
    Zero,
    Named(String),
    CalcIntermediate(u32),
    CalcTemp(u32),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ParseIdent {
    Static(u32),
    Dynamic(DynamicIdent),
}

struct Parser<I> {
    source: I,
    buf: Option<Token>,
}

impl<I: Iterator<Item = Result<Token>>> Parser<Peekable<I>> {
    fn new(iter: Peekable<I>) -> Parser<Peekable<I>> {
        Parser {
            source: iter,
            buf: None,
        }
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

    fn parse_expected(&mut self, expected: Token) -> Result<()> {
        match self.next()? {
            None => Err(Error::new(
                ErrorKind::UnexpectedEof,
                format!("Found EOF while expecting '{:?}' token.", expected),
            )),
            Some(actual) if actual == expected => Ok(()),
            Some(actual) => Err(Error::new(
                ErrorKind::InvalidData,
                format!(
                    "Expected token '{:?}', found '{:?}' instead.",
                    expected, actual
                ),
            )),
        }
    }

    fn parse_number(&mut self) -> Result<Natural> {
        match self.next()? {
            None => Err(Error::new(
                ErrorKind::UnexpectedEof,
                "Found EOF while expecting a number token.",
            )),
            Some(Token::Number(nat)) => Ok(nat),
            Some(actual) => Err(Error::new(
                ErrorKind::InvalidData,
                format!("Expected number token, found '{:?}' instead.", actual),
            )),
        }
    }

    fn parse_ident(&mut self) -> Result<ParseIdent> {
        match self.next()? {
            None => Err(Error::new(
                ErrorKind::UnexpectedEof,
                "Found EOF while expecting an ident token.",
            )),
            Some(Token::Ident(IdentToken::FromNumber(id))) => Ok(ParseIdent::Static(id)),
            Some(Token::Ident(IdentToken::FromString(id))) => {
                Ok(ParseIdent::Dynamic(DynamicIdent::Named(id)))
            }
            Some(actual) => Err(Error::new(
                ErrorKind::InvalidData,
                format!("Expected ident token, found '{:?}' instead.", actual),
            )),
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
            }
            Token::Subtract => {
                let amount = self.parse_number()?;
                self.parse_expected(Token::From)?;
                let src = self.parse_ident()?;
                self.parse_expected(Token::Into)?;
                let dst = self.parse_ident()?;
                Ok(SubtractFromInto(amount, src, dst))
            }
            Token::Loop => {
                let var = self.parse_ident()?;
                self.parse_expected(Token::Do)?;
                let block = self.parse_block(false)?;
                self.parse_expected(Token::End)?;
                Ok(LoopDo(var, block))
            }
            Token::Do => {
                let amount = self.parse_number()?;
                self.parse_expected(Token::Times)?;
                let block = self.parse_block(false)?;
                self.parse_expected(Token::End)?;
                Ok(DoTimes(amount, block))
            }
            Token::While => {
                let var = self.parse_ident()?;
                self.parse_expected(Token::Do)?;
                let block = self.parse_block(false)?;
                self.parse_expected(Token::End)?;
                Ok(WhileDo(var, block))
            }
            t => Err(Error::new(
                ErrorKind::InvalidData,
                format!("Cannot start statement with token '{:?}'.", t),
            )),
        }
    }

    fn parse_block(&mut self, is_outermost: bool) -> Result<ParseBlock> {
        let mut statements = Vec::with_capacity(10);

        loop {
            match self.peek()? {
                None => {
                    if !is_outermost {
                        return Err(Error::new(
                            ErrorKind::UnexpectedEof,
                            "Found EOF while parsing block; missing 'end' token?",
                        ));
                    } else {
                        break;
                    }
                }
                Some(&Token::End) => {
                    if is_outermost {
                        return Err(Error::new(ErrorKind::InvalidData, "Unmatched 'end' token"));
                    } else {
                        break;
                    }
                }
                Some(_) => {}
            };
            statements.push(self.parse_statement()?);
        }

        Ok(ParseBlock(statements))
    }
}

#[cfg(test)]
mod test_parser {
    use super::super::nat;
    use super::*;

    fn parse_token_vec(vec: Vec<Token>) -> Result<ParseBlock> {
        ParseBlock::try_from_iter(vec.into_iter().map(|t| Ok(t)))
    }

    #[test]
    fn test_empty() {
        use std::iter::empty;
        assert_eq!(
            ParseBlock::try_from_iter(empty()).unwrap(),
            ParseBlock(vec![])
        );
    }

    #[test]
    fn test_simple() {
        use ParseStatement::*;
        use Token::*;
        let parse_result = parse_token_vec(vec![
            Add,
            Number(nat(100)),
            To,
            Ident(IdentToken::FromNumber(1337)),
            Into,
            Ident(IdentToken::FromString("foo".to_string())),
        ]);
        assert_eq!(
            parse_result.unwrap(),
            ParseBlock(vec![AddToInto(
                nat(100),
                ParseIdent::Static(1337),
                ParseIdent::Dynamic(DynamicIdent::Named("foo".to_string()))
            )])
        );
    }

    #[test]
    fn test_dotimes() {
        use ParseStatement::*;
        use Token::*;
        let parse_result = parse_token_vec(vec![Do, Number(nat(100)), Times, End]);
        assert_eq!(
            parse_result.unwrap(),
            ParseBlock(vec![DoTimes(nat(100), ParseBlock(vec![])),])
        );
    }
}
