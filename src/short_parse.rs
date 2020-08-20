use num_traits::identities::Zero;
use std::io::{Error, ErrorKind, Result};
use std::iter::Peekable;

use super::{nat, IdentToken, Natural, Token};

#[derive(Clone, Debug, Eq, PartialEq)]
enum CalcOrd {
    Cmp,
    Ne,
    Eq,
    Lt,
    Le,
    Gt,
    Ge,
}

impl CalcOrd {
    #[must_use]
    fn gen_code(self, lhs: &ParseIdent, rhs: &ParseIdent, dst: &ParseIdent) -> Vec<ParseStatement> {
        use ParseStatement::*;
        let tmp = ParseIdent::Dynamic(DynamicIdent::CalcTemp(0));
        let v0nonzero = ParseIdent::Dynamic(DynamicIdent::CalcTemp(1));
        let v1nonzero = ParseIdent::Dynamic(DynamicIdent::CalcTemp(2));
        let mut code = vec![
            // v0nonzero := (lhs - rhs) > 0
            AddToInto(nat(0), lhs.clone(), tmp.clone()),
            LoopDo(rhs.clone(), ParseBlock(vec![
                SubtractFromInto(nat(1), tmp.clone(), tmp.clone()),
            ])),
            AddToInto(nat(0), ParseIdent::Dynamic(DynamicIdent::Zero), v0nonzero.clone()),
            LoopDo(tmp.clone(), ParseBlock(vec![
                AddToInto(nat(1), ParseIdent::Dynamic(DynamicIdent::Zero), v0nonzero.clone()),
            ])),
            // v1nonzero := (rhs - lhs) > 0
            AddToInto(nat(0), rhs.clone(), tmp.clone()),
            LoopDo(lhs.clone(), ParseBlock(vec![
                SubtractFromInto(nat(1), tmp.clone(), tmp.clone()),
            ])),
            AddToInto(nat(0), ParseIdent::Dynamic(DynamicIdent::Zero), v1nonzero.clone()),
            LoopDo(tmp.clone(), ParseBlock(vec![
                AddToInto(nat(1), ParseIdent::Dynamic(DynamicIdent::Zero), v1nonzero.clone()),
            ])),
        ];
        // assert ! ( _v0nonzero && _v1nonzero )
        drop(tmp);
        code.append(&mut match self {
            CalcOrd::Cmp => vec![
                // 1 - v1nonzero + v0nonzero
                AddToInto(nat(1), ParseIdent::Dynamic(DynamicIdent::Zero), dst.clone()),
                LoopDo(v1nonzero, ParseBlock(vec![
                    SubtractFromInto(nat(1), dst.clone(), dst.clone()),
                ])),
                LoopDo(v0nonzero, ParseBlock(vec![
                    AddToInto(nat(1), dst.clone(), dst.clone()),
                ])),
            ],
            CalcOrd::Ne => vec![
                // 0 + v0nonzero + v1nonzero
                AddToInto(nat(0), ParseIdent::Dynamic(DynamicIdent::Zero), dst.clone()),
                LoopDo(v0nonzero, ParseBlock(vec![
                    AddToInto(nat(1), ParseIdent::Dynamic(DynamicIdent::Zero), dst.clone()),
                ])),
                LoopDo(v1nonzero, ParseBlock(vec![
                    AddToInto(nat(1), ParseIdent::Dynamic(DynamicIdent::Zero), dst.clone()),
                ])),
            ],
            CalcOrd::Eq => vec![
                // 1 - v0nonzero - v1nonzero
                AddToInto(nat(1), ParseIdent::Dynamic(DynamicIdent::Zero), dst.clone()),
                LoopDo(v0nonzero, ParseBlock(vec![
                    AddToInto(nat(0), ParseIdent::Dynamic(DynamicIdent::Zero), dst.clone()),
                ])),
                LoopDo(v1nonzero, ParseBlock(vec![
                    AddToInto(nat(0), ParseIdent::Dynamic(DynamicIdent::Zero), dst.clone()),
                ])),
            ],
            CalcOrd::Lt => vec![
                // = v1nonzero
                AddToInto(nat(0), v1nonzero, dst.clone()),
            ],
            CalcOrd::Le => vec![
                // 1 - v0nonzero
                AddToInto(nat(1), ParseIdent::Dynamic(DynamicIdent::Zero), dst.clone()),
                LoopDo(v0nonzero, ParseBlock(vec![
                    SubtractFromInto(nat(1), dst.clone(), dst.clone()),
                ])),
            ],
            CalcOrd::Gt => vec![
                // = v0nonzero
                AddToInto(nat(0), v0nonzero, dst.clone()),
            ],
            CalcOrd::Ge => vec![
                // 1 - v1nonzero
                AddToInto(nat(1), ParseIdent::Dynamic(DynamicIdent::Zero), dst.clone()),
                LoopDo(v1nonzero, ParseBlock(vec![
                    SubtractFromInto(nat(1), dst.clone(), dst.clone()),
                ])),
            ],
        });

        code
    }
}

enum DivMod {
    Div,
    Mod,
    Take,
}

impl DivMod {
    #[must_use]
    fn gen_code(self, lhs: &ParseIdent, rhs: &ParseIdent, dst: &ParseIdent) -> Vec<ParseStatement> {
        use ParseStatement::*;
        let unsure = ParseIdent::Dynamic(DynamicIdent::CalcTemp(0));
        let res_div = ParseIdent::Dynamic(DynamicIdent::CalcTemp(1));
        let res_mod = ParseIdent::Dynamic(DynamicIdent::CalcTemp(2));
        let next_overmod = ParseIdent::Dynamic(DynamicIdent::CalcTemp(3));

        let mut code = vec![
            AddToInto(nat(1), ParseIdent::Dynamic(DynamicIdent::Zero), unsure.clone()),
            AddToInto(nat(0), ParseIdent::Dynamic(DynamicIdent::Zero), res_div.clone()),
            AddToInto(nat(0), lhs.clone(), res_mod.clone()),

            // Invariants:
            // res_div * rhs + res_mod == lhs
            // (unsure == 0) implies res_div == floor(lhs / rhs)
            LoopDo(lhs.clone(), ParseBlock(vec![
                LoopDo(unsure.clone(), ParseBlock(vec![
                    // Compute (res_mod + 1) - rhs
                    AddToInto(nat(1), res_mod.clone(), next_overmod.clone()),
                    LoopDo(rhs.clone(), ParseBlock(vec![
                        SubtractFromInto(nat(1), next_overmod.clone(), next_overmod.clone()),
                    ])),
                    // If next_overmod is > 0, then res_mod was >= rhs.
                    AddToInto(nat(0), ParseIdent::Dynamic(DynamicIdent::Zero), unsure.clone()),
                    LoopDo(next_overmod.clone(), ParseBlock(vec![
                        AddToInto(nat(1), ParseIdent::Dynamic(DynamicIdent::Zero), unsure.clone()),
                    ])),
                    // And if that wasn't the answer, need to increment:
                    LoopDo(unsure.clone(), ParseBlock(vec![
                        AddToInto(nat(1), res_div.clone(), res_div.clone()),
                        // This "add one subtract one" game is a bit tedious.
                        // TODO: Optimize "div" calc
                        SubtractFromInto(nat(1), next_overmod.clone(), res_mod.clone()),
                    ])),
                ])),
            ])),
        ];
        match self {
            DivMod::Div =>
                code.push(AddToInto(nat(0), res_div, dst.clone())),
            DivMod::Mod =>
                code.push(AddToInto(nat(0), res_mod, dst.clone())),
            DivMod::Take => {
                code.push(AddToInto(nat(0), res_div, lhs.clone()));
                code.push(AddToInto(nat(0), res_mod, dst.clone()));
            }
        }

        code
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum BinaryCalcOperation {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    LogAnd,
    LogOr,
    OrdQuery(CalcOrd),
}

impl BinaryCalcOperation {
    #[must_use]
    fn gen_code(self, lhs: &ParseIdent, rhs: &ParseIdent, dst: &ParseIdent) -> Vec<ParseStatement> {
        /* Some, if not all of these implementations cannot handle the case where dst \in \{ lhs, rhs \}.
         * CalcExpression handles this by copying all supplied idents to local registers first. */
        use BinaryCalcOperation::*;
        use ParseStatement::*;
        // See also exec::test::test_manual_*
        match self {
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
                AddToInto(nat(0), ParseIdent::Dynamic(DynamicIdent::Zero), dst.clone()),
                LoopDo(lhs.clone(), ParseBlock(vec![
                    LoopDo(rhs.clone(), ParseBlock(vec![
                        AddToInto(nat(1), dst.clone(), dst.clone()),
                    ])),
                ])),
            ],
            LogAnd => vec![
                AddToInto(nat(0), ParseIdent::Dynamic(DynamicIdent::Zero), dst.clone()),
                // Sure we could use Mul's implementation.
                // However, The outer loop would be too difficult to optimize,
                // so we make sure that the outer loop only runs 0 or 1 times.
                AddToInto(nat(0), ParseIdent::Dynamic(DynamicIdent::Zero), ParseIdent::Dynamic(DynamicIdent::CalcTemp(0))),
                LoopDo(lhs.clone(), ParseBlock(vec![
                    AddToInto(nat(1), ParseIdent::Dynamic(DynamicIdent::Zero), ParseIdent::Dynamic(DynamicIdent::CalcTemp(0))),
                ])),
                LoopDo(ParseIdent::Dynamic(DynamicIdent::CalcTemp(0)), ParseBlock(vec![
                    LoopDo(rhs.clone(), ParseBlock(vec![
                        AddToInto(nat(1), ParseIdent::Dynamic(DynamicIdent::Zero), dst.clone()),
                    ])),
                ])),
            ],
            LogOr => vec![
                // 0 + lhs + rhs …ish.
                AddToInto(nat(0), ParseIdent::Dynamic(DynamicIdent::Zero), dst.clone()),
                LoopDo(lhs.clone(), ParseBlock(vec![
                    AddToInto(nat(1), ParseIdent::Dynamic(DynamicIdent::Zero), dst.clone()),
                ])),
                LoopDo(rhs.clone(), ParseBlock(vec![
                    AddToInto(nat(1), ParseIdent::Dynamic(DynamicIdent::Zero), dst.clone()),
                ])),
            ],
            Div => DivMod::Div.gen_code(lhs, rhs, dst),
            Mod => DivMod::Mod.gen_code(lhs, rhs, dst),
            OrdQuery(ord) => ord.gen_code(lhs, rhs, dst),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum CalcExpression {
    Constant(Natural),
    Ident(ParseIdent),
    LogNot(Box<CalcExpression>),
    Binary(BinaryCalcOperation, Box<CalcExpression>, Box<CalcExpression>),
}

impl CalcExpression {
    fn gen_code(self, dst: &ParseIdent) -> Vec<ParseStatement> {
        let mut into = Vec::with_capacity(10);
        self.gen_code_recursive(0, dst, &mut into);
        into
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

                into.append(&mut op.gen_code(&lhs_ident, &rhs_ident, &dst));
            }
            LogNot(sub) => {
                let sub_ident = ParseIdent::Dynamic(DynamicIdent::CalcIntermediate(stack_depth));
                stack_depth += 1;
                sub.gen_code_recursive(stack_depth, &sub_ident, into);

                into.append(&mut vec![
                    // 1 - sub_ident
                    ParseStatement::AddToInto(nat(1), ParseIdent::Dynamic(DynamicIdent::Zero), dst.clone()),
                    ParseStatement::LoopDo(sub_ident, ParseBlock(vec![
                        ParseStatement::AddToInto(nat(0), ParseIdent::Dynamic(DynamicIdent::Zero), dst.clone()),
                    ])),
                ]);
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
    // ForIn
    // SplitInto
}

#[derive(Clone, Debug, Ord, Eq, PartialOrd, PartialEq)]
pub enum DynamicIdent {
    Zero,
    Named(String),
    CalcIntermediate(u32),
    CalcTemp(u32),
    If, // Due to 'Else' we will need an argument eventually.
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

    fn parse_calc_expression(&mut self) -> Result<CalcExpression> {
        use Token::*;
        match self.next()? {
            None => Err(Error::new(
                ErrorKind::UnexpectedEof,
                "Found EOF while expecting a calc expression.",
            )),
            Some(Number(nat)) => Ok(CalcExpression::Constant(nat)),
            // TODO: Light code duplication here:
            Some(Ident(IdentToken::FromNumber(id))) => {
                Ok(CalcExpression::Ident(ParseIdent::Static(id)))
            }
            Some(Ident(IdentToken::FromString(id))) => {
                Ok(CalcExpression::Ident(ParseIdent::Dynamic(DynamicIdent::Named(id))))
            }
            Some(LogNot) => {
                Ok(CalcExpression::LogNot(Box::new(self.parse_calc_expression()?)))
            }
            Some(op_token @ (Plus | SatMinus | Mult | Div | Mod | OrdCmp | OrdNe | OrdEq | OrdLt | OrdLe | OrdGt | OrdGe | LogAnd | LogOr)) => {
                let op = match op_token {
                    Plus => BinaryCalcOperation::Add,
                    SatMinus => BinaryCalcOperation::Sub,
                    Mult => BinaryCalcOperation::Mul,
                    Div => BinaryCalcOperation::Div,
                    Mod => BinaryCalcOperation::Mod,
                    OrdCmp => BinaryCalcOperation::OrdQuery(CalcOrd::Cmp),
                    OrdNe => BinaryCalcOperation::OrdQuery(CalcOrd::Ne),
                    OrdEq => BinaryCalcOperation::OrdQuery(CalcOrd::Eq),
                    OrdLt => BinaryCalcOperation::OrdQuery(CalcOrd::Lt),
                    OrdLe => BinaryCalcOperation::OrdQuery(CalcOrd::Le),
                    OrdGt => BinaryCalcOperation::OrdQuery(CalcOrd::Gt),
                    OrdGe => BinaryCalcOperation::OrdQuery(CalcOrd::Ge),
                    LogAnd => BinaryCalcOperation::LogAnd,
                    LogOr => BinaryCalcOperation::LogOr,
                    _ => unreachable!(),
                };
                Ok(CalcExpression::Binary(op, Box::new(self.parse_calc_expression()?), Box::new(self.parse_calc_expression()?)))
            }
            Some(actual) => Err(Error::new(
                ErrorKind::InvalidData,
                format!("Expected calc expression, found '{:?}' instead.", actual),
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
            Token::Calc => {
                let expr = self.parse_calc_expression()?;
                self.parse_expected(Token::Into)?;
                let dst = self.parse_ident()?;
                Ok(DoTimes(nat(1), ParseBlock(expr.gen_code(&dst))))
            }
            Token::If => {
                let expr = CalcExpression::LogNot(Box::new(
                    CalcExpression::LogNot(Box::new(
                        self.parse_calc_expression()?
                    ))
                ));
                self.parse_expected(Token::Do)?;
                let block_then = self.parse_block(false)?;
                // TODO: Support "else".
                // let block_else = match self.next()? {
                //     None => return Err(Error::new(
                //         ErrorKind::UnexpectedEof,
                //         "Found EOF while end of 'if' block; missing 'end' token?",
                //     ))
                //     Some(Token::End) => None,
                //     Some(Token::Else) => Some(self.parse_block(false)),
                // };
                self.parse_expected(Token::End)?;
                let condition = ParseIdent::Dynamic(DynamicIdent::If);
                let mut code = expr.gen_code(&condition);
                code.push(LoopDo(condition, block_then));
                // code.push(LoopDo(inv_condition, block_else))
                Ok(DoTimes(nat(1), ParseBlock(code)))
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
                Some(&(Token::End /*| Token::Else*/)) => {
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
mod test_calc_parse {
    use super::super::nat;
    use super::*;

    fn parse_token_vec(vec: Vec<Token>) -> Result<CalcExpression> {
        Parser::new(vec.into_iter().map(|t| Ok(t)).peekable()).parse_calc_expression()
    }

    #[test]
    fn test_empty() {
        assert!(parse_token_vec(vec![]).is_err());
    }

    #[test]
    fn test_nat() {
        use Token::*;
        let actual = parse_token_vec(vec![
            Number(nat(42)),
        ]).unwrap();
        let expected = CalcExpression::Constant(nat(42));
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_ignore_rest() {
        use Token::*;
        let actual = parse_token_vec(vec![
            Number(nat(1)),
            Number(nat(22)),
            Number(nat(333)),
        ]).unwrap();
        let expected = CalcExpression::Constant(nat(1));
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_ident_num() {
        use Token::*;
        let actual = parse_token_vec(vec![
            Ident(IdentToken::FromNumber(13)),
        ]).unwrap();
        let expected = CalcExpression::Ident(ParseIdent::Static(13));
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_ident_str() {
        use Token::*;
        let actual = parse_token_vec(vec![
            Ident(IdentToken::FromString("hello".into())),
        ]).unwrap();
        let expected = CalcExpression::Ident(ParseIdent::Dynamic(DynamicIdent::Named("hello".into())));
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_plus() {
        use Token::*;
        let actual = parse_token_vec(vec![
            Plus,
            Number(nat(12)),
            Ident(IdentToken::FromNumber(5)),
        ]).unwrap();
        let expected = CalcExpression::Binary(BinaryCalcOperation::Add,
            Box::new(CalcExpression::Constant(nat(12))),
            Box::new(CalcExpression::Ident(ParseIdent::Static(5))),
        );
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_recursive() {
        use Token::*;
        let actual = parse_token_vec(vec![
            Plus,
            Plus,
            Number(nat(1)),
            Number(nat(2)),
            Plus,
            Number(nat(3)),
            Number(nat(4)),
        ]).unwrap();
        let expected = CalcExpression::Binary(BinaryCalcOperation::Add,
            Box::new(CalcExpression::Binary(BinaryCalcOperation::Add,
                Box::new(CalcExpression::Constant(nat(1))),
                Box::new(CalcExpression::Constant(nat(2))),
            )),
            Box::new(CalcExpression::Binary(BinaryCalcOperation::Add,
                Box::new(CalcExpression::Constant(nat(3))),
                Box::new(CalcExpression::Constant(nat(4))),
            )),
        );
        assert_eq!(actual, expected);
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