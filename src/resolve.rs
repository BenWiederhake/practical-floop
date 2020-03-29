use std::collections::{BTreeMap, BTreeSet};
use std::rc::{Rc};

use super::{ParseId, ParseBlock, ParseStatement, VarId, PloopBlock, PloopStatement};

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
        let mut statements : Vec<&ParseStatement> = root_block.statements().iter().collect();

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
                    statements.extend(subblock.statements());
                },
                ParseStatement::DoTimes(_, subblock) => {
                    statements.extend(subblock.statements());
                },
                ParseStatement::WhileDo(a, subblock) => {
                    self.reserve_if_fixed(&a);
                    statements.extend(subblock.statements());
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
        let mut resolved_statements = Vec::with_capacity(parent_block.statements().len());
        for statement in parent_block.statements() {
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

#[cfg(test)]
mod test_resolver {
    use super::*;
    use super::super::nat;

    #[test]
    fn test_empty() {
        let input = ParseBlock::from_statements(&vec![]);
        let expected = PloopBlock(Rc::new(vec![]));
        let actual = PloopBlock::from_parsed(input);
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_idents_literal() {
        let input = ParseBlock::from_statements(&vec![
            ParseStatement::AddToInto(nat(42), ParseId::FromNumber(1337), ParseId::FromNumber(23)),
        ]);
        let expected = PloopBlock::from_statements(&vec![
            PloopStatement::AddToInto(nat(42), VarId(1337), VarId(23)),
        ]);
        let actual = PloopBlock::from_parsed(input);
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_idents_named() {
        let input = ParseBlock::from_statements(&vec![
            ParseStatement::AddToInto(nat(42), ParseId::FromString("A".into()), ParseId::FromString("B".into())),
            ParseStatement::AddToInto(nat(47), ParseId::FromString("C".into()), ParseId::FromString("A".into())),
        ]);
        let expected = PloopBlock::from_statements(&vec![
            /* Note: `0` is reserved. */
            PloopStatement::AddToInto(nat(42), VarId(1), VarId(2)),
            PloopStatement::AddToInto(nat(47), VarId(3), VarId(1)),
        ]);
        let actual = PloopBlock::from_parsed(input);
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_noninterference() {
        let input = ParseBlock::from_statements(&vec![
            ParseStatement::AddToInto(nat(42), ParseId::FromNumber(2), ParseId::FromString("A".into())),
            ParseStatement::AddToInto(nat(47), ParseId::FromString("B".into()), ParseId::FromNumber(3)),
        ]);
        let expected = PloopBlock::from_statements(&vec![
            /* Note: `0` is reserved. */
            PloopStatement::AddToInto(nat(42), VarId(2), VarId(1)),
            PloopStatement::AddToInto(nat(47), VarId(4), VarId(3)),
        ]);
        let actual = PloopBlock::from_parsed(input);
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_recursion() {
        let input = ParseBlock::from_statements(&vec![
            ParseStatement::LoopDo(ParseId::FromNumber(2), ParseBlock::from_statements(&vec![
                ParseStatement::AddToInto(nat(5), ParseId::FromString("A".into()), ParseId::FromString("C".into())),
                ParseStatement::AddToInto(nat(9), ParseId::FromString("B".into()), ParseId::FromString("A".into())),
            ])),
            ParseStatement::WhileDo(ParseId::FromString("x".into()), ParseBlock::from_statements(&vec![
                ParseStatement::AddToInto(nat(8), ParseId::FromString("A".into()), ParseId::FromNumber(1)),
                ParseStatement::AddToInto(nat(4), ParseId::FromString("E".into()), ParseId::FromString("x".into())),
            ])),
        ]);
        let expected = PloopBlock::from_statements(&vec![
            /* Note: `0` is reserved. */
            PloopStatement::LoopDo(VarId(2), PloopBlock::from_statements(&vec![
                PloopStatement::AddToInto(nat(5), VarId(3), VarId(4)),
                PloopStatement::AddToInto(nat(9), VarId(5), VarId(3)),
            ])),
            PloopStatement::WhileDo(VarId(6), PloopBlock::from_statements(&vec![
                PloopStatement::AddToInto(nat(8), VarId(3), VarId(1)),
                PloopStatement::AddToInto(nat(4), VarId(7), VarId(6)),
            ])),
        ]);
        let actual = PloopBlock::from_parsed(input);
        assert_eq!(expected, actual);
    }
}
