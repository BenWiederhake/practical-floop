use std::collections::{BTreeMap, BTreeSet};

use super::{
    DynamicIdent, ParseBlock, ParseIdent, ParseStatement, PloopBlock, PloopStatement, VarIdent,
};

pub struct Resolver {
    reserved: BTreeSet<VarIdent>,
    dict: BTreeMap<DynamicIdent, VarIdent>,
    first_unchecked: u32,
}

impl Resolver {
    pub fn new() -> Resolver {
        /* Note that this marks index 0 as "already reserved" in the eyes of
         * `reserve_any`. This is intentional, as variable 0 will be
         * considered input/output, and *really* should not be interfered with
         * by automatic assignment, even if it's not explicitly used for some
         * reason. */
        Resolver {
            reserved: BTreeSet::new(),
            dict: BTreeMap::new(),
            first_unchecked: 1,
        }
    }

    fn reserve_if_static(&mut self, ident: &ParseIdent) {
        if let &ParseIdent::Static(n) = ident {
            self.reserved.insert(VarIdent(n));
        }
    }

    pub fn reserve_static(&mut self, root_block: &ParseBlock) {
        let mut statements: Vec<&ParseStatement> = root_block.statements().iter().collect();

        while let Some(statement) = statements.pop() {
            match statement {
                ParseStatement::AddToInto(_nat, a, b) => {
                    self.reserve_if_static(&a);
                    self.reserve_if_static(&b);
                }
                ParseStatement::SubtractFromInto(_, a, b) => {
                    self.reserve_if_static(&a);
                    self.reserve_if_static(&b);
                }
                ParseStatement::LoopDo(a, subblock) => {
                    self.reserve_if_static(&a);
                    statements.extend(subblock.statements());
                }
                ParseStatement::DoTimes(_, subblock) => {
                    statements.extend(subblock.statements());
                }
                ParseStatement::WhileDo(a, subblock) => {
                    self.reserve_if_static(&a);
                    statements.extend(subblock.statements());
                }
            }
        }
    }

    fn reserve_any(&mut self) -> VarIdent {
        let chosen = (self.first_unchecked..)
            .filter(|x| !self.reserved.contains(&VarIdent(*x)))
            .next()
            .unwrap();
        self.first_unchecked = chosen + 1;
        let is_new = self.reserved.insert(VarIdent(chosen));
        assert!(is_new);
        VarIdent(chosen)
    }

    fn resolve_ident(&mut self, ident: &ParseIdent) -> VarIdent {
        match ident {
            ParseIdent::Static(var_index) => {
                assert!(self.reserved.contains(&VarIdent(*var_index)));
                VarIdent(*var_index)
            }
            ParseIdent::Dynamic(var_dyn) => {
                // TODO: Can `entry()` be used here somehow?
                if let Some(value) = self.dict.get(var_dyn) {
                    value.clone()
                } else {
                    let value = self.reserve_any();
                    // TODO: Get rid of the string clone?
                    self.dict.insert(var_dyn.clone(), value);
                    value
                }
            }
        }
    }

    pub fn resolve_remaining(&mut self, parent_block: &ParseBlock) -> PloopBlock {
        let mut resolved_statements = Vec::with_capacity(parent_block.statements().len());
        for statement in parent_block.statements() {
            resolved_statements.push(match statement {
                ParseStatement::AddToInto(amount, src, dst) => PloopStatement::AddToInto(
                    amount.clone(),
                    self.resolve_ident(src),
                    self.resolve_ident(dst),
                ),
                ParseStatement::SubtractFromInto(amount, src, dst) => {
                    PloopStatement::SubtractFromInto(
                        amount.clone(),
                        self.resolve_ident(src),
                        self.resolve_ident(dst),
                    )
                }
                ParseStatement::LoopDo(var, subblock) => PloopStatement::LoopDo(
                    self.resolve_ident(var),
                    self.resolve_remaining(subblock),
                ),
                ParseStatement::DoTimes(amount, subblock) => {
                    PloopStatement::DoTimes(amount.clone(), self.resolve_remaining(subblock))
                }
                ParseStatement::WhileDo(var, subblock) => PloopStatement::WhileDo(
                    self.resolve_ident(var),
                    self.resolve_remaining(subblock),
                ),
            });
        }

        PloopBlock::from(resolved_statements.as_slice())
    }
}

#[cfg(test)]
mod test_resolver {
    use super::super::nat;
    use super::*;

    #[test]
    fn test_empty() {
        let input = ParseBlock::from(&[][..]);
        let expected = PloopBlock::from(&[][..]);
        let actual = PloopBlock::from(&input);
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_idents_literal() {
        let input = ParseBlock::from(
            &[ParseStatement::AddToInto(
                nat(42),
                ParseIdent::Static(1337),
                ParseIdent::Static(23),
            )][..],
        );
        let expected = PloopBlock::from(
            &[PloopStatement::AddToInto(
                nat(42),
                VarIdent(1337),
                VarIdent(23),
            )][..],
        );
        let actual = PloopBlock::from(&input);
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_idents_named() {
        let input = ParseBlock::from(
            &[
                ParseStatement::AddToInto(
                    nat(42),
                    ParseIdent::Dynamic(DynamicIdent::Named("A".into())),
                    ParseIdent::Dynamic(DynamicIdent::Named("B".into())),
                ),
                ParseStatement::AddToInto(
                    nat(47),
                    ParseIdent::Dynamic(DynamicIdent::Named("C".into())),
                    ParseIdent::Dynamic(DynamicIdent::Named("A".into())),
                ),
            ][..],
        );
        let expected = PloopBlock::from(
            &[
                /* Note: `0` is reserved. */
                PloopStatement::AddToInto(nat(42), VarIdent(1), VarIdent(2)),
                PloopStatement::AddToInto(nat(47), VarIdent(3), VarIdent(1)),
            ][..],
        );
        let actual = PloopBlock::from(&input);
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_noninterference() {
        let input = ParseBlock::from(
            &[
                ParseStatement::AddToInto(
                    nat(42),
                    ParseIdent::Static(2),
                    ParseIdent::Dynamic(DynamicIdent::Named("A".into())),
                ),
                ParseStatement::AddToInto(
                    nat(47),
                    ParseIdent::Dynamic(DynamicIdent::Named("B".into())),
                    ParseIdent::Static(3),
                ),
            ][..],
        );
        let expected = PloopBlock::from(
            &[
                /* Note: `0` is reserved. */
                PloopStatement::AddToInto(nat(42), VarIdent(2), VarIdent(1)),
                PloopStatement::AddToInto(nat(47), VarIdent(4), VarIdent(3)),
            ][..],
        );
        let actual = PloopBlock::from(&input);
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_recursion() {
        let input = ParseBlock::from(
            &[
                ParseStatement::LoopDo(
                    ParseIdent::Static(2),
                    ParseBlock::from(
                        &[
                            ParseStatement::AddToInto(
                                nat(5),
                                ParseIdent::Dynamic(DynamicIdent::Named("A".into())),
                                ParseIdent::Dynamic(DynamicIdent::Named("C".into())),
                            ),
                            ParseStatement::AddToInto(
                                nat(9),
                                ParseIdent::Dynamic(DynamicIdent::Named("B".into())),
                                ParseIdent::Dynamic(DynamicIdent::Named("A".into())),
                            ),
                        ][..],
                    ),
                ),
                ParseStatement::WhileDo(
                    ParseIdent::Dynamic(DynamicIdent::Named("x".into())),
                    ParseBlock::from(
                        &[
                            ParseStatement::AddToInto(
                                nat(8),
                                ParseIdent::Dynamic(DynamicIdent::Named("A".into())),
                                ParseIdent::Static(1),
                            ),
                            ParseStatement::AddToInto(
                                nat(4),
                                ParseIdent::Dynamic(DynamicIdent::Named("E".into())),
                                ParseIdent::Dynamic(DynamicIdent::Named("x".into())),
                            ),
                        ][..],
                    ),
                ),
            ][..],
        );
        let expected = PloopBlock::from(
            &[
                /* Note: `0` is reserved. */
                PloopStatement::LoopDo(
                    VarIdent(2),
                    PloopBlock::from(
                        &[
                            PloopStatement::AddToInto(nat(5), VarIdent(3), VarIdent(4)),
                            PloopStatement::AddToInto(nat(9), VarIdent(5), VarIdent(3)),
                        ][..],
                    ),
                ),
                PloopStatement::WhileDo(
                    VarIdent(6),
                    PloopBlock::from(
                        &[
                            PloopStatement::AddToInto(nat(8), VarIdent(3), VarIdent(1)),
                            PloopStatement::AddToInto(nat(4), VarIdent(7), VarIdent(6)),
                        ][..],
                    ),
                ),
            ][..],
        );
        let actual = PloopBlock::from(&input);
        assert_eq!(expected, actual);
    }
}
