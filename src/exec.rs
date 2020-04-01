use std::collections::BTreeMap;
use std::convert::TryFrom;
use std::io::{Error, Result};
use std::iter::IntoIterator;
use std::ops::{Deref, Index, IndexMut, SubAssign};
use std::rc::Rc;

use num_traits::identities::Zero;
use num_traits::ops::checked::CheckedSub;

use super::ParseBlock;
use super::Resolver;
use super::{nat, Natural, Tokenizer};

// TODO: Can this be done without lazy_static?
lazy_static! {
    static ref THE_ZERO: Natural = Natural::zero();
}

#[derive(Clone, Copy, Debug, Ord, Eq, PartialOrd, PartialEq)]
pub struct VarIdent(pub u32);

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

    fn try_loop_shortcut(&self, amount: &Natural, conf: &mut Configuration) -> bool {
        if self.0.len() > 1 {
            // Only handle single statements for now.
            // TODO: Can we deal with multi-statement loops?  Is that desirable?
            return false;
        }
        assert!(!amount.is_zero());
        self.0[0].try_loop_shortcut(amount, conf)
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
    AddToInto(Natural, VarIdent, VarIdent),
    SubtractFromInto(Natural, VarIdent, VarIdent),
    LoopDo(VarIdent, PloopBlock),
    DoTimes(Natural, PloopBlock),
    WhileDo(VarIdent, PloopBlock),
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
                if src == dst {
                    conf.state[&dst] += amount;
                } else {
                    conf.state[&dst] = conf.state[&src].clone() + amount;
                }
            }
            SubtractFromInto(amount, src, dst) => {
                if conf.state[&src] <= amount {
                    conf.state[&dst].set_zero();
                } else if src == dst {
                    conf.state[&dst] -= amount;
                } else {
                    conf.state[&dst] = conf.state[&src].clone() - amount;
                }
            }
            LoopDo(var, block) => {
                conf.push(DoTimes(conf.state[&var].clone(), block));
            }
            DoTimes(mut amount, block) => {
                if amount.is_zero() {
                    // Base case.
                    // Nothing to do.
                } else if block.try_loop_shortcut(&amount, conf) {
                    // A loop shortcut was found and applied.
                    // Nothing to do.
                } else {
                    amount = amount.checked_sub(&nat(1)).unwrap();
                    conf.push(DoTimes(amount, block.clone()));
                    conf.push_all(&block);
                }
            }
            WhileDo(var, block) => {
                // Cannot shortcut.
                // Or rather, if we can shortcut, then it's an infinite loop,
                // so shortcutting it would be pointless.
                if !conf.state[&var].is_zero() {
                    conf.push(WhileDo(var, block.clone()));
                    conf.push_all(&block);
                }
            }
        }
    }

    // I really want to name this "try_loophole".
    fn try_loop_shortcut(&self, outer_amount: &Natural, conf: &mut Configuration) -> bool {
        use PloopStatement::*;
        match self {
            AddToInto(amount, src, dst) => {
                if src == dst {
                    conf.state[&dst] += outer_amount * amount;
                } else {
                    // `outer_amount` is irrelevant.
                    // This can happen when the code is, for example,
                    // determining whether something is non-zero.
                    conf.state[&dst] = conf.state[&src].clone() + amount;
                }
                true
            }
            SubtractFromInto(amount, src, dst) => {
                if src == dst {
                    let actual_amount: Natural = amount * outer_amount;
                    let dst_var = &mut conf.state[&dst];
                    // TODO: Why doesn't this work without a cast?
                    // if dst_var <= &actual_amount {
                    if (dst_var as &Natural) <= &actual_amount {
                        dst_var.set_zero();
                    } else {
                        //dst_var -= (&actual_amount as &Natural);
                        dst_var.sub_assign(&actual_amount as &Natural);
                    }
                } else {
                    // `outer_amount` is irrelevant.
                    // Why write code like that? Whatever.
                    conf.state[&dst] = conf.state[&src].clone() - amount;
                }
                true
            }
            LoopDo(var, _block) => {
                if conf[var].is_zero() {
                    // The inner loop is a no-op. Executing a no-op `amount`
                    // many times is still a no-op so we can skip this.
                    true
                    // I know this can be written differently.
                    // Writing it this way stresses that there could be a `else if`,
                    // and that doing nothing here is actually non-trivial.
                } else {
                    // TODO: Maybe this can be improved?
                    false
                }
            }
            DoTimes(amount, block) => {
                // Nice!
                block.try_loop_shortcut(&(outer_amount * amount), conf)
            }
            WhileDo(_var, _block) => false, // Hard
        }
    }
}

// TODO: Consider a splay tree, as accesses are going to be repetitive.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Environment(BTreeMap<VarIdent, Natural>);

impl Environment {
    pub fn new(input: Natural) -> Environment {
        let mut map = BTreeMap::new();
        map.insert(VarIdent(0), input);
        Environment(map)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&VarIdent, &Natural)> {
        self.0.iter()
    }
}

impl<'a> IntoIterator for &'a Environment {
    type Item = (&'a VarIdent, &'a Natural);

    // Ugh.
    type IntoIter = <&'a BTreeMap<VarIdent, Natural> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl Index<&VarIdent> for Environment {
    type Output = Natural;

    fn index(&self, varid: &VarIdent) -> &Self::Output {
        self.0.get(varid).unwrap_or(&THE_ZERO)
    }
}

impl IndexMut<&VarIdent> for Environment {
    fn index_mut(&mut self, varid: &VarIdent) -> &mut Self::Output {
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
        let mut statements: Vec<PloopStatement> = (*block.0).clone();
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
        }
    }
}

impl Deref for Configuration {
    type Target = Environment;

    fn deref(&self) -> &Environment {
        &self.state
    }
}

#[cfg(test)]
mod test {
    use super::super::nat;
    use super::*;

    #[derive(Debug)]
    enum Halts {
        OnOrBefore(u32),
        NotEvenAfter(u32),
    }

    impl Halts {
        fn satisfies(&self, requirement: &Halts) -> bool {
            use Halts::*;
            match (self, requirement) {
                (NotEvenAfter(act), NotEvenAfter(exp)) => act >= exp,
                (OnOrBefore(act), NotEvenAfter(exp)) => act > exp,
                (NotEvenAfter(act), OnOrBefore(exp)) => {
                    // Image we require `OnOrBefore(10)`, and we only know
                    // `NotEvenAfter(5)`. Then we don't have enough information,
                    // because for some reason execution was halted too early.
                    assert!(act >= exp);
                    false
                }
                (OnOrBefore(act), OnOrBefore(exp)) => act <= exp,
            }
        }
    }

    fn observe(code: &str, input: Environment, max_steps: u32) -> (Halts, Configuration) {
        let program = PloopBlock::try_from(code).expect("bad code");
        let mut conf = Configuration::from_state(input, &program);
        println!("Initial configuration: {:?}", conf);

        let mut actual_steps = 0;
        for i in 0..max_steps {
            if !conf.is_completed() {
                actual_steps += 1;
                conf.step();
                println!("Configuration after step #{}: {:?}", i, conf);
            } else {
                break;
            }
        }
        let halts = if conf.is_completed() {
            println!("Done (halted)");
            Halts::OnOrBefore(actual_steps)
        } else {
            println!("Done (stopped)");
            Halts::NotEvenAfter(actual_steps)
        };

        (halts, conf)
    }

    fn run_test(code: &str, input: Environment, exp_halts: Halts, exp_env: Vec<(u32, u64)>) {
        let max_steps = match exp_halts {
            Halts::NotEvenAfter(n) => n + 5,
            // Make off-by-one-errors more obvious:
            Halts::OnOrBefore(n) => n + 5,
        };

        let (act_halts, conf) = observe(code, input, max_steps);
        assert!(act_halts.satisfies(&exp_halts));
        let act_env = conf.deref();

        let mut mismatch = false;
        for (key, exp_value) in exp_env.iter() {
            let key = VarIdent(*key);
            let exp_value = nat(*exp_value);
            let act_value = &act_env[&key];
            if &exp_value != act_value {
                println!(
                    "MISMATCH for {:?}: expected {}, but was {}!",
                    key, exp_value, act_value
                );
                mismatch = true;
            }
        }
        assert!(!mismatch);
    }

    fn env_from(pairs: Vec<(u32, u64)>) -> Environment {
        assert_eq!(0, pairs[0].0, "Must start with (0, _): {:?}", pairs);
        let mut env = Environment::new(nat(pairs[0].1));
        for (key, value) in pairs.iter() {
            let ekey = VarIdent(*key);
            let evalue = nat(*value);
            env[&ekey] = evalue;
        }

        env
    }

    #[test]
    fn test_empty() {
        run_test(
            "
            ",
            Environment::new(nat(1337)),
            Halts::OnOrBefore(0),
            vec![(0, 1337)],
        );
    }

    #[test]
    fn test_assignments() {
        run_test(
            "
                add 0x1 to v0 into v0
                add 0x2 to v1 into v1
                add 0x4 to v2 into v2
                add 0x40 to v0 into v10
                add 0xF0 to v1 into v11
                add 0xFC to v2 into v12
                add 0x100 to v12 into v22
                add 0x100 to v22 into v22
                add 0x100 to v22 into v22
            ",
            Environment::new(nat(0x10)),
            Halts::OnOrBefore(9),
            vec![
                (0, 0x11),
                (1, 0x2),
                (2, 0x4),
                (10, 0x51),
                (11, 0xF2),
                (12, 0x100),
                (22, 0x400),
            ],
        );
    }

    #[test]
    fn test_simple() {
        let code = "
            subtract 0x5 from v0 into v1
            add 0x5 to v1 into v1
            add 0x0 to v2 into v0
            loop v1 do
                add 0x2 to v0 into v0
            end
            # This implements:
            # x1 = min(5, x0)
            # x0 = 2 * x1
        ";

        run_test(
            code,
            Environment::new(nat(2)),
            Halts::OnOrBefore(15),
            vec![(0, 10), (1, 5), (2, 0)],
        );

        run_test(
            code,
            Environment::new(nat(7)),
            Halts::OnOrBefore(19),
            vec![(0, 14), (1, 7), (2, 0)],
        );
    }

    #[test]
    fn test_empty_dotimes() {
        run_test(
            "
                do 0x0 times
                end
            ",
            Environment::new(nat(42)),
            Halts::OnOrBefore(1),
            vec![(0, 42), (1337, 0)],
        );
    }

    #[test]
    fn test_hanging_while() {
        run_test(
            "
                while v0 do
                    add 0x1 to v0 into v1
                end
            ",
            Environment::new(nat(1)),
            Halts::NotEvenAfter(999),
            vec![(0, 1)],
        );
    }

    #[test]
    fn test_stopping_while() {
        run_test(
            "
                while v0 do
                    subtract 0x1 from v0 into v0
                end
            ",
            Environment::new(nat(5)),
            Halts::OnOrBefore(11),
            vec![(0, 0)],
        );
    }

    #[test]
    fn test_loopy_3() {
        run_test(
            "
                loop v0 do # v0 → v0 * (2 ** v0)
                    loop v0 do # v0 → 2*v0
                        add 0x1 to v0 into v0
                    end
                end
            ",
            Environment::new(nat(3)),
            Halts::OnOrBefore(24 * 3),
            vec![(0, 24)],
        );
    }

    #[test]
    fn test_loopy_4() {
        run_test(
            "
                loop v0 do # v0 → v0 * (2 ** v0)
                    loop v0 do # v0 → 2*v0
                        add 0x1 to v0 into v0
                    end
                end
            ",
            Environment::new(nat(4)),
            Halts::OnOrBefore(64 * 3),
            vec![(0, 64)],
        );
    }

    #[test]
    fn test_loopy_5() {
        run_test(
            "
                loop v0 do # v0 → v0 * (2 ** v0)
                    loop v0 do # v0 → 2*v0
                        add 0x1 to v0 into v0
                    end
                end
            ",
            Environment::new(nat(5)),
            Halts::OnOrBefore(160 * 3),
            vec![(0, 160)],
        );
    }

    #[test]
    fn test_looopy_2() {
        run_test(
            "
                loop v0 do # v0 → ???
                # 0
                # 1 → 2
                # 2 → 8 → 2048
                # 3 → 24 → 402653184 → Oh boy!
                    loop v0 do # v0 → v0 * (2 ** v0)
                        loop v0 do # v0 → 2*v0
                            add 0x1 to v0 into v0
                        end
                    end
                end
            ",
            Environment::new(nat(2)),
            Halts::OnOrBefore(2048 * 3),
            vec![(0, 2048)],
        );
    }

    #[test]
    fn test_looopy_3() {
        run_test(
            "
                loop v0 do # v0 → ???
                # 0
                # 1 → 2
                # 2 → 8 → 2048
                # 3 → 24 → 402653184 → Oh boy!
                    loop v0 do # v0 → v0 * (2 ** v0)
                        loop v0 do # v0 → 2*v0
                            add 0x1 to v0 into v0
                        end
                    end
                end
            ",
            Environment::new(nat(3)),
            Halts::NotEvenAfter(10_000),
            // We can't know for sure where exactly the interruption will happen
            vec![],
        );
    }

    #[test]
    fn test_manual_add() {
        let code = "
            # input is v0 and v1, output is v2
            add 0x0 to v0 into v2
            loop v1 do
                add 0x1 to v2 into v2
            end
        ";

        run_test(
            code,
            env_from(vec![(0, 0), (1, 0)]),
            Halts::OnOrBefore(4),
            vec![(0, 0), (1, 0), (2, 0)],
        );

        run_test(
            code,
            env_from(vec![(0, 10), (1, 10)]),
            Halts::OnOrBefore(30),
            vec![(0, 10), (1, 10), (2, 20)],
        );

        run_test(
            code,
            env_from(vec![(0, 42), (1, 13)]),
            Halts::OnOrBefore(30),
            vec![(0, 42), (1, 13), (2, 55)],
        );

        run_test(
            code,
            env_from(vec![(0, 5), (1, 48)]),
            Halts::OnOrBefore(100),
            vec![(0, 5), (1, 48), (2, 53)],
        );
    }

    #[test]
    fn test_manual_sub() {
        let code = "
            # input is v0 and v1, output is v2
            add 0x0 to v0 into v2
            loop v1 do
                subtract 0x1 from v2 into v2
            end
        ";

        run_test(
            code,
            env_from(vec![(0, 0), (1, 0), (2, 99)]),
            Halts::OnOrBefore(4),
            vec![(0, 0), (1, 0), (2, 0)],
        );

        run_test(
            code,
            env_from(vec![(0, 10), (1, 10), (2, 1337)]),
            Halts::OnOrBefore(30),
            vec![(0, 10), (1, 10), (2, 0)],
        );

        run_test(
            code,
            env_from(vec![(0, 42), (1, 13), (2, 99)]),
            Halts::OnOrBefore(30),
            vec![(0, 42), (1, 13), (2, 29)],
        );

        run_test(
            code,
            env_from(vec![(0, 5), (1, 48), (2, 123456)]),
            Halts::OnOrBefore(100),
            vec![(0, 5), (1, 48), (2, 0)],
        );

        run_test(
            code,
            env_from(vec![(0, 0), (1, 3), (2, 99)]),
            Halts::OnOrBefore(10),
            vec![(0, 0), (1, 3), (2, 0)],
        );

        run_test(
            code,
            env_from(vec![(0, 3), (1, 0), (2, 2020)]),
            Halts::OnOrBefore(5),
            vec![(0, 3), (1, 0), (2, 3)],
        );
    }

    #[test]
    fn test_manual_div() {
        let code = "
            # input is v0 and v1, output is v2
            # Note: We don't care about v1 == 1
            # ---
            # We would like a 'set to zero' operation, but there is none.
            add 0x0 to v1 into _zero
            loop _zero do
                subtract 0x1 from _zero into _zero
            end
            add 0x0 to _zero into v2
            add 0x1 to _zero into _unsure
            add 0x1 to v0 into _overremainder
            # Invariants:
            # _zero == 0
            # (_unsure == 0) implies v2 * v1 + _overremainder == v0 + 1
            # (_unsure == 1) implies v2 == floor(v0/v1)
            loop v0 do
                loop _unsure do
                    # Compute next _overremainder
                    loop v1 do
                        subtract 0x1 from _overremainder into _overremainder
                    end
                    # If _overremainder is still larger than 0,
                    # then the current remainder was >= v1 (_overremainder > v1),
                    # so v2 wasn't the answer.
                    add 0x0 to _zero into _unsure
                    loop _overremainder do
                        add 0x1 to _zero into _unsure
                    end
                    # And if v2 wasn't the answer, try v2+1 next:
                    loop _unsure do
                        add 0x1 to v2 into v2
                    end
                end
            end
        ";

        run_test(
            code,
            env_from(vec![(0, 0), (1, 1)]),
            Halts::OnOrBefore(20),
            vec![(0, 0), (1, 1), (2, 0)],
        );

        run_test(
            code,
            env_from(vec![(0, 0), (1, 2)]),
            Halts::OnOrBefore(20),
            vec![(0, 0), (1, 2), (2, 0)],
        );

        run_test(
            code,
            env_from(vec![(0, 1), (1, 10), (2, 99)]),
            Halts::OnOrBefore(99),
            vec![(0, 1), (1, 10), (2, 0)],
        );

        run_test(
            code,
            env_from(vec![(0, 9), (1, 10)]),
            Halts::OnOrBefore(99),
            vec![(0, 9), (1, 10), (2, 0)],
        );

        run_test(
            code,
            env_from(vec![(0, 10), (1, 10)]),
            Halts::OnOrBefore(300),
            vec![(0, 10), (1, 10), (2, 1)],
        );

        run_test(
            code,
            env_from(vec![(0, 11), (1, 10)]),
            Halts::OnOrBefore(300),
            vec![(0, 11), (1, 10), (2, 1)],
        );

        run_test(
            code,
            env_from(vec![(0, 19), (1, 10)]),
            Halts::OnOrBefore(300),
            vec![(0, 19), (1, 10), (2, 1)],
        );

        run_test(
            code,
            env_from(vec![(0, 20), (1, 10)]),
            Halts::OnOrBefore(300),
            vec![(0, 20), (1, 10), (2, 2)],
        );

        run_test(
            code,
            env_from(vec![(0, 21), (1, 10)]),
            Halts::OnOrBefore(300),
            vec![(0, 21), (1, 10), (2, 2)],
        );

        run_test(
            code,
            env_from(vec![(0, 255), (1, 256)]),
            Halts::OnOrBefore(196608),
            vec![(0, 255), (1, 256), (2, 0)],
        );

        run_test(
            code,
            env_from(vec![(0, 256), (1, 256)]),
            Halts::OnOrBefore(196608),
            vec![(0, 256), (1, 256), (2, 1)],
        );

        run_test(
            code,
            env_from(vec![(0, 257), (1, 256)]),
            Halts::OnOrBefore(200),
            vec![(0, 257), (1, 256), (2, 1)],
        );
    }

    #[test]
    fn test_manual_div256() {
        let code = "
            # input is v0, output is v1 (DIFFERENT!)
            # ---
            # We would like a 'set to zero' operation, but there is none.
            subtract 0xFFFFFFFF from v0 into _zero
            loop _zero do
                subtract 0x1 from _zero into _zero
            end
            add 0x0 to _zero into v1
            add 0x1 to _zero into _unsure
            add 0x1 to v0 into _overremainder
            # Invariants:
            # _zero == 0
            # (_unsure == 0) implies v1 * 256 + _overremainder == v0 + 1
            # (_unsure == 1) implies v1 == floor(v0/256)
            loop v0 do
                loop _unsure do
                    # Compute next _overremainder
                    subtract 0x100 from _overremainder into _overremainder
                    # If _overremainder is still larger than 0,
                    # then the current remainder was >= 256 (_overremainder > 257),
                    # so v1 wasn't the answer.
                    add 0x0 to _zero into _unsure
                    loop _overremainder do
                        add 0x1 to _zero into _unsure
                    end
                    # And if v1 wasn't the answer, try v1+1 next:
                    loop _unsure do
                        add 0x1 to v1 into v1
                    end
                end
            end
        ";

        run_test(
            code,
            env_from(vec![(0, 0), (1, 1337)]),
            Halts::OnOrBefore(20),
            vec![(0, 0), (1, 0)],
        );

        run_test(
            code,
            env_from(vec![(0, 1), (1, 1337)]),
            Halts::OnOrBefore(20),
            vec![(0, 1), (1, 0)],
        );

        run_test(
            code,
            env_from(vec![(0, 2), (1, 1337)]),
            Halts::OnOrBefore(21),
            vec![(0, 2), (1, 0)],
        );

        run_test(
            code,
            env_from(vec![(0, 254), (1, 42), (2, 422)]),
            Halts::OnOrBefore(200),
            vec![(0, 254), (1, 0)],
        );

        run_test(
            code,
            env_from(vec![(0, 255), (1, 42), (2, 422)]),
            Halts::OnOrBefore(200),
            vec![(0, 255), (1, 0)],
        );

        run_test(
            code,
            env_from(vec![(0, 256), (1, 42), (2, 422)]),
            Halts::OnOrBefore(200),
            vec![(0, 256), (1, 1)],
        );

        run_test(
            code,
            env_from(vec![(0, 257), (1, 42), (2, 422)]),
            Halts::OnOrBefore(200),
            vec![(0, 257), (1, 1)],
        );

        run_test(
            code,
            env_from(vec![(0, 511), (1, 42), (2, 422)]),
            Halts::OnOrBefore(200),
            vec![(0, 511), (1, 1)],
        );

        run_test(
            code,
            env_from(vec![(0, 512), (1, 42), (2, 422)]),
            Halts::OnOrBefore(200),
            vec![(0, 512), (1, 2)],
        );

        run_test(
            code,
            env_from(vec![(0, 1023), (1, 42), (2, 422)]),
            Halts::OnOrBefore(200),
            vec![(0, 1023), (1, 3)],
        );

        run_test(
            code,
            env_from(vec![(0, 1024), (1, 42), (2, 422)]),
            Halts::OnOrBefore(200),
            vec![(0, 1024), (1, 4)],
        );
    }

    #[test]
    fn test_manual_div256_large() {
        let code = "
            # input is v0, output is v1 (DIFFERENT!)
            # ---
            # We would like a 'set to zero' operation, but there is none.
            subtract 0xFFFFFFFF from v0 into _zero
            loop _zero do
                subtract 0x1 from _zero into _zero
            end
            add 0x0 to _zero into v1
            add 0x1 to _zero into _unsure
            add 0x1 to v0 into _overremainder
            # Invariants:
            # _zero == 0
            # (_unsure == 0) implies v1 * 256 + _overremainder == v0 + 1
            # (_unsure == 1) implies v1 == floor(v0/256)
            loop v0 do
                loop _unsure do
                    # Compute next _overremainder
                    subtract 0x100 from _overremainder into _overremainder
                    # If _overremainder is still larger than 0,
                    # then the current remainder was >= 256 (_overremainder > 257),
                    # so v1 wasn't the answer.
                    add 0x0 to _zero into _unsure
                    loop _overremainder do
                        add 0x1 to _zero into _unsure
                    end
                    # And if v1 wasn't the answer, try v1+1 next:
                    loop _unsure do
                        add 0x1 to v1 into v1
                    end
                end
            end
        ";

        run_test(
            code,
            env_from(vec![(0, 2559)]),
            Halts::OnOrBefore(200),
            vec![(0, 2559), (1, 9)],
        );

        run_test(
            code,
            env_from(vec![(0, 2560)]),
            Halts::OnOrBefore(200),
            vec![(0, 2560), (1, 10)],
        );
    }
}
