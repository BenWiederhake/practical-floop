use std::collections::BTreeMap;
use std::convert::TryFrom;
use std::fmt::{self, Debug, Display, Formatter};
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

impl Display for VarIdent {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "v{}", self.0)
    }
}

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

    pub fn try_from_iter_verbose<I: Iterator<Item = Result<char>>>(iter: I) -> Result<(PloopBlock, String)> {
        let token_iter = Tokenizer::new(iter);
        let parsed_block = ParseBlock::try_from_iter(token_iter)?;
        Ok(PloopBlock::from_verbose(&parsed_block))
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

    fn statements(&self) -> &[PloopStatement] {
        &**self.0
    }

    fn from_verbose(block: &ParseBlock) -> (PloopBlock, String) {
        let mut r = Resolver::new();
        r.reserve_static(block);
        (r.resolve_remaining(block), r.make_table())
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
        PloopBlock::try_from_iter(string.chars().map(Ok))
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
                let amount = conf.state[&var].clone();
                if !amount.is_zero() {
                    conf.push(DoTimes(amount, block));
                }
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
                    if !amount.is_zero() {
                        conf.push(DoTimes(amount, block.clone()));
                    }
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
                    // TODO: Maybe this case can be improved?
                    // Especially in case of multiplication
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
#[derive(Clone, PartialEq, Eq)]
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

impl Debug for Environment {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_map().entries(self.0.iter().map(|(k, v)|
            (format!("{}", k), format!("0x{:X}", v))
        )).finish()
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

#[derive(Clone)]
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

pub trait PrettyPrint {
    fn fmt(&self, level: usize, f: &mut Formatter) -> fmt::Result;
}

impl PrettyPrint for PloopBlock {
    fn fmt(&self, level: usize, f: &mut Formatter) -> fmt::Result {
        for stmt in self.statements() {
            PrettyPrint::fmt(stmt, level, f)?;
        }
        Ok(())
    }
}

impl PrettyPrint for PloopStatement {
    fn fmt(&self, level: usize, f: &mut Formatter) -> fmt::Result {
        use PloopStatement::*;
        let levelindent = "    ".to_string().repeat(level);
        match self {
            AddToInto(amount, src, dst) => {
                write!(f, "{}add 0x{:X} to {} into {}\n",
                    levelindent, amount, src, dst)
            }
            SubtractFromInto(amount, src, dst) => {
                write!(f, "{}subtract 0x{:X} from {} into {}\n",
                    levelindent, amount, src, dst)
            }
            LoopDo(var, block) => {
                write!(f, "{}loop {} do\n",
                    levelindent, var)?;
                PrettyPrint::fmt(block, level + 1, f)?;
                write!(f, "{}end\n", levelindent)
            }
            DoTimes(amount, block) => {
                write!(f, "{}do 0x{:X} times\n",
                    levelindent, amount)?;
                PrettyPrint::fmt(block, level + 1, f)?;
                write!(f, "{}end\n", levelindent)
            }
            WhileDo(var, block) => {
                write!(f, "{}while {} times\n",
                    levelindent, var)?;
                PrettyPrint::fmt(block, level + 1, f)?;
                write!(f, "{}end\n", levelindent)
            }
        }
    }
}

impl Debug for Configuration {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str("Configuration {\n")?;
        write!(f, "    state: {:?}\n", self.state)?;
        write!(f, "    stack: [\n")?;
        for stmt in &self.stack {
            PrettyPrint::fmt(stmt, 2, f)?;
            write!(f, "    ,\n")?;
        }
        write!(f, "    ]\n")?;
        f.write_str("}")
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
        let (program, table) = PloopBlock::try_from_iter_verbose(code.chars().map(Ok)).expect("bad code");
        let mut conf = Configuration::from_state(input, &program);
        println!("Initial configuration: {:?}", conf);
        println!("Table is: {}", table);

        let mut actual_steps = 0;
        for _ in 0..max_steps {
            if !conf.is_completed() {
                actual_steps += 1;
                conf.step();
            } else {
                break;
            }
        }
        println!("Configuration after step #{}: {:?}", actual_steps, conf);
        let halts = if conf.is_completed() {
            println!("Done (halted)");
            Halts::OnOrBefore(actual_steps)
        } else {
            println!("Done (stopped)");
            Halts::NotEvenAfter(actual_steps)
        };
        println!("Table is (still): {}", table);

        (halts, conf)
    }

    fn run_test(code: &str, input: Environment, exp_halts: Halts, exp_env: Vec<(u32, u64)>) {
        let max_steps = match exp_halts {
            Halts::NotEvenAfter(n) => n + 5,
            // Make off-by-one-errors more obvious:
            Halts::OnOrBefore(n) => n * 2 + 5,
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
    fn test_calc_add() {
        run_test(
            "calc + 0x0 0x0 into v0",
            env_from(vec![(0, 42)]),
            Halts::OnOrBefore(10),
            vec![(0, 0)],
        );

        run_test(
            "calc + + 0x0 0x0 + 0x0 0x0 into v0",
            env_from(vec![(0, 42)]),
            Halts::OnOrBefore(20),
            vec![(0, 0)],
        );

        run_test(
            "calc + - 0x2 0x1 - 0x4 0x3 into v13",
            env_from(vec![(0, 1337)]),
            Halts::OnOrBefore(20),
            vec![(0, 1337), (13, 2)],
        );

        run_test(
            "calc + 0xa 0xa into v2",
            env_from(vec![(0, 1337)]),
            Halts::OnOrBefore(20),
            vec![(0, 1337), (2, 20)],
        );

        run_test(
            "calc + v1 v3 into v2",
            env_from(vec![(0, 1337), (1, 42), (3, 13)]),
            Halts::OnOrBefore(20),
            vec![(0, 1337), (1, 42), (3, 13), (2, 55)],
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
    fn test_calc_sub() {
        let code = "calc - v0 v1 into v2";

        run_test(
            code,
            env_from(vec![(0, 0), (1, 0), (2, 99)]),
            Halts::OnOrBefore(10),
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
            Halts::OnOrBefore(10),
            vec![(0, 3), (1, 0), (2, 3)],
        );
    }

    #[test]
    fn test_manual_div() {
        let code = "
            # input is v0 and v1, output is v2
            # Note: We don't care about v1 == 0
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
            Halts::OnOrBefore(200),
            vec![(0, 255), (1, 256), (2, 0)],
        );

        run_test(
            code,
            env_from(vec![(0, 256), (1, 256)]),
            Halts::OnOrBefore(200),
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

    #[test]
    fn test_manual_mul() {
        let code = "
            # input is v0 and v1, output is v2
            add 0x0 to _zero into v2
            loop v0 do
                loop v1 do
                    add 0x1 to v2 into v2
                end
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
            Halts::OnOrBefore(35),
            vec![(0, 10), (1, 10), (2, 100)],
        );

        run_test(
            code,
            env_from(vec![(0, 1), (1, 13), (2, 99)]),
            Halts::OnOrBefore(10),
            vec![(0, 1), (1, 13), (2, 13)],
        );

        run_test(
            code,
            env_from(vec![(0, 5), (1, 1), (2, 123456)]),
            Halts::OnOrBefore(20),
            vec![(0, 5), (1, 1), (2, 5)],
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
            Halts::OnOrBefore(10),
            vec![(0, 3), (1, 0), (2, 0)],
        );
    }

    #[test]
    fn test_calc_mul() {
        let code = "calc * v0 v1 into v2";

        run_test(
            code,
            env_from(vec![(0, 0), (1, 0), (2, 99)]),
            Halts::OnOrBefore(10),
            vec![(0, 0), (1, 0), (2, 0)],
        );

        run_test(
            code,
            env_from(vec![(0, 10), (1, 10), (2, 1337)]),
            Halts::OnOrBefore(40),
            vec![(0, 10), (1, 10), (2, 100)],
        );

        run_test(
            code,
            env_from(vec![(0, 1), (1, 13), (2, 99)]),
            Halts::OnOrBefore(20),
            vec![(0, 1), (1, 13), (2, 13)],
        );

        run_test(
            code,
            env_from(vec![(0, 5), (1, 1), (2, 123456)]),
            Halts::OnOrBefore(30),
            vec![(0, 5), (1, 1), (2, 5)],
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
            Halts::OnOrBefore(10),
            vec![(0, 3), (1, 0), (2, 0)],
        );

        run_test(
            code,
            env_from(vec![(0, 2), (1, 256), (2, 2020)]),
            Halts::OnOrBefore(20),
            vec![(0, 2), (1, 256), (2, 512)],
        );
    }

    #[test]
    fn test_manual_mod() {
        let code = "
            # input is v0 and v1, output is v2
            # Note: We don't care about v1 == 0
            # Note: Mostly copied from 'manual_div'. This can probably be improved.
            # ---
            # We would like a 'set to zero' operation, but there is none.
            add 0x0 to v1 into _zero
            loop _zero do
                subtract 0x1 from _zero into _zero
            end
            add 0x0 to _zero into v2
            add 0x1 to _zero into _unsure
            add 0x1 to v0 into _overremainder
            add 0x0 to _overremainder into _oldoverremainder
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
                        add 0x0 to _overremainder into _oldoverremainder
                    end
                end
            end
            subtract 0x1 from _oldoverremainder into v2
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
            vec![(0, 1), (1, 10), (2, 1)],
        );

        run_test(
            code,
            env_from(vec![(0, 9), (1, 10)]),
            Halts::OnOrBefore(99),
            vec![(0, 9), (1, 10), (2, 9)],
        );

        run_test(
            code,
            env_from(vec![(0, 10), (1, 10)]),
            Halts::OnOrBefore(300),
            vec![(0, 10), (1, 10), (2, 0)],
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
            vec![(0, 19), (1, 10), (2, 9)],
        );

        run_test(
            code,
            env_from(vec![(0, 20), (1, 10)]),
            Halts::OnOrBefore(300),
            vec![(0, 20), (1, 10), (2, 0)],
        );

        run_test(
            code,
            env_from(vec![(0, 21), (1, 10)]),
            Halts::OnOrBefore(300),
            vec![(0, 21), (1, 10), (2, 1)],
        );

        run_test(
            code,
            env_from(vec![(0, 255), (1, 256)]),
            Halts::OnOrBefore(200),
            vec![(0, 255), (1, 256), (2, 255)],
        );

        run_test(
            code,
            env_from(vec![(0, 256), (1, 256)]),
            Halts::OnOrBefore(200),
            vec![(0, 256), (1, 256), (2, 0)],
        );

        run_test(
            code,
            env_from(vec![(0, 257), (1, 256)]),
            Halts::OnOrBefore(200),
            vec![(0, 257), (1, 256), (2, 1)],
        );
    }

    #[test]
    fn test_manual_cmp() {
        let code = "
            # input is v0 and v1, output is v2
            add 0x0 to v0 into _v0
            add 0x0 to v1 into _v1
            add 0x2 to v0 into _rounds
            add 0x1 to _zero into _bothnonzero
            loop _rounds do
                loop _bothnonzero do
                    add 0x0 to _zero into _v0nonzero
                    loop _v0 do
                        add 0x1 to _zero into _v0nonzero
                    end
                    add 0x0 to _zero into _v1nonzero
                    loop _v1 do
                        add 0x1 to _zero into _v1nonzero
                    end
                    add 0x0 to _zero into _bothnonzero
                    loop _v0nonzero do
                        loop _v1nonzero do
                            add 0x1 to _zero into _bothnonzero
                        end
                    end
                    loop _bothnonzero do
                        subtract 0x1 from _v0 into _v0
                        subtract 0x1 from _v1 into _v1
                    end
                end
            end
            # assert ! _bothnonzero
            # or in other words:
            # assert _v0 == 0 or _v1 == 0
            # also:
            # assert ! ( _v0nonzero && _v1nonzero )
            add 0x1 to _zero into v2
            loop _v0nonzero do
                subtract 0x1 from v2 into v2
            end
            loop _v1nonzero do
                add 0x1 to v2 into v2
            end
        ";

        run_test(
            code,
            env_from(vec![(0, 0), (1, 0), (2, 99)]),
            Halts::OnOrBefore(30),
            vec![(0, 0), (1, 0), (2, 1)],
        );

        run_test(
            code,
            env_from(vec![(0, 1), (1, 0), (2, 99)]),
            Halts::OnOrBefore(30),
            vec![(0, 1), (1, 0), (2, 0)],
        );

        run_test(
            code,
            env_from(vec![(0, 0), (1, 1), (2, 99)]),
            Halts::OnOrBefore(30),
            vec![(0, 0), (1, 1), (2, 2)],
        );

        run_test(
            code,
            env_from(vec![(0, 10), (1, 10), (2, 1337)]),
            Halts::OnOrBefore(250),
            vec![(0, 10), (1, 10), (2, 1)],
        );

        run_test(
            code,
            env_from(vec![(0, 1), (1, 13), (2, 99)]),
            Halts::OnOrBefore(50),
            vec![(0, 1), (1, 13), (2, 2)],
        );

        run_test(
            code,
            env_from(vec![(0, 5), (1, 1), (2, 123456)]),
            Halts::OnOrBefore(50),
            vec![(0, 5), (1, 1), (2, 0)],
        );

        run_test(
            code,
            env_from(vec![(0, 0), (1, 3), (2, 99)]),
            Halts::OnOrBefore(30),
            vec![(0, 0), (1, 3), (2, 2)],
        );

        run_test(
            code,
            env_from(vec![(0, 3), (1, 0), (2, 2020)]),
            Halts::OnOrBefore(30),
            vec![(0, 3), (1, 0), (2, 0)],
        );
    }

    fn cmp_helper(args: [u64; 2], results: [u64; 7]) {
        for (i, op_str) in ["?=", "<>", "==", "<", "<=", ">", ">="].iter().enumerate() {
            run_test(
                &format!("calc {} v0 v1 into v2", op_str),
                env_from(vec![(0, args[0]), (1, args[1]), (2, 99), (99, i as u64)]),
                Halts::OnOrBefore(25),
                vec![(0, args[0]), (1, args[1]), (2, results[i])],
            );
        }
    }

    #[test]
    fn test_calc_cmp() {
        // Second argument order: Cmp, Ne, Eq, Lt, Le, Gt, Ge
        cmp_helper([0, 0], [1, 0, 1, 0, 1, 0, 1]);
        cmp_helper([1, 0], [2, 1, 0, 0, 0, 1, 1]);
        cmp_helper([0, 1], [0, 1, 0, 1, 1, 0, 0]);
        cmp_helper([1, 1], [1, 0, 1, 0, 1, 0, 1]);
        cmp_helper([9, 9], [1, 0, 1, 0, 1, 0, 1]);
        cmp_helper([5, 9], [0, 1, 0, 1, 1, 0, 0]);
        cmp_helper([5, 1], [2, 1, 0, 0, 0, 1, 1]);
        cmp_helper([0, 3], [0, 1, 0, 1, 1, 0, 0]);
        cmp_helper([3, 0], [2, 1, 0, 0, 0, 1, 1]);
    }

    #[test]
    fn test_calc_not() {
        let code = "calc ! v0 into v2";

        run_test(
            code,
            env_from(vec![(0, 0), (2, 99)]),
            Halts::OnOrBefore(6),
            vec![(0, 0), (2, 1)],
        );

        run_test(
            code,
            env_from(vec![(0, 1), (1, 10), (2, 1337)]),
            Halts::OnOrBefore(6),
            vec![(0, 1), (2, 0)],
        );

        run_test(
            code,
            env_from(vec![(0, 1), (1, 0), (2, 99)]),
            Halts::OnOrBefore(6),
            vec![(0, 1), (2, 0)],
        );

        run_test(
            code,
            env_from(vec![(0, 999), (1, 1), (2, 123456)]),
            Halts::OnOrBefore(6),
            vec![(0, 999), (2, 0)],
        );
    }

    fn logbin_helper(args: [u64; 2], results: [u64; 2]) {
        for (i, op_str) in ["&&", "||"].iter().enumerate() {
            run_test(
                &format!("calc {} v0 v1 into v2", op_str),
                env_from(vec![(0, args[0]), (1, args[1]), (2, 99), (99, i as u64)]),
                Halts::OnOrBefore(15),
                vec![(0, args[0]), (1, args[1]), (2, results[i])],
            );
        }
    }

    #[test]
    fn test_calc_logbin() {
        // Second argument order: &&, ||

        logbin_helper([0, 0], [0, 0]);
        logbin_helper([0, 1], [0, 1]);
        logbin_helper([1, 0], [0, 1]);
        logbin_helper([1, 1], [1, 1]);

        logbin_helper([0, 9], [0, 1]);
        logbin_helper([9, 0], [0, 1]);
        logbin_helper([9, 9], [1, 1]);

        logbin_helper([18, 33], [1, 1]);
        logbin_helper([42, 23], [1, 1]);
    }

    #[test]
    fn test_if_then() {
        let code = "if v0 do add 0x1 to v1 into v1 end";

        run_test(
            code,
            env_from(vec![(0, 0), (1, 5)]),
            Halts::OnOrBefore(20),
            vec![(0, 0), (1, 5)],
        );

        run_test(
            code,
            env_from(vec![(0, 1), (1, 5)]),
            Halts::OnOrBefore(20),
            vec![(0, 1), (1, 6)],
        );

        run_test(
            code,
            env_from(vec![(0, 9), (1, 5)]),
            Halts::OnOrBefore(20),
            vec![(0, 9), (1, 6)],
        );

        run_test(
            code,
            env_from(vec![(0, 0), (1, 23)]),
            Halts::OnOrBefore(20),
            vec![(0, 0), (1, 23)],
        );

        run_test(
            code,
            env_from(vec![(0, 9), (1, 23)]),
            Halts::OnOrBefore(20),
            vec![(0, 9), (1, 24)],
        );
    }

    #[test]
    fn test_if_then_recursion() {
        let code = "
            if v0 do
                add 0x1 to v10 into v10
                if v1 do
                    add 0x1 to v11 into v11
                end
            end
        ";

        run_test(
            code,
            env_from(vec![(0, 0), (1, 0), (10, 34), (11, 56)]),
            Halts::OnOrBefore(30),
            vec![(0, 0), (1, 0), (10, 34), (11, 56)],
        );

        run_test(
            code,
            env_from(vec![(0, 0), (1, 12), (10, 34), (11, 56)]),
            Halts::OnOrBefore(30),
            vec![(0, 0), (1, 12), (10, 34), (11, 56)],
        );

        run_test(
            code,
            env_from(vec![(0, 7), (1, 0), (10, 34), (11, 56)]),
            Halts::OnOrBefore(30),
            vec![(0, 7), (1, 0), (10, 35), (11, 56)],
        );

        run_test(
            code,
            env_from(vec![(0, 7), (1, 7), (10, 34), (11, 56)]),
            Halts::OnOrBefore(30),
            vec![(0, 7), (1, 7), (10, 35), (11, 57)],
        );
    }

    fn divmod_helper(args: [u64; 2], time: u32, results: [u64; 2]) {
        for (i, op_str) in ["/", "%"].iter().enumerate() {
            run_test(
                &format!("calc {} v0 v1 into v2", op_str),
                env_from(vec![(0, args[0]), (1, args[1]), (2, 1337), (100, i as u64)]),
                Halts::OnOrBefore(time),
                vec![(0, args[0]), (1, args[1]), (2, results[i])],
            );
        }
    }

    #[test]
    #[ignore]
    fn test_calc_divmod_div0() {
        divmod_helper([0, 0], 30, [0, 0]);
        divmod_helper([10, 0], 300, [10, 10]);
        divmod_helper([20, 0], 600, [20, 20]);
    }

    #[test]
    fn test_calc_divmod() {
        // Canary up front:
        divmod_helper([25, 10], 60, [2, 5]);

        divmod_helper([0, 1], 20, [0, 0]);
        divmod_helper([0, 2], 20, [0, 0]);
        divmod_helper([0, 999], 20, [0, 0]);

        divmod_helper([1, 1], 35, [1, 0]);
        divmod_helper([2, 1], 60, [2, 0]);
        divmod_helper([3, 1], 90, [3, 0]);
        divmod_helper([10, 1], 200, [10, 0]);

        divmod_helper([8, 10], 60, [0, 8]);
        divmod_helper([9, 10], 60, [0, 9]);
        divmod_helper([10, 10], 60, [1, 0]);
        divmod_helper([11, 10], 60, [1, 1]);
        divmod_helper([19, 10], 90, [1, 9]);
        divmod_helper([20, 10], 90, [2, 0]);
        divmod_helper([21, 10], 90, [2, 1]);
    }

    #[test]
    fn test_calc_divmod_large() {
        divmod_helper([254, 256], 60, [0, 254]);
        divmod_helper([255, 256], 60, [0, 255]);
        divmod_helper([256, 256], 60, [1, 0]);
        divmod_helper([257, 256], 60, [1, 1]);

        divmod_helper([65534, 256], 1000, [255, 254]);
        divmod_helper([65535, 256], 1000, [255, 255]);
        divmod_helper([65536, 256], 1000, [256, 0]);
        divmod_helper([65537, 256], 1000, [256, 1]);
        divmod_helper([65541, 256], 1000, [256, 5]);
    }

    #[test]
    fn test_calc_divmod_verylarge() {
        // These are just some random u64s divided by some random u32s.

        // Python3:
        // #!/usr/bin/env python3
        // 
        // import random
        // 
        // def gen(num_bits, denom_bits):
        //     num = random.randrange(2 ** num_bits)
        //     while True:
        //         denom = random.randrange(2 ** denom_bits)
        //         if denom != 0:
        //             break
        //     div = num // denom
        //     mod = num % denom
        //     assert div * denom + mod == num, (num, denom, div, mod)
        //     steps = max(1000, 670 * len(bin(div - 5).split('1')))
        //     print('        divmod_helper([0x{:016x}, 0x{:016x}], {}, [0x{:016x}, 0x{:016x}]);'.format(num, denom, steps, div, mod))
        // 
        // print('        // u64/u32 ~= u32, smoke test')
        // for _ in range(8):
        //     gen(64, 32)
        // print('        // u64/u61 ~= u3, large mod')
        // for _ in range(8):
        //     gen(64, 61)
        // print('        // u64/u4 ~= u60, large div')
        // for _ in range(8):
        //     gen(64, 4)

        // u64/u32 ~= u32, smoke test
        divmod_helper([0x097f1e09bec7def9, 0x00000000f7d4a0a9], 8710, [0x0000000009cf418d, 0x00000000683978e4]);
        divmod_helper([0xfa07873df47c40f5, 0x0000000017175568], 16080, [0x0000000ad3f375ee, 0x00000000090a5245]);
        divmod_helper([0xd9e8fc88c3f325c6, 0x000000009d3ab39b], 11390, [0x0000000162ccd931, 0x0000000073f4621b]);
        divmod_helper([0x24777262b712e2de, 0x0000000070988f67], 11390, [0x0000000052e93a33, 0x000000003571fb59]);
        divmod_helper([0xc674fe8ac9965e4c, 0x000000001823dabd], 12060, [0x000000083897d042, 0x0000000011236992]);
        divmod_helper([0xb61b860e8727737a, 0x00000000709952f7], 10050, [0x000000019e081dc6, 0x0000000008734d70]);
        divmod_helper([0x8cb1ed27b5a43968, 0x00000000eddd9cd2], 13400, [0x00000000976bd96e, 0x000000003cb6d52c]);
        divmod_helper([0x53a003009b261baa, 0x000000005094dbc3], 11390, [0x0000000109ab4c81, 0x0000000028a47a67]);
        // u64/u61 ~= u3, large mod
        divmod_helper([0x53abe7ac72dda83a, 0x1f3e9613fd5a484b], 2010, [0x0000000000000002, 0x152ebb84782917a4]);
        divmod_helper([0x80a5b8ba8d4fde69, 0x0d642d43bd30126d], 1340, [0x0000000000000009, 0x08202158e69f3894]);
        divmod_helper([0xff7e0b56ec9860f9, 0x06eb93394bdcca84], 4020, [0x0000000000000024, 0x065d5748418be669]);
        divmod_helper([0x69deee143f0a3833, 0x08006fc68e22321d], 1340, [0x000000000000000d, 0x01d940ff074dacba]);
        divmod_helper([0x92af0579a6d908d2, 0x169185a4f5848b5e], 1340, [0x0000000000000006, 0x0b45e39be5bdc49e]);
        divmod_helper([0xc8e051d741402f1b, 0x0755c8fa0015dc53], 2680, [0x000000000000001b, 0x02d41f793ef1f25a]);
        divmod_helper([0xbfa4dac2880d2222, 0x0318e9978bfec48f], 2680, [0x000000000000003d, 0x02b531a62c584c0f]);
        divmod_helper([0x181d625ecc5d5beb, 0x0c44273c1f72614a], 1340, [0x0000000000000001, 0x0bd93b22aceafaa1]);
        // u64/u4 ~= u60, large div
        divmod_helper([0x177f1ea78887a74a, 0x0000000000000009], 17420, [0x029c58bd480f1296, 0x0000000000000004]);
        divmod_helper([0x9d88ef4f768dab5d, 0x000000000000000a], 20770, [0x0fc0e4bb25749122, 0x0000000000000009]);
        divmod_helper([0x6cccb6b00811e9df, 0x0000000000000004], 18760, [0x1b332dac02047a77, 0x0000000000000003]);
        divmod_helper([0x023a5ee7989b3ee2, 0x000000000000000a], 19430, [0x0039097d8f42b97d, 0x0000000000000000]);
        divmod_helper([0x96af240ab662222d, 0x000000000000000c], 20100, [0x0c8e985639dd82d9, 0x0000000000000001]);
        divmod_helper([0xe6d49eadc19dcde8, 0x000000000000000d], 21440, [0x11c1960d5da9ad60, 0x0000000000000008]);
        divmod_helper([0x69c28f16f2058b68, 0x0000000000000004], 20100, [0x1a70a3c5bc8162da, 0x0000000000000000]);
        divmod_helper([0x538699b85202aec8, 0x0000000000000008], 18090, [0x0a70d3370a4055d9, 0x0000000000000000]);
    }

    fn split_helper(args: [u64; 1], time: u32, results: [u64; 2]) {
        run_test(
            "split v0 into v1 v2",
            env_from(vec![(0, args[0]), (1, 0xbad), (2, 0xbaaaad)]),
            Halts::OnOrBefore(time),
            vec![(0, args[0]), (1, results[0]), (2, results[1])],
        );
    }

    #[test]
    fn test_split_simple() {
        split_helper([0xcafe18889], 30000, [0x1001, 0xcafe]);
        split_helper([0x0], 30000, [0, 0]);
        split_helper([0x8], 30000, [0, 0]);
        split_helper([0x88888], 30000, [0, 0]);
        split_helper([0x70], 30000, [0, 7]);
        split_helper([0x78], 30000, [7, 0]);
        split_helper([0x7], 30000, [7, 0]);
        split_helper([0x788888], 30000, [7, 0]);
        split_helper([0x7088888], 30000, [0, 7]);
        split_helper([0x71], 30000, [0o1, 7]);
        split_helper([0x79], 30000, [0o17, 0]);
        split_helper([0x788889], 30000, [0o100007, 0]);
        split_helper([0x7088889], 30000, [0o100000, 7]);
        split_helper([0x88889], 30000, [0o100000, 0]);
    }

    #[test]
    fn test_split_longhead() {
        split_helper([0b11101111101111101111111010111111], 60000,
                     [0b_111_011_110_111_110_011_111_110_000, 0]);
        split_helper([0b01101111101111101111111010111111], 60000,
                     [0b_111_011_110_111_110_011_111_110, 0]);

        split_helper([0b10011100101111001000110110101110], 60000,
                     [0b_110_010_101_000_100_011_100_001_000, 0]);
        split_helper([0b00011100101111001000110110101110], 60000,
                     [0b_110_010_101_000_100_011_100_001, 0]);
    }

    #[test]
    fn test_split_large() {
        // 0b_101_000_110_111_111_011_000_010 :: 0x57af7082
        //      D   8   E   F   F   B   8   2 (reverse)
        // = 0x57af708228bffe8d
        split_helper([0x57af708228bffe8d], 100000, [0b_101_000_110_111_111_011_000_010, 0x57af7082]);
    }
}
