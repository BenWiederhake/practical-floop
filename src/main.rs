use std::collections::BTreeMap;
use std::ops::{Add, Sub, Index, IndexMut};

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

impl Add<&Natural> for Natural {
    type Output = Natural;

    fn add(self, rhs: &Natural) -> Natural {
        Natural(self.0.checked_add(rhs.0).unwrap())
    }
}

/*impl Sub<u64> for Natural {
    type Output = Natural;

    fn sub(self, rhs: u64) -> Natural {
        Natural(self.0.saturating_sub(rhs))
    }
}*/

impl Sub<&Natural> for Natural {
    type Output = Natural;

    fn sub(self, rhs: &Natural) -> Natural {
        Natural(self.0.saturating_sub(rhs.0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        assert_eq!(Natural(42) + 1337, Natural(42 + 1337));
        assert_eq!(Natural(0) + 0, Natural(0));
    }

    #[test]
    fn test_sub() {
        assert_eq!(Natural(0) - 0, Natural(0));
        assert_eq!(Natural(5) - 3, Natural(2));
        assert_eq!(Natural(5) - 55, Natural(0));
    }

    #[test]
    fn test_clonable() {
        let x = Natural(123);
        let y = x.clone() + 321;
        let z = y.clone() - 40;
        assert_eq!(x, Natural(123));
        assert_eq!(y, Natural(444));
        assert_eq!(z, Natural(404));
    }
}

#[derive(Clone, Copy, Debug, Ord, Eq, PartialOrd, PartialEq)]
struct VarId(u32);

#[derive(Clone, Debug)]
struct PloopBlock(Vec<PloopStatement>);

#[derive(Clone, Debug)]
enum PloopStatement {
    AddToInto(Natural, VarId, VarId),
    SubtractFromInto(Natural, VarId, VarId),
    LoopDo(VarId, PloopBlock), // Rc
    //DoTimes(Natural, PloopBlock), // Rc?
    // loop-forever
    // break
    // calc
}

impl PloopStatement {
    fn apply(&self, conf: &mut Configuration) {
        // TODO: Assertions would need a return value of sorts
        use PloopStatement::*;
        match self {
            AddToInto(amt, src, dst) => {
                println!("AddToInto: {:?} {:?} {:?}", amt, src, dst);
                let newval = conf.state[src].clone() + amt;
                conf.state[dst] = newval;
            },
            SubtractFromInto(amt, src, dst) => {
                println!("SubtractFromInto: {:?} {:?} {:?}", amt, src, dst);
                let newval = conf.state[src].clone() - amt;
                conf.state[dst] = newval;
            },
            LoopDo(a, b) => {
                println!("LoopDo: {:?} {:?}", a, b);
                unimplemented!();
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
    fn new(input: Natural, program: PloopBlock) -> Configuration {
        let mut program_statements = program.0;
        program_statements.reverse();
        Configuration {
            state: Environment::new(input),
            stack: program_statements,
        }
    }

    fn step(&mut self) {
        let statement : PloopStatement = self.stack.pop().unwrap();
        statement.apply(self);
    }

    fn run(&mut self) {
        while !self.stack.is_empty() {
            self.step();
            println!("Configuration after one step: {:?}", self);
        }
    }
}

fn main() {
    /*let data = fs::read_to_string("/etc/hosts").expect("Unable to read file");
    println!("{}", data);*/

    use PloopStatement::*;
    let sample_prog = PloopBlock(vec![
        SubtractFromInto(Natural(5), VarId(0), VarId(1)),
        AddToInto(Natural(5), VarId(1), VarId(1)),
        AddToInto(Natural(0), VarId(2), VarId(0)),
        LoopDo(VarId(1), PloopBlock(vec![
            AddToInto(Natural(2), VarId(0), VarId(0)),
        ])),
        // This implements:
        // x1 = min(5, x0)
        // x0 = 2 * x1
    ]);

    let mut conf = Configuration::new(Natural(2), sample_prog);
    println!("Initial configuration: {:?}", conf);
    conf.run();
    println!("Done");
}
