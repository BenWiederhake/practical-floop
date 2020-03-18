use std::ops::{Add, Sub};

//use std::fs;

#[derive(Clone, Debug)]
// For now, always clone explicitly.
// This makes transition to "BigNum" easier, I hope?
struct Natural(u64);

impl Add<u64> for Natural {
    type Output = Natural;

    fn add(self, rhs: u64) -> Natural {
        Natural(self.0.checked_add(rhs).unwrap())
    }
}

impl Sub<u64> for Natural {
    type Output = Natural;

    fn sub(self, rhs: u64) -> Natural {
        Natural(self.0.saturating_sub(rhs))
    }
}

#[derive(Clone, Debug)]
struct VarId(u32);

#[derive(Clone, Debug)]
struct PloopBlock(Vec<PloopStatement>);

#[derive(Clone, Debug)]
enum PloopStatement {
    AddToInto(Natural, VarId, VarId),
    SubtractFromInto(Natural, VarId, VarId),
    LoopDo(VarId, PloopBlock), // Rc
    // DoTimes(Natural, PloopBlock), // Rc?
    // loop-forever
    // break
    // calc
}

fn main() {
    /*let data = fs::read_to_string("/etc/hosts").expect("Unable to read file");
    println!("{}", data);*/

    let x = Natural(123);
    let y = x.clone() + 321;
    let z = y.clone() - 40;
    println!("Hello, world!  {:?} {:?} {:?} {:?} (should be 42, 123, 444, and 404)", Natural(42), x, y, z);

    use PloopStatement::*;
    let sample_prog = PloopBlock(vec![
        SubtractFromInto(Natural(5), VarId(0), VarId(1)),
        AddToInto(Natural(5), VarId(1), VarId(1)),
        AddToInto(Natural(0), VarId(2), VarId(0)),
        LoopDo(VarId(1), PloopBlock(vec![
            AddToInto(Natural(2), VarId(0), VarId(0)),
        ])),
        // x1 = min(5, x0)
        // x0 = 2 * x1
    ]);

    println!("Sample prog is {:?}", sample_prog);
}
