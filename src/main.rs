use std::ops::{Add, Sub};

//use std::fs;

#[derive(Clone, Debug, Eq, PartialEq)]
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
