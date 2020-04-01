# practical-floop

> A practical variation of BlooP/FlooP, and an implementation of the recursion theorem.

This library/binary implements a parser and interpreter of BlooP/FlooP programs.

## Table of Contents

- [Install](#install)
- [Usage](#usage)
- [Background](#background)
- [Format documentation](#format-documentation)
- [Performance](#performance)
- [TODOs](#todos)
- [NOTDOs](#notdos)
- [Contribute](#contribute)

## Install

This project is not yet ready for installation or production use.  Also, what
kind of production were you thinking of?

## Usage

I intended to write a nice frontend – Oh well, you can paste it in `main.rs`
or something.

## Background

This is strongly inspired by the languages [BlooP and
FlooP](https://en.wikipedia.org/wiki/BlooP_and_FlooP).  The funny thing is
that these languages are very similar, with only once key difference: The
`while` keyword.  BlooP (the language without `while` is bounded, and always
terminates.  FlooP on the other hand is turing-complete.

### Syntactic sugar

In `parse.rs`, one can now easily implement syntactic sugar, and for example
implement a more general `add`, `sub`, or even `if` and `divmod` or something
along these lines, without actually extending the language.

## Format documentation

The following BNF should describe "both" languages (where `{}` means "0 or more"):

```
program ::= block
block ::= { statement }
statement ::= addstmt | substmt | loopstmt | dostmt | whilestmt
addstmt ::= "add" nat "to" ident "into" ident
substmt ::= "subtract" nat "from" ident "into" ident
loopstmt ::= "loop" ident "do" block "end"
dostmt ::= "do" nat "times" block "end"
whilestmt ::= "while" ident "do" block "end"
nat ::= "0x" hexit { hexit }
ident ::= varident | namedident
varident ::= "v" digit { digit }
namedident ::= "_" printable { printable }
hexit ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" | "a" | "b" | "c" | "d" | "e" | "f" | "A" | "B" | "C" | "D" | "E" | "F"
digit ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
printable ::= "a" | "b" | "c" | "d" | "e" | "f" | "g" | …
```

Note: This is inaccurate only with regard to the whitespace, which works "the obvious way", and is non-trivial to describe but uninteresting.

The semantics are:

- A block is executed by executing its statements sequentially
- The "add" and "subtract" statements work in the "obvious" way.
- A "loop" statement evaluates its first argument (the identifier) once, and that determines the number of times that the loop body is executed.
- A "do" statement works similarly, except that the first argument must be a hardcoded natural.  (Therefore, `do times` could have been syntactic sugar; but for implementation reasons it is easier to not.)
- A "while" statement is the entire magic of turing completeness: It evaluates whether the first argument (an identifier) is non-zero.  If it is non-zero, it executes the body, and evaluates the identifier *again*.  This repeats until it evaluates to zero, at which point execution of "while" finishes.

Note that programs in practical-floop work on
[naturals](https://en.wikipedia.org/wiki/Natural_number). So there are no
negative numbers, but also no upper limits.  This means that you *can*
simulate something like a list, you just have to be very clever about it.

## Performance

Terrible, in comparison to modern programming languages.  Of course, what did you expect.

On the other hand, a simple optimization means that nearly all loops which
contain only one statement can be optimized into a single step.  This means
that "complicated" calculations such as "sign" or "add" and "multiply" run
much faster than the code may appear to be.

## TODOs

* Implement syntactic sugar for `calc`, an arbitrary expression evaluation.  I'm thinking of polish notation, because that simplifies parsing by a great deal.  Also, that's why the most recent tests in `exec` all are of arithmetic operations.
* Implement syntactic sugar for `if/then/else`.
* Implement syntactic sugar for `divmod`.
* Implement syntactic sugar for "join these two numbers into one" and "split this number into two"; injective, of course.
* Use all of this to implement lists
* Use all of this to implement an interpreter (careful: the "optimizations" in the interpreter written in Rust probably need to be replicated, or else this will be a lot of pain)
* Use all of this to implement a quine
* Use all of this to implement a [fixed-point construction scheme](https://github.com/BenWiederhake/general_purpose_fixedpoint#general_purpose_fixedpoint)
* Afterwards, solve actual problems like COVID19 or world hunger

## NOTDOs

Here are some things this project will definitely not support:
* General support for high-level languages or even "types"

These are highly unlikely, but if you actually need them and can tell me
how to elegantly implement it, I might look into it:
* Incredibly good performance
* Compilation to native instructions
* binfmt wrapper so that arbitrary files can be treated as a program

## Contribute

Feel free to dive in! [Open an issue](https://github.com/BenWiederhake/practical-floop/issues/new) or submit PRs.
