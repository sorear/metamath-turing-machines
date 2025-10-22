# Directory structure

Subdirectories of `machines/` contain specific machine constructions intended
to be reproducible. Each subdirectory contains a single .nql file and a single
.tm which represents the actual machine. After being committed, a machine will
not change up to isomorphism. Submissions of new machines is encouraged if they
address new "sufficiently interesting" problems or are smaller than existing
machines for the same problem. An optimized version of an existing machine is a
new machine and requires a new subdirectory.

No attempt is currently made to track pre-2017 compiler versions, so machines
existing in 2017 are dated 2017 to reflect use of the 2017 compiler.

`doc/` contains explanatory material (TBD) describing the construction of
Turing machines and the behavior of the machines in `machines/`. Documentation
in the machine subdirectory will generally be limited to referencing the
combined machine construction document. Documentation updates are strongly
encouraged for any new machine and the compiler features it uses.

`compiler/` holds a Python program which generates the Turing machines in this
repository, under guidance from their corresponding .nql files. Compilation of
the .nql for a committed machine shall exactly reproduce the corresponding .tm.
Compiler changes which cause committed machines to generate non-isomorphic
Turing machines are not permissible. Changes which result in isomorphic textual
changes are discouraged but permissible in exceptional cases. Compiler
improvements have been a major driver of state count reductions and continued
improvements are encouraged, but for reproducibility they must be "opted into"
by some mechanism in the .nql file.

There is a single compiler in the repository for reasons of maintainer
convenience. There is no fundamental distinction between the .nql and .py
inputs, and changes to the "compiler" are considered to have equal status to
changes to the "inputs". If compilation strategies diverge too much it may be
necessary to have multiple separate compilers, but this will complicate
development and testing. Reproducibility will require identifying the compiler
used to reproduce each individual machine.

`misc/` contains test and maintenance code which does not contribute to a
stable machine in `machines/`. Develop stuff here before moving it to
`machines/` when it is stable and documented.

This file contains information for running the NQL compiler and maintaining the
repository.

# Compiler changes through 2017

    530d545 2017-08-07 Main functions are automatically looped
    815b8a8 2017-08-07 Purely additive, builtins and alignment mechanism
    70064e1 2017-08-06 Transfer functions are sorted
      riemann-matiyasevich-aaronson added here
      pjt33's zf added here
    cc993b3 2016-05-17 Purely additive, true/false
      pjt33's riemann improvements
    all prior machines are sorear so detailed analysis not needed

#

(Remainder of this file needs a rewrite to address current needs rather than
people already familiar with Laconic in 2016)

# What is NQL?

Not-Quite-Laconic is a language and compiler for generating Turing machines with small state counts.
It is directly inspired by [Adam Yedidia's Laconic](https://github.com/adamyedidia/parsimony),
and the language is similar, but the implementation is less so.
Laconic and the programme of constructing small Turing machines to establish upper bounds on provable BB(k) values are [discussed on Scott Aaronson's blog](http://www.scottaaronson.com/blog/?p=2725).

NQL uses a different compilation methodology based on register machines and constructing binary decision diagrams to compress large programs without an explicit call stack.
It achieves "a few" times smaller state counts than Laconic for the range of programs relevant to the BB(k) problem; e.g. 1919 states for a ZF proof enumerator.
On very small programs it cannot compete with hand-coding, and behavior on much larger programs is unknown; Laconic *may* regain the upper hand,

# Differences from Laconic

 * NQL does not support negative numbers.  The `-` operator is actually monus and clamps at zero.

 * NQL implements only procs, not funcs; in other words your procedures are copied for every distinct combination of variables passed to them.
   This is less of a problem than it appears because BDD compression can share any subtrees that don't use arguments; still, it's best to use variables consistently, or copy to globals.

 * NQL supports global variables which can be referenced from any function.

 * NQL functions cannot be recursive (in other words, the call graph must be directed acyclic).  Very deep call graphs are also somewhat problematic for the state count.

 * NQL does not have any native support for lists (for this reason, Yedidia's "friedman.lac" has not yet been ported).

 * NQL presently distinguishes between numbers and booleans, and trying to mix them will cause an assertion fault.

 * NQL doesn’t require return statements.

 * NQL has a `switch` statement, which produces more parsimonious code than long elsif chains.

 * Minor syntactic differences: `ifelse` is replaced with a Perl-style `if ... elsif ... else`; global variables do not have a specific type.

# Setup

1. Make sure `python3` is installed.  This code is tested on 3.4.3
2. Make sure the "pyparsing" package is installed.  For instance: `pip3 install pyparsing`.  You may need to bootstrap pip first.

# Running

Generate a Turing machine from NQL sources:

    python3 nqlaconic.py --print-tm zf.nql

Print intermediate call tree code (very relevant for debugging):

    python3 nqlaconic.py --print-subs zf.nql

Built-in Turing machine executor:

    python3 nqlaconic.py --run-tm squaresaresmall.nql

# Optimization ideas

## Backend (framework.py)

 * `while (x) { x = x - 1; ... }` generates an inc immediately followed by a dec; could be peepholed (20 minutes, 0.5%)

 * Inlining subs used once to reduce nop padding (1 hour, 2%)

 * CFG optimizer could break down code into basic blocks and rearrange them to minimize unconditional jumps (4 hours, 1%)

 * Hill-climbing or genetic global optimizer to rearrange nops and jumps to maximize sharing (16 hours, 5%)

## Middle end (nqlast.py)

 * Global live-range tracking to do destructive reads when possible and eliminate redundant zeroing (16 hours, 5%)

 * Local variables and interprocedural register allocation will cut down on the number of live variables and transfer subs (8 hours, 2%)

## Specific test programs

 * ZF: Replace ax-17 with several other axioms to get rid of "var_not_used" (WIP, 15%)

 * ZF: combine all non-propositional axioms into a giant conjunction to save on control flow (WIP, 50%)

 * ZF: Rewrite pair and unpair to use fewer multiplications and divisions (1 hour, 15%)

# On claims

reproducibility of specific version
