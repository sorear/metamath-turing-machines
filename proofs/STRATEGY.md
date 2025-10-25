Build specific proofs for specific Turing machines, we're not trying to prove
the compiler in general.

IR-free, bottom-up approach which proves properties directly on the Turing
machine. Do not construct intermediate Turing machines or other intermediate
representations, do not define operational semantics at a high level. Since
there is only one Turing machine it can be a constant and not a parameter in
(most) proofs.

Read the Turing machine from the .tm files. The proofs are not parameterized
but the proof scripts can be reusable, to a degree.

Haltedness is expressed as an extra state so that the world-step function can
be total. Our fundamental predicate is A ->-> B, where A and B are
world-classes (sets of world-states), and the interpretation is that every
world-state in A evolves after one or more world-steps to a world-state in B.
World-classes allow for parts of the state to be treated as garbage without
quantification. High-level knowledge is carried by functions which construct
world-classes.

Primitive register operations can be identified by name in the .tm and proven
inductively in a class model that starts from a state, a prefix (the left half
of the tape), and the right side as a list of integer registers. They return to
a distinguished nextstate state with the same prefix and a modified register
list, again identified by name. These are lifted to a higher level
representation which only constrains a prefix of the register list.

From the .subs we construct dispatch, nextstate, and jump proofs. These divide
the prefix into a return prefix and an active prefix; with an assumption that
the return prefix dispatches back to the sub root, we prove that individual
instructions in the sub evolve in the expected way, simulating an operational
semantics of the subprogrammed register machine. These can be further lifted by
idiom recognition, perhaps not quite to the level of expression decompilation.

Initialization is handled by straight calculation; the initial class I ->->
an encoded world-class representing the start of main with zero registers.

The effect of subs can then be mapped to functions acting on encoded states.
Move to a higher level which assumes scratch registers are zeros and represents
the stacks. Prove high level behavior of the main loop: next proof if stack
empty, pop and apply a proof step, halt if contradiction. This is the first
place zf2.nql specifics are used.

By induction over _proofs_, for any theorem there is a proof-stack prefix such
that evolving with that prefix will either halt or lead to a state with the
proof stack cleanly popped and the theorem, not the contradiction, cleanly
pushed. If the contradiction is provable then there is a next-proof value such
that evolution halts from an empty proof-stack and the proper next-proof,
regardless of the wff-stack. Loosen to ignore the wff-stack and the contents
(but not the depth) of the wff-stack; double induction shows that any numbered
proof is reachable if it doesn't halt first, so completeness is established.

Prove soundness by loosening the world-classes. Define a class S where the
proof-stack and next-proof are arbitrary, the wff-stack contains only theorems,
and the halted world-state is included only if the contradiction is provable. S
->-> S, as may be proved by expanding the union. From I ->-> S and S ->-> S,
the machine halts only if S contains the halted world-state; this is where it
becomes necessary that ->-> is irreflexive.

Finally (or perhaps at the start) a version of the model existence theorem to
show that the formulation of predicate logic is itself valid.
