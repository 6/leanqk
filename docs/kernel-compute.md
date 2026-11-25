# Kernel computation: the closed-term evaluator

Proofs by `decide`, by reflection and by certificate checkers run inside the
kernel are checked by reduction: the kernel reduces a closed term such as
`Decidable.decide P` to `Bool.true`. `src/check/eval/` is a fast evaluator for
these closed terms. This note describes what it does, where it is used and why
it gives the same verdicts as the kernel's own reduction.

## Where it is used

There is one hook, in `Tc::whnf` (`src/check/tc.rs`). After the cache lookup,
`whnf(e)` of a term `e` with no free and no loose bound variables first asks
the evaluator (`eval::whnf`). If the evaluator answers with a term `r`, `whnf`
caches it and returns it. If not, `whnf` goes on exactly as before. Nothing
else in the checker calls the evaluator. Definitional equality reaches it
through `whnf`. For example, `decide P =?= true` reduces `decide P` with
`whnf`, as Lean's kernel does.

`NITROLEAN_EVAL=0` turns the evaluator off. `nitrolean check --stats` prints how
often it was called, how often it answered, how many steps it took and why it
gave up. `NITROLEAN_EVAL_DEBUG=1` says where it got stuck and
`NITROLEAN_EVAL_PROFILE=1` which constants it reached most.

## How it evaluates

It is an environment machine (in the style of Krivine's and Crégut's machines)
over the checker's hash-consed term DAG:

- A **thunk** is a term together with an environment for its loose bound
  variables. It is evaluated at most once (call by need), then holds its value.
  An application's arguments become thunks, so nothing is evaluated unless the
  reduction needs it. Beta reduction binds thunks in the environment and never
  substitutes into terms.
- A **value** is a weak head normal form:
  - a `Nat` literal (a machine word, or a big integer from 2^64 up);
  - a string literal;
  - a constructor applied to thunks;
  - a closure (a lambda and its environment);
  - a head that does not reduce (a sort, a Pi, an inductive type, an axiom, an
    opaque constant, `Quot.mk`) applied to thunks;
  - a recursor or built-in operation waiting for more arguments;
  - an array held as a vector of thunks.
- **Sharing**: every closed subterm has one thunk per declaration, so a closed
  term is evaluated once. An application `c a₁ … aₙ` of a definition whose
  arguments all stand for known closed terms `t₁ … tₙ` shares its value with
  the closed term `c t₁ … tₙ` (which the store hash-conses). This is the
  sharing that `whnf`'s cache gets after substitution. It is kept only for
  constants where it pays off.
- Deep recursion (a long chain of thunks each needing the next) runs on extra
  stack segments allocated on demand (`stacker`), up to `MAX_DEPTH` nested
  evaluations.

## Why the answers are right

**What a value stands for.** Every thunk and value stands for a closed term:

- a thunk `(t, ρ)` for `t` with its loose bound variables replaced by the terms
  `ρ` stands for;
- a constructor or neutral value for its head applied to its arguments' terms;
- a closure `(λx.b, ρ)` for `(λx.b)` under `ρ`;
- an array vector `[x₀ … xₙ₋₁]` of element type `α` for
  `Array.mk α (x₀ :: … :: xₙ₋₁ :: [])`;
- a literal for itself.

A thunk made from a closed term stands for that term itself. Reading back
(`value::Readback`) builds exactly the term a value stands for. It keeps
sharing, and reads a closed thunk back as its original term, evaluated or not,
just as `whnf` leaves arguments unevaluated.

**Every step is a kernel step.** The machine only takes steps that `Tc::whnf`
and `Tc::whnf_core` take themselves, on the terms the values stand for:

- **beta and zeta**: binding a thunk for a lambda's or `let`'s variable is
  substitution, delayed;
- **delta**: a definition or theorem is replaced by its value, with its
  universe parameters instantiated (`is_delta`: only declarations visible
  from the one being checked, with the right number of levels; opaque
  constants and axioms are neutral);
- **iota**: a recursor with its major premise evaluated to a constructor of
  one of its rules is replaced by the rule's right-hand side, applied as in
  `inductive_reduce_rec`. A `Nat` literal major premise becomes `Nat.zero` or
  `Nat.succ (n-1)`, and a string literal `String.ofList […]`, as in
  `nat_lit_to_constructor` and `string_lit_to_constructor`;
- **K-like recursors**: before evaluating the major premise, the machine
  calls the checker's own `ctor_when_k`. It infers the premise's type and
  checks with the checker's definitional equality that it is the type of the
  constructor, as Lean does. Only then is the constructor used. A proof is
  never evaluated just to find `Eq.refl`;
- **projections**: `x.i` evaluates `x` to a constructor of the structure and
  takes field `i`;
- **quotients**: `Quot.lift f h (Quot.mk r a) ⋯` and `Quot.ind`, as in
  `quot_reduce_rec`;
- **`Nat` literal arithmetic**: `Nat.succ` and the fourteen operations of
  `ext.rs`, only where `Ext` enables them (definitions that match a known
  prelude's: `fingerprint.rs`), with the results of `Tc::nat_op`. The machine
  gives up where `Tc::nat_op` would raise an error (the 128 MB size limit, a
  shift or exponent that does not fit in 32 bits), so `whnf` raises it.
  Arguments that are not literals make the operation unfold to its
  definition, as in `whnf`.

The term a value stands for is therefore reachable from the input by kernel
reduction steps. So it is definitionally equal to the input, by the rules the
checker's definitional equality itself uses.

**The answer is a weak head normal form.** A constructor application, a
literal, a lambda, a sort, a Pi, or a neutral head (an inductive type, an
axiom or opaque constant, `Quot`, `Quot.mk`) applied to arguments cannot be
reduced at its head by `whnf_core` or by delta. Neither can a recursor
missing its major premise, nor `Quot.lift` or `Quot.ind` missing theirs. A
built-in `Nat` or array operation missing arguments *would* still unfold, so
the machine gives up on those instead of answering. It also gives up on a
recursor whose major premise is not a constructor, a projection of something
that is not a constructor, an unknown constant, a free variable, a thunk that
depends on itself, too deep a recursion, and an ill-typed application. In all
these cases `whnf` goes on with its own reduction, from the original term.

**Same answer, same verdicts.** Where the evaluator answers, its result is a
weak head normal form of the input, as is `whnf`'s own. The two can differ
only in which arguments are written as their evaluated forms. Read-back keeps
the original terms of closed arguments, so in practice they are the same
term. Since `whnf` is only used up to definitional equality, a different but
definitionally equal weak head normal form cannot make a checker accept what
the kernel rejects. The evaluator only takes kernel steps, so it can't prove
a false equation.

**Termination.** Evaluation is as lazy as `whnf`. A term is forced exactly
where `whnf` would reduce it: a recursor's major premise, a projected
structure, both arguments of a built-in operation, the quotient argument of
`Quot.lift`. So the evaluator terminates whenever `whnf` does. It may
terminate where `whnf` does not finish in practice, because shared thunks are
never evaluated twice.

**Structure eta.** For a recursor on a structure, nitrolean's `whnf` expands
the major premise by eta before reducing it (a deliberate divergence, see
`corpus/divergences.md`). The evaluator instead evaluates the major premise,
as Lean v4.36.0's kernel does. If the major premise is stuck, the evaluator
gives up and `whnf` applies eta itself.

## Proofs

The machine never needs the value of a proof. It needs a proof's term only
to read back an answer that contains it, or to type the major premise of a
`K`-like recursor. Yet a lazy proof can hold a lot of memory. A decision
procedure's result `isTrue h` holds the proof `h`, a thunk that refers to the
proofs of every step of the decision. Stored in a data structure, such a
result keeps every step alive. LRAT-Catcher's checker stores each clause
with the proof of its `Nodup` decision, so all its `DecidableEq` traces stay
alive: this was most of its memory.

So a thunk for a proof (a theorem, or a constructor of an inductive
proposition, applied to arguments) is **erased**, unless the terms of its
variables are all known: then it is made the closed term it stands for. An
erased thunk holds its term and only a weak reference to its environment, so
it keeps nothing alive. While
something else keeps the environment, the thunk behaves exactly like a
delayed one. Once it is gone, forcing the thunk or reading it back gives up
(`Bail::Erased`). `whnf` then evaluates the term again from scratch, with
proofs kept and the cached values dropped. If a run does not give up,
erasure changes nothing in it: the machine only looks at a thunk to force it
or to read it back, so the run takes the same steps as without erasure.

**Decisions.** An answer `Decidable.isTrue p h` is read back as
`isTrue p (of_decide_eq_true p e (Eq.refl true))`, where `e` is the input and
`p` the proposition of its type `Decidable p`. `isFalse` uses
`of_decide_eq_false`. This never reads back `h`, which may be erased or a
huge term (the proof of a `Nodup` over a few hundred elements has millions
of nodes). The answer is definitionally equal to the real one by proof
irrelevance: `h` and the new proof have the same type `p`, and definitional
equality compares proofs by their types only. The lemmas are used only if
they are theorems whose types are exactly the core library's.

## Arrays

Lean's `Array α` is a structure around `List α`, and its operations are
defined by list operations. In the kernel, `a[i]` therefore walks `i` list
cells and `a.set i v` copies `i` of them. The evaluator holds arrays as
vectors and runs four operations on them directly:

| operation | definition (Lean v4.30 – v4.36) | on a vector |
|---|---|---|
| `Array.size a` | `a.toList.length` | its length |
| `Array.getInternal a i h` | `a.toList.get ⟨i, h⟩` | element `i` |
| `Array.set xs i v h` | `⟨xs.toList.set i v⟩` | a copy with element `i` replaced |
| `Array.push a v` | `⟨a.toList.concat v⟩` | a copy with `v` appended |

These are not kernel rules, so each one is enabled only if the operation's
definition, and everything it depends on (`List.length`, `List.get`,
`List.set`, `List.concat`, `List`, `Array`, `Nat`, `Fin`, …), match the
fingerprints of one Lean version's prelude. This is the same rule as for the
built-in `Nat` operations. Then running the operation on the vector gives the
value whose term is what unfolding the definition and reducing the list
operation gives. The vector stands for `Array.mk α [x₀, …]`, and for example
`List.set [x₀, …, xₙ₋₁] i v` reduces to `[x₀, …, v, …, xₙ₋₁]` for `i < n`.
An array value that is `Array.mk` of a list is turned into a vector only if
its spine evaluates to the end (forcing its cells, not its elements). An
index that is not a literal below the length, or an array that is not a
value, makes the operation unfold to its definition. A vector meeting a
projection or a recursor is turned back into the constructor application it
stands for. `set` and `push` copy the vector only if it is shared.

## Built-in operations of several Lean versions

The fingerprint table (`src/check/fingerprint_table.rs`, written by
`examples/fingerprints.rs`) holds the prelude definitions of the `Nat` and
`Array` operations of Lean v4.36.0, v4.34.0 and v4.30.0, each digest with the
versions it comes from. An operation is enabled only if every declaration it
depends on matches one and the same version. Before this, an export made
with v4.34.0 or v4.30.0 got no built-in `Nat.div`, `Nat.mod`, `Nat.gcd`,
`Nat.land` or `Nat.xor`, because `dite`, `ite` and a few others differ from
v4.36.0's. Literal division then ran in unary: the published planar-graph
result (doi:10.5281/zenodo.24467489) divides coordinates near 4·10⁸ and ran
out of memory.

## Tests

`tests/kernel/cases.py` has 38 `eval-*` cases, each a claim proved by
`Eq.refl` (so only reduction decides it) together with a false twin. They
cover:

- K-like recursors whose indices do or do not match;
- structure eta on an opaque major premise;
- `Quot.lift`;
- string literals;
- deep recursion;
- partial applications of built-in operations;
- `Nat.rec` on a literal, and big literals;
- shared lets and closures;
- arrays: `get!` and `getD` in and out of range, `set!`, `push`, array
  equality, and arrays of functions;
- erased proofs that are needed after all: a cast over a theorem applied to
  a variable, `And.rec` on a constructed proof, an answer that holds a
  proof.

Lean's verdict on each is recorded in `cases.tsv`. The arena's `perf` tests in
`corpus/` exercise the evaluator on larger computations. Every corpus and
kernel test gives the same verdict with the evaluator on and off.

## Results

`bench/kernel-compute/` builds the benchmarks from public inputs and
measures four checkers within 60 s and 4 GiB of resident memory; its README
has every number. In short, the largest kernel-only LRAT proof checked
within that budget:

| series | nitrolean | Lean's `leanchecker` | gruszka, nano-lean |
|---|---:|---:|---:|
| GBD instances | 696 KB (45 s, 1.5 GiB) | 1.9 KB | 31 KB |
| pigeonhole PHP(n+1, n) | 796 KB (47 s, 1.5 GiB) | 1.7 KB | 9.6 KB |

The next sizes (1.8 MB and 4.5 MB) run out of 4 GiB after 2 to 5 minutes.
The planar-graph result (doi:10.5281/zenodo.24467489, its own declarations
and their closure) takes 26.6 s and 248 MiB. `leanchecker` needs 524 s and
7.5 GiB, and nano-lean 26.9 s and 1.9 GiB.

Steps on the way, on that result and on the 278 KB LRAT proof (lrat06):

| | planar-graph result | LRAT, 278 KB |
|---|---|---|
| without the evaluator | 211 s, 2.0 GiB | out of memory after 35 s |
| evaluator with the built-in operations of v4.36.0 only | out of memory | not measured |
| … of v4.36.0, v4.34.0 and v4.30.0 | 54 s, 457 MiB | not measured |
| adaptive memoization, before erasing proofs | 32.9 s, 270 MiB | 18.4 s, 875 MiB |
| proofs erased, decisions read back without their proofs | 26.6 s, 248 MiB | 15.8 s, 458 MiB |

## Not done

- A hook in definitional equality (comparing two closed terms by evaluating
  both): `is_def_eq` still unfolds lazily and reaches the evaluator only
  through `whnf`.
- Compiling hot definitions to closures. The machine interprets the term DAG,
  at about 60 ns per step.
- Fast paths for `ByteArray`, `List` operations and derived `DecidableEq`
  instances, which dominate what is left of the LRAT checker's time. Its
  steps grow a little faster than the proof (about 1,400 steps per LRAT
  byte at 700 KB), and memory about linearly once proofs are erased.
