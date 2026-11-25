# Kernel computation: the closed-term evaluator

Proofs by `decide`, by reflection and by certificate checkers run inside the
kernel are checked by reduction: the kernel reduces a closed term such as
`Decidable.decide P` to `Bool.true`. `src/check/eval/` is a fast evaluator for
these closed terms. This note describes what it does, where it is used and why
it gives the same verdicts as the kernel's own reduction.

## Where it is used

There are two hooks. In `Tc::whnf` (`src/check/tc.rs`), after the cache
lookup, `whnf(e)` of a term `e` with no free and no loose bound variables first
asks the evaluator (`eval::whnf`). If the evaluator answers with a term `r`,
`whnf` caches it and returns it. If not, `whnf` goes on exactly as before. The
evaluating checker's `whnf` (`src/check/nbe/whnf.rs`) does the same for a
value with no free variables, once `whnf_core` leaves it at a definition to
unfold: the value is read back to a term (`src/check/nbe/closed.rs`), and the
evaluator's answer is evaluated back into a value. Nothing else in the checker
calls the evaluator. Definitional equality reaches it through `whnf`. For example, `decide P =?= true` reduces `decide P` with
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
- **Tail calls** do not nest. A beta step that takes all of a closure's
  arguments, a `let` body and a recursor's minor premise (with the fields
  and further arguments) are what `eval_here` evaluates next, in its loop.
  So the stack grows only where a value is needed before going on: a forced
  argument, a major premise, the head of an application. The functions on
  that path keep their frames small: the fast paths and rare cases are
  out of line. Their frames add up to about 1 KB per nested evaluation.
  On `npowRec`-style unary powers in `Fin p` (100002 multiplications), the
  check goes from 1.26 GB to 0.57 GB. The public corpus's peak goes from
  4.5 to 1.8 GB.

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
just as `whnf` leaves arguments unevaluated. A thunk that has been read back keeps
the term it stands for, so later read-backs and memo keys reuse it. This
matters for `K`-like recursors, whose major premise is read back and its
type inferred (below): on Mathlib's Cartan matrix determinants those
read-backs met the same large values again and again. `cartan_A7` went
from 14.5 s in the evaluator to 3.8 s (and from 94 to 65 million steps,
as memo keys became known), at 237 MB instead of 111 MB.

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

## Lists and decidable equality

What is left of a proof checked by LRAT-Catcher's kernel checker is mostly
lists of literals and their comparisons. A literal is a pair of a `PosFin n`
(a subtype of `Nat`) and a `Bool`. Comparing two literals with `==` or with
`decide (a = b)` goes through `instBEqProd` or `instDecidableEqProd`, then
`Subtype.instDecidableEq`, `Nat.decEq` and `Bool.decEq`. Each is a few
matches, each match a `casesOn`, and a recursor step. List functions such as
`List.any` are compiled to structural recursion (`List.brecOn`), which
builds a table of results per cell. So the evaluator runs a few of these
definitions directly:

| definition | on values |
|---|---|
| `List.any l p`, `List.all l p` | `p` on the elements until one is `true` (`false`) |
| `List.elem a l` | `a == x` on the elements until one is `true` |
| `List.filter p l` | `p` on the elements up to the first one kept; the rest of the result is `List.filter p t`, not evaluated |
| `List.reverseAux l r` | `l` reversed onto `r` |
| `List.foldl f a l` | the thunk `f (… (f a x₀) …) xₙ₋₁`, then forced |
| `List.getLast l h` | the last element |
| `List.eraseDupsBy.loop r l acc` | the elements kept, then reversed |
| `List.map f l`, `List.zipWith f l₁ l₂`, `List.append l₁ l₂` | the first cell; its head and the rest are thunks of `f x` (or `f x y`) and of the same operation on the tails |
| `List.length l` | the number of cells |
| `instBEqProd α β bα bβ` | `BEq.mk` of a function that runs `a₁ == a₂ && b₁ == b₂` on pairs |
| `Nat.decEq n m` | on two literals |
| `Bool.decEq a b` | on two booleans |
| `instDecidableEqProd dα dβ x y` | on two pairs: `dα` on the first components, then `dβ` on the second |
| `Subtype.instDecidableEq dα x y` | on two subtype values: `dα` on the values |

Each one is enabled only if its definition and everything it depends on
match one Lean version's prelude (the fingerprint rule above). Every known
version defines the same function, so the loop computes what the definition
computes. Each loop forces the same thunks as the definition, in the same
order, and stops where the definition reaches its weak head normal form:
`any`, `all`, `elem` and `filter` stop at the first element that decides,
`map`, `zipWith` and `append` at the first cell,
while the others need the whole list, as their definitions do. So laziness
and termination are as before. Where a value is not of the expected kind (a
list that is not built from `List.cons` and `List.nil`, a pair that is not
`Prod.mk`, a test that is not a `Bool`), the operation is its definition,
from the original arguments.

**What the results stand for.** A boolean result is the constructor the
definition reduces to. A list result is made of `List.cons` cells whose
elements are the original thunks. The rest of a `filter` stands for
`List.filter p t`. The definition's reduct has, in its place, the
corresponding entry of the `brecOn` table, which reduces to the same thing.
`instBEqProd α β bα bβ` stands for `BEq.mk T (F' α β bα bβ)`, where
`F' = fun α β bα bβ => F` is built from the definition
`fun α β bα bβ => BEq.mk T F`. One beta step turns it into the definition's
reduct. In every case the value stands for a term definitionally equal to
the input, by the unfoldings and reductions of the kernel. That is what the
argument above needs.

**Decisions.** A `DecidableEq` result is `isTrue p h` or `isFalse p h`. Here
`p` is the proposition `x = y` of the type `Decidable p` of the
application, taken from the instance's type over its arguments. `h` is an
erased proof whose environment is already gone. The definition reduces to
the same constructor, with a proposition definitionally equal to `p`, and
some proof `h'` of it. A run that never forces or reads back `h` takes the
same steps as with `h'`, for the reasons given under *Proofs*: the machine
only looks at a thunk to force it or read it back, and `h` has no known
term, so no memo key is built from it. A run that needs `h` (a cast over
the equality, say: a `K`-like major premise) gives up with
`Bail::Erased`. Then `whnf` evaluates again keeping proofs. In that run,
`h` is the term `of_decide_eq_true p (c x₁ … xₙ) (Eq.refl true)` (or the
same with `of_decide_eq_false` and `false`) over the arguments' thunks. It
is a proof of `p` because the instance reduces to `isTrue` (which is what
the fast path computed), so it is definitionally equal to `h'` by proof
irrelevance. Before, the instances were their definitions in that run. On
Mathlib's Cartan matrix determinants, whose evaluation needs a proof once,
the run that keeps proofs is most of the work: `cartan_A7` takes 13 %
fewer steps (107.6 to 93.8 million). A decision that is the answer itself
is read back by *Decisions* above, without `h`.

These four instances are only for Lean v4.34.0 and v4.30.0. From v4.36.0,
`Decidable` is a structure with a `Bool` field, and the derived instances
already compute that field with `&&`.

On the LRAT proof of 67 KB (lrat05), this takes the evaluator from 53.7
million steps to 18.4 million, and the check from 3.8 s to 1.9 s.

## Integers

Lean's kernel has no built-in `Int` arithmetic: `Int.add`, `Int.mul` and
the others are matches on `Int.ofNat n` and `Int.negSucc n` that end in
`Nat` operations, reached through `HAdd.hAdd`, `Add.add` and the
instances. The evaluator runs thirteen of them on values whose `Nat` field
is a literal: `Int.add`, `sub`, `mul`, `neg`, `ediv` and `emod` (`/` and
`%`), `tdiv`, `tmod`, `pow`, `subNatNat`, `negOfNat`, `natAbs` and `toNat`.
It takes the case of the definition that the arguments select and computes
its right-hand side with the kernel's `Nat` operations (`Tc::nat_op`, so
with its size limits). The result is the `Int.ofNat` or `Int.negSucc` value
that the right-hand side reduces to. For example, `Int.mul (ofNat m)
(negSucc n)` is `negOfNat (m * succ n)`, which is `0` or
`negSucc (m * (n + 1) - 1)`. The definitions are the same in Lean v4.30.0,
v4.34.0 and v4.36.0, and each operation is enabled only if its definition
matches one of them. Arguments that are not such values make the operation
its definition. Each argument is forced, as the definitions' matches force
them, with one exception: `Int.emod (ofNat m) n` is `ofNat (m % n.natAbs)`,
whose `n` the definition leaves unevaluated under `Int.ofNat`. If that `n`
is stuck, the evaluator gives up and `whnf` reduces the term itself.

On the coefficients of a product of 300 linear polynomials over `Int`,
computed as lists, the `Int` operations halve the evaluator's steps (8.4
to 4.6 million). With the lazy `List.map`, `zipWith` and `append` the check
goes from 0.55 s to 0.13 s.

## Class methods

Arithmetic in compiled code reaches its operation through a class method:
`x + y` is `HAdd.hAdd α α α inst x y`. `HAdd.hAdd` is a projection
function, `fun α β γ self => self.1`, and the instance is a closed term or
a variable bound to one, so `whnf` unfolds `HAdd.hAdd`, then the instance
(`instHAdd`), then `Add.add` and the next instance. That repeats at every
operation. A definition of that shape, `fun p₁ … pₖ self => self.i`, is
recognized when its value is looked at (`proj_fn_arity`; it is a property of
the term, so no version check is needed). Applied to more than `k`
arguments, the evaluator takes the value of `c p₁ … pₖ` and applies it to
the rest (`method`). That is the reduct `whnf` reaches after unfolding `c`
and projecting the field. The value is kept per argument thunks, for the
last 8 combinations of each method. The same thunk stands for the same term
in one environment, so a hit is that term's value again. When the
arguments' terms are known, the value is also shared through the closed
term `c p₁ … pₖ`. The test `eval-methods` applies `+` through 20 instances
built from a number (more than the 8 kept), an instance passed as an
argument and an instance whose field is computed.

On a 40 × 40 and a 60 × 60 integer matrix product mod 65521, the steps go
from 8.8 to 6.4 million and the evaluator's time from 0.55 to 0.49 s.

## Matches

Every `match` compiles to a matcher that unfolds to `casesOn`, or to the
sparse `casesOn` of matchers that leave out some constructors, and
`casesOn` unfolds to the recursor with minor premises that drop the
inductive hypotheses. A definition of that shape is recognized when its
value is looked at (`cases_shape`):

- It is `fun x₀ … xₖ₋₁ => I.rec a₀ … aₙ`, where `I.rec` is not `K`-like,
  has one motive and a minor premise per constructor, and takes exactly its
  arguments up to the major premise, a variable `xⱼ`.
- Each minor premise is `fun fields ihs extras => x_l fields`, applying an
  argument to the fields in order, or `fun fields ihs extras => z t₁ … tₙ`,
  applying one of the extra binders (the sparse form's `else`) to closed
  terms. The number of inductive hypotheses is read from the recursor's rule.

Applied to its arguments, with the major premise evaluated to a constructor,
it becomes that rule's minor premise body directly (`cases_n`): `x_l` applied
to the constructor's fields, or `z` applied to `t₁ … tₙ`, and then to the
arguments past the extra binders. Unfolding the definition, reducing the
recursor with the rule's right-hand side and beta-reducing the minor
premise gives the same term. It is a property of the definition's term, so
no version check is needed. Any other major premise makes it its
definition. The tests `eval-cases` and `eval434-cases` (with their false
twins) match on a three-constructor type with a recursive field, on a
`Nat` literal and a list with wildcards, on a structure, and on an `Option`
whose result is a function.

On the certificate session's `nonsingular-128`, the steps go from 84 to 54
million and the evaluator's time from 5.0 to 4.0 s. On lrat06 they go from
81 to 52 million steps (4.8 to 3.9 s). On `cartan_A7` they go from 65 to 42
million steps (3.8 to 3.1 s).

## Built-in operations of several Lean versions

The fingerprint table (`src/check/fingerprint_table.rs`, written by
`examples/fingerprints.rs`) holds the prelude definitions of the `Nat`,
`Array`, `List` and `DecidableEq` operations of Lean v4.36.0, v4.34.0 and
v4.30.0, each digest with the versions it comes from. An operation is
enabled only if every declaration it depends on matches one and the same
version. An operation that is only for some versions is enabled only if
that version is one of them. Before this, an export made
with v4.34.0 or v4.30.0 got no built-in `Nat.div`, `Nat.mod`, `Nat.gcd`,
`Nat.land` or `Nat.xor`, because `dite`, `ite` and a few others differ from
v4.36.0's. Literal division then ran in unary: the published planar-graph
result (doi:10.5281/zenodo.24467489) divides coordinates near 4·10⁸ and ran
out of memory.

## Tests

`xtask/src/kernel_cases/cases.rs` has 77 `eval*` cases. Each is a claim proved by
`Eq.refl`, so only reduction decides it, and nearly every one has a false
twin. The 27 `eval434-*` cases are exported from Lean v4.34.0, where the
`DecidableEq` fast paths apply. They cover:

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
  proof;
- `List.any`, `all`, `elem`, `filter` (lazily: later tests would divide by
  zero), `getLast?`, `foldl`, `reverse` and `eraseDups`, in v4.36.0 and
  v4.34.0, and `map`, `zipWith`, `append` and `length`;
- the `Int` operations on every combination of signs, zero divisors and
  values past 2^64;
- `DecidableEq` and `==` on lists of (subtype, `Bool`) pairs, equal and not,
  `Nodup`, `eraseDups` and `elem` on them; a cast over a `DecidableEq` proof
  (the erased proof is a `K`-like major premise), and the same over
  `Nat.decEq` in a fold, which is evaluated again keeping proofs; a value
  that holds a decision; and a pair that is an axiom, which stays stuck, as
  in Lean.

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

With the `List` and `DecidableEq` fast paths, on a second machine where
the previous build takes 40.3 s on lrat07, 41.7 s on php7 and 20.6 s on the
planar-graph result:

| | before | after |
|---|---|---|
| LRAT, 696 KB (lrat07) | 40.3 s, 1.1 GiB, 798 M steps | 13.0 s, 1.1 GiB, 236 M steps |
| pigeonhole, 796 KB (php7) | 41.7 s, 1.2 GiB | 14.3 s, 1.2 GiB |
| planar-graph result | 20.6 s, 216 MiB | 9.6 s, 118 MiB |

The next sizes still run out of 4 GiB, now within 35 to 70 s. Memory, not
time, bounds the curve now.

## Not done

- A hook in definitional equality (comparing two closed terms by evaluating
  both): `is_def_eq` still unfolds lazily and reaches the evaluator only
  through `whnf`.
- Compiling hot definitions to closures. The machine interprets the term DAG,
  at about 60 ns per step.
- Memory on the largest LRAT proofs: at 1.8 MB of LRAT the check passes
  4 GiB. The values that the checker's clause arrays keep alive grow about
  linearly with the proof.
- Fast paths for `ByteArray`, and for `decide` on `Fin` and `ZMod`.
