# Numeric certificates checked by the kernel

Big computational proofs often have the shape *an external program finds a witness, a
small verified checker inside Lean checks it*. For SAT this is LRAT: a solver writes the
proof and the verified LRAT checker of the standard library, run by the kernel, checks it
(benchmark **b** of `bench/kernel-compute/`). This note looks at the same pattern for
other kinds of certificates: what Lean 4 and Mathlib already have, how each is checked,
and the first format built here for `nitrolean`'s evaluator (`docs/kernel-compute.md`),
matrix certificates (`bench/certificates/`).

## How a certificate can be checked

There are three ways to turn a witness into a Lean proof:

- **Kernel reduction** (reflection): a checker `check : Cert → Bool` written in Lean, a
  theorem `check c = true → P`, and the proof `of_decide_eq_true (Eq.refl true)` (what
  `decide +kernel` makes), so the kernel evaluates `check c`. Only the kernel is
  trusted, and checking the proof means running the checker: this is the work
  `nitrolean`'s evaluator is for. Core Lean also has `eagerReduce`, which asks the
  kernel to reduce a term eagerly.
- **Native evaluation**: `native_decide` (`decide +native`) compiles the checker and runs
  it. Since Lean v4.29 each use adds a new axiom asserting the result
  ([v4.29.0 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.29.0/));
  v4.35 removed `Lean.ofReduceBool` and the kernel's support for it
  ([v4.35.0 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/)).
  Fast, but the compiler is trusted, and an exported proof contains an axiom that an
  independent checker can only take on faith.
- **Proof terms**: a tactic (`ring`, `norm_num`, `linarith`, `omega`) builds an ordinary
  proof from the witness. Nothing is evaluated by reduction except small leaves such as
  `Nat` literal arithmetic, but the terms grow with the witness.

What the kernel computes fast matters for the first one. Lean's kernel evaluates these
`Nat` operations on literals with GMP: `Nat.succ`, `add`, `sub`, `mul`, `div`, `mod`,
`gcd`, `pow`, `beq`, `ble`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight`
([`type_checker.cpp`](https://github.com/leanprover/lean4/blob/master/src/kernel/type_checker.cpp),
`reduce_nat`). Nothing else: `Int` operations reduce by matching on `Int.ofNat` /
`Int.negSucc` down to those `Nat` operations, and `Nat.log2`, `Nat.powMod`, `Array`
operations other than a few primitives, and well-founded recursion (`Acc.rec`) are
unfolded or are stuck. String literals are kernel literals.

## What exists

Sources: lean4 and mathlib4 `master` of November 2026 (Mathlib on `v4.37.0-rc1`); links
point to `master`. **K** = checked by kernel reduction, **N** = native evaluation,
**P** = proof term built by a tactic. *External* = the certificate can come from a
program outside Lean.

### Linear arithmetic and linear programming

| What | Where | How | External |
| --- | --- | --- | --- |
| `linarith`: Farkas combination of hypotheses | [`Linarith/Verification.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Linarith/Verification.lean), oracles [simplex](https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/Tactic/Linarith/Oracle/SimplexAlgorithm), [Fourier–Motzkin](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Linarith/Oracle/FourierMotzkin.lean) | P: the coefficients from the oracle are summed with lemmas and `ring1` proves the sum is zero | no (oracles are Lean code) |
| `nlinarith`: products of hypotheses, a degree 2 Positivstellensatz | [`Linarith/Preprocessing.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Linarith/Preprocessing.lean) | P, as `linarith` | no |
| `linear_combination e`: coefficients for an ideal membership or inequality | [`LinearCombination.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/LinearCombination.lean) | P: `ring1` | yes (the user's `e`) |
| `polyrith`: found `linear_combination` coefficients with Sage | [`Polyrith.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Polyrith.lean) | disabled: the Sage server it called was shut down | (was yes) |
| `omega` | [`Elab/Tactic/Omega`](https://github.com/leanprover/lean4/tree/master/src/Lean/Elab/Tactic/Omega), [`Init/Omega`](https://github.com/leanprover/lean4/tree/master/src/Init/Omega) | P, with small `decide` leaves | no |
| `grind`'s linear integer arithmetic, linarith and commutative ring modules | [`Init/Data/Int/Linear.lean`](https://github.com/leanprover/lean4/blob/master/src/Init/Data/Int/Linear.lean), [`Init/Grind/Ring/CommSolver.lean`](https://github.com/leanprover/lean4/blob/master/src/Init/Grind/Ring/CommSolver.lean), [`Init/Grind/Ordered/Linarith.lean`](https://github.com/leanprover/lean4/blob/master/src/Init/Grind/Ordered/Linarith.lean) | K: each derivation step is a theorem guarded by a Boolean `…_cert` over reified polynomials, closed by `eagerReduce (Eq.refl true)` | no (grind's own search) |
| `simp +arith` (`Nat.Linear`) | [`Init/Data/Nat/Internal/Linear.lean`](https://github.com/leanprover/lean4/blob/master/src/Init/Data/Nat/Internal/Linear.lean) | K, kernel-friendly `_k` variants | no |

There is no importer of LP solver output (a primal or dual solution, a Farkas vector for
thousands of constraints) as a kernel-checked certificate. `grind`'s reflective
certificates are the closest: they show the pattern works in core, but each is a small
step of one tactic run.

### Sum of squares and Positivstellensatz

- Mathlib has no sum-of-squares tactic; `nlinarith` is the nearest. A sum-of-squares
  tactic for Mathlib is an open pull request
  ([#42336](https://github.com/leanprover-community/mathlib4/pull/42336)).
- The [`leanprover/sos`](https://github.com/leanprover/sos) package: reifies the goal,
  calls the CSDP solver (external), rounds the Gram matrix to rationals and decomposes it
  (LDLᵀ); the certificate is checked by `decide +kernel` (K) against `Certificate.checks`,
  with `native_decide` in some tests.
- Elsewhere: Coq's `psatz` (micromega) calls CSDP and checks the certificate by
  reflection ([manual](https://rocq-prover.org/doc/master/refman/addendum/micromega.html));
  [ValidSDP](https://github.com/validsdp/validsdp) checks SDP output by reflection, with a
  floating-point Cholesky; HOL Light's
  [`REAL_SOS`](https://github.com/jrh13/hol-light/blob/master/Examples/sos.ml) and
  Isabelle's [`sos`](https://isabelle.in.tum.de/library/HOL/HOL-Library/Sum_of_Squares.html)
  replay the decomposition by inference.

### Interval arithmetic and numeric bounds

- Mathlib's `inclusion` / `dyadic_interval` tactic
  ([`Tactic/Inclusion`](https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/Tactic/Inclusion)):
  dyadic interval enclosures of `exp`, `log`, `sqrt` and rationals, reified to a Boolean
  check. Default: a compiled pre-check, then K; `+kernel` is K only; `+native` is N.
- Bounds on π ([`Analysis/Real/Pi/Bounds.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Real/Pi/Bounds.lean)):
  a list of rationals (external, from a script quoted in the file), each step closed by
  `norm_num1` (P).
- [`girving/interval`](https://github.com/girving/interval): software floating-point
  intervals and boxes; its `interval` tactic uses `native_decide` (N), some library lemmas
  `decide +kernel`
  ([`Tactic/Interval.lean`](https://github.com/girving/interval/blob/master/Interval/Tactic/Interval.lean)).
- [LeanCert](https://github.com/alerad/leancert): rational, dyadic and affine interval
  arithmetic with root and optimisation certificates and a Python front end that searches
  for them (external); the default mode is N, with a `decide +kernel` mode (K).
- Elsewhere: Coq's [`interval`](https://coqinterval.gitlabpages.inria.fr/) tactic, by
  reflection with `vm_compute`.

### Modular arithmetic and number theory

| What | Where | How | External |
| --- | --- | --- | --- |
| `Nat.Prime n` by trial division, composites by a factor | [`NormNum/Prime.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/NormNum/Prime.lean) | P with K leaves (`Nat.ble`, `Nat.mod` on literals); deep terms above about 25 bits | no |
| `primality`: Pratt (Lucas) certificates | [`Tactic/Primality`](https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/Tactic/Primality), [`Primality/Lucas.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Primality/Lucas.lean), theorem [`LucasPrimality.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/LucasPrimality.lean) | K: `lucasCheck p a fac : Bool` with a kernel-friendly `powMod`, closed by `Eq.refl true` | yes (`cert := .witnesses […]`), else found by Lean code |
| Pocklington certificates | — | not in Mathlib (a TODO of the `primality` tactic) | — |
| `decide` on `Nat.Prime` | [`Nat/Prime/Defs.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Nat/Prime/Defs.lean) | K, for small values only | no |
| `a ^ b % m`, numerals modulo the characteristic | [`NormNum/PowMod.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/NormNum/PowMod.lean), [`ReduceModChar.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/ReduceModChar.lean) | P | no |
| `gcd`, Bézout coefficients | [`NormNum/GCD.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/NormNum/GCD.lean) | P: the coefficients are checked as `x * a = y * b + 1` by literal arithmetic | no |
| Chinese remainder theorem | [`Data/Nat/ChineseRemainder.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Nat/ChineseRemainder.lean) | definitions and lemmas, no certificate tactic | — |

The kernel's `Nat` acceleration makes single modular steps cheap, but `Nat.powMod` is
not accelerated; the `primality` tactic works around it, and a core pull request to speed
up its kernel reduction is open
([lean4#15167](https://github.com/leanprover/lean4/pull/15167)). Coq's
[CoqPrime](https://github.com/thery/coqprime) checks Pocklington and elliptic-curve
certificates (from its own generator or Primo) by reflection.

### Linear algebra

- Determinants and equalities of small explicit integer matrices are proved by `decide`
  (K), e.g. the Cartan matrices
  ([`Matrix/Cartan/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/LinearAlgebra/Matrix/Cartan/Basic.lean)):
  `Matrix.det` unfolds to a sum over permutations, so this only works for tiny sizes.
  These are among the Mathlib declarations of benchmark **c**.
- `Matrix.inv_eq_left_inv (h : B * A = 1) : A⁻¹ = B`
  ([`NonsingularInverse.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean))
  is the lemma for a supplied inverse, but nothing proves `h` for a large matrix except
  `decide` or `norm_num` on the Mathlib `Matrix` type.
- No Lean 4 project was found that checks inverse, determinant, rank, LU or normal form
  (Smith, Hermite) certificates by kernel reduction (a code search, not exhaustive).

### SAT and the native route

- `bv_decide` runs CaDiCaL and checks its LRAT proof with the verified checker of
  [`Std.Tactic.BVDecide.LRAT`](https://github.com/leanprover/lean4/tree/master/src/Std/Tactic/BVDecide/LRAT),
  natively (N).
- [LRAT-Catcher](https://github.com/leansolving/lrat-catcher) imports DIMACS and LRAT files
  as theorems with the same verified checker, natively by default and by the kernel in its
  `+kernel` mode (K), which replaces the parts of the checker that do not reduce in the
  kernel (well-founded recursion, `HashMap`, `Array.map`) by `List` code.
- Mathlib bans `native_decide`
  ([linter](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Linter/DeprecatedSyntaxLinter.lean)).

### Summary

Kernel-checked certificate checkers exist for SAT (LRAT-Catcher's kernel mode), Pratt
primality, dyadic intervals, sum of squares (a package) and as internal steps of
`grind`. Native evaluation is the default in the SAT, interval and SOS packages, for speed.
Nothing imports linear-algebra witnesses. Matrix certificates are the cheapest to add:
the checker is a few list functions over `Int`, the soundness proof is short, they are
generated by elimination in any language, and their size is easy to scale. They also
exercise exactly what a kernel evaluator needs to be good at for numeric certificates:
`Int` arithmetic, long lists of literals, and modular reduction.

## Matrix certificates (`bench/certificates/`)

See `bench/certificates/README.md`.
