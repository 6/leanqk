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

The first format beyond SAT: `A * B ≡ C (mod m)` for explicit integer matrices, checked
by the kernel. The package is `bench/certificates/` (its README has the details):

- the statement `MulEqMod m r k c A B C` (`m = 0`: equality over `Int`), and on top of it
  `InvertibleMod p n A` (an inverse modulo `p` exists) and `Nonsingular n A`
  (`A * B = d • 1` with `d ≠ 0`, so `A` is invertible over ℚ);
- the checker `check : Int → Nat → Nat → Nat → Mat → Mat → Mat → Bool` on
  `List (List Int)`, computing each row of `A * B` as a combination of the rows of `B`;
- `check_sound`, proved in core Lean (axioms `propext`, `Quot.sound`);
- `cargo xtask matcert`, which makes seeded synthetic
  certificates of any size (inverses modulo 65521: machine-word arithmetic; adjugates with
  their determinants: big integers), states them with the `mat_cert` command, exports
  them, runs the checkers and tabulates the results.

Why this one first. The checker is a few list functions and the soundness proof is short;
witnesses come from elimination in any language; the size scales smoothly (`n³` kernel
multiply-adds). On its own, checking a product costs as much as computing an inverse, so
the format pays off through the statements built on it, whose witnesses are what is hard
to find or what the statement needs: nonsingularity of an integer matrix (from an
adjugate), rank lower bounds (an invertible `r × r` submatrix modulo a prime proves rank
`≥ r` over ℚ; a small extension of `InvertibleMod`), and the linear-algebra parts of LP and
sum-of-squares certificates, which are matrix identities of the same shape
(`yᵀA = c`, `Q = LDLᵀ`). The determinant itself is not certified (`A * adj A = d • 1` also
holds for `d = 0` and does not pin `d` down); with Mathlib, `Matrix.det` would follow from
an LU factorisation checked the same way.

### Results

12-core aarch64 Linux, 95 GB, one run each, with the limits of `cargo xtask kc measure` (60 s wall clock,
4 GiB resident), plus 600 s runs: nitrolean where it timed out, and leanchecker on the two
`n = 64` exports with a 32 GiB limit. Checkers as in `bench/kernel-compute/README.md`:
nitrolean at the commit that added this benchmark (no change to the checker itself),
leanchecker of Lean v4.36.0, gruszka `43d2d12` (susz 0.4.0), nano-lean `b5602a4`. Wall time
and peak resident memory in MiB; `oom` is over 4 GiB, `timeout` over 60 s. Every export
contains the checker's closure (5.05 MB, `inverse-1`); export sizes are in the manifest
`cargo xtask matcert exports` writes (37.6 MB for `inverse-512`).

| export | n | certificate bytes | nitrolean | leanchecker | gruszka | nano-lean |
| --- | ---: | ---: | --- | --- | --- | --- |
| inverse-1 | 1 | 28 | 0.10 s, 17 | 0.33 s, 113 | 0.01 s, 46 | 0.05 s, 52 |
| inverse-4 | 4 | 202 | 0.10 s, 17 | 0.35 s, 113 | 0.01 s, 46 | 0.04 s, 53 |
| inverse-8 | 8 | 760 | 0.10 s, 17 | 0.36 s, 124 | 0.01 s, 49 | 0.04 s, 59 |
| inverse-16 | 16 | 3 007 | 0.13 s, 17 | 0.64 s, 230 | 0.04 s, 71 | 0.07 s, 83 |
| inverse-32 | 32 | 11 949 | 0.32 s, 21 | 3.61 s, 992 | 0.28 s, 237 | 0.21 s, 294 |
| inverse-32-corrupt | 32 | 11 949 | rejected | rejected | rejected | rejected |
| inverse-64 | 64 | 47 750 | 1.80 s, 28 | oom; 33.4 s, 6 832 at 600 s | 3.40 s, 1 072 | 1.57 s, 1 903 |
| inverse-128 | 128 | 191 114 | 14.4 s, 69 | oom | 31.1 s, 1 234 | oom |
| inverse-256 | 256 | 764 095 | timeout; 130.7 s, 192 at 600 s | oom | timeout | oom |
| inverse-512 | 512 | 3 056 762 | timeout; timeout at 600 s | oom | timeout | oom |
| nonsingular-4 | 4 | 126 | 0.10 s, 16 | 0.34 s, 112 | 0.01 s, 44 | 0.04 s, 51 |
| nonsingular-8 | 8 | 726 | 0.11 s, 16 | 0.37 s, 124 | 0.01 s, 49 | 0.04 s, 55 |
| nonsingular-16 | 16 | 5 401 | 0.13 s, 19 | 0.65 s, 226 | 0.04 s, 68 | 0.07 s, 85 |
| nonsingular-32 | 32 | 44 813 | 0.35 s, 25 | 3.37 s, 940 | 0.23 s, 223 | 0.20 s, 280 |
| nonsingular-32-corrupt | 32 | 44 813 | rejected | rejected | rejected | rejected |
| nonsingular-64 | 64 | 383 580 | 2.15 s, 29 | oom; 27.5 s, 6 075 at 600 s | 3.16 s, 1 005 | 1.61 s, 1 479 |
| nonsingular-128 | 128 | 3 334 160 | 16.4 s, 75 | oom | 33.0 s, 1 257 | oom |

All four checkers accept every certificate they finish and reject both corrupted ones.
The kernel work is `n³` multiply-adds: 2.1 million for `n = 128`, 16.8 million for
`n = 256`. nitrolean's time grows with it (14.4 s → 130.7 s from 128 to 256, about 13
million evaluator steps a second) with little memory (192 MiB at `n = 256`). gruszka is about
twice as slow and uses 1.2 GiB at `n = 128`; nano-lean and leanchecker run out of 4 GiB at
`n = 128` and `n = 64`. Lean's kernel needs 6.8 GiB for `n = 64`. With the evaluator
off (`NITROLEAN_EVAL=0`), nitrolean takes 24.2 s and 3.2 GiB for `inverse-64` (1.80 s with
it) and 21.5 s and 3.2 GiB for `nonsingular-64` (2.15 s).

The two series cost about the same per multiply-add, although the adjugate entries have
hundreds of digits at `n = 128` (inverse-128: 213 million evaluator steps, 13.9 s;
nonsingular-128: 244 million, 16.8 s): the time is in the steps around each
operation, not in the arithmetic.

### What the evaluator spends its time on

From `nitrolean check --stats` and `NITROLEAN_EVAL_PROFILE=1` on `inverse-128`,
`inverse-256`, `nonsingular-64` and `nonsingular-128`: every evaluator call is answered
(nothing stuck, too deep, over the limit or evaluated again), and the evaluator is almost
all of the time (133.7 s of 133.9 s for `inverse-256`). It takes about 100 steps per
multiply-add `acc + a * b`, in every export. The constants reached most for `inverse-256`
(1.68 billion steps, 16.8 million multiply-adds), as reaches per multiply-add:

| constant | per multiply-add | from |
| --- | ---: | --- |
| `Int.rec`, `Int.casesOn` | 4 + 4 | matching both arguments of `Int.add` and `Int.mul` |
| `List.rec` | 3 | the structural recursion of `axpy` and `rowTimes` (compiled with `brecOn`) |
| `HAdd.hAdd`, `Add.add`, `HMul.hMul`, `Mul.mul` | 2 each | the instance chain from `+`, `*` to `Int.add`, `Int.mul` |
| `List.cons` | 2 | the rows built by `axpy` |
| `MatCert.axpy._sparseCasesOn_1`, `axpy.match_1` | 2 + 1 | the compiled `match` of `axpy` |
| `Int.ofNat`, `Int.add.match_1` | 2 + 2 | rebuilding the result |
| `PProd.mk` | 1 | the `below` tuples of `brecOn` |

With negative entries (`nonsingular-128`, 244 million steps), `Int.add` of mixed signs adds
`Int.subNatNat`, `Int.negOfNat`, `Int.negSucc` and `Nat.rec` / `Nat.casesOn` on literals
(2.2 million each, plus 3.6 million `Nat.succ`): `Int.negOfNat` matches its argument with
`Nat.casesOn`, which takes a literal apart into `Nat.succ`.

The evaluator fast paths that would help most, in order:

1. **`Int` arithmetic on literals.** Treat `Int.ofNat n` / `Int.negSucc n` with literal `n`
   as one signed literal (a word, or a big integer), and evaluate `Int.add`, `Int.sub`,
   `Int.mul`, `Int.neg`, `Int.emod`, `Int.ediv`, `Int.decEq` and the order tests on them
   in one step, the way `Nat` literal arithmetic is evaluated. This replaces the `Int.rec`,
   `Int.casesOn`, `match_1`, `Int.ofNat` and, for mixed signs, the `subNatNat` /
   `negOfNat` / `Nat.casesOn` steps: by the counts above, about half of all steps. Lean's
   kernel has no `Int` acceleration either, so this is where nitrolean can be faster than
   Lean on every numeric certificate stated over `Int` (and `ZMod`, `Rat`, matrices
   over `ℤ`).
2. **The arithmetic instance chain.** `HAdd.hAdd Int Int Int (instHAdd …)` → `Add.add` →
   `Int.add` is unfolded on every operation (8 reaches per multiply-add); resolving the chain
   once for a known instance (as part of 1, for `Int` and `Nat`) removes it.
3. **Structural recursion compiled with `brecOn`.** `List.rec`, `PProd.mk`, the
   `_sparseCasesOn` and `match_1` auxiliaries cost about 10 steps per list element. A
   direct rule for `brecOn` (the recursive call evaluated where the `below` tuple is
   projected, without building the tuple), or evaluating the definition through its
   compiled `match` when the major premise is a constructor, would cut most of them.
   Every kernel-reducible checker written with ordinary pattern matching on lists (this one,
   LRAT-Catcher's kernel mode) goes through this.
4. **Packed literal lists.** A `List Int` (or `Array Int`) literal could be held as a vector
   of literals, read lazily as `List.cons` cells. Not a bottleneck here (192 MiB for the
   131 072 entries of `A` and `B` at `n = 256`), so lower priority; modular reduction is not one
   either, as this checker reduces once per entry.

Exports to reproduce these: `cargo xtask matcert exports --only inverse-256,nonsingular-128`.
