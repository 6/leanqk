# Matrix certificates checked by the kernel (`MatCert`)

A small Lean package (core Lean only, toolchain pinned in `lean-toolchain`: v4.34.0) for
importing linear-algebra witnesses as theorems, and a benchmark of growing certificates for
the checkers of `bench/kernel-compute/`. The survey behind the choice of format is
`docs/certificates.md`.

## The checker

`MatCert/Basic.lean`:

- `MulEqMod m r k c A B C`: for all `i < r`, `j < c`,
  `m ∣ (∑ l < k, A i l * B l j) - C i j`. Matrices are `List (List Int)`, entry
  `A i j` is `0` outside the lists, and `m = 0` means equality over `Int`.
- `check m r k c A B C : Bool`: checks the shapes, then computes each row of `A * B`
  as `∑ l, A i l • (row l of B)` and compares it with the row of `C` modulo `m`. Only
  structural recursion on lists and `Int` arithmetic, so the kernel reduces it.
- `check_sound : check m r k c A B C = true → MulEqMod m r k c A B C`.
- Two statements on top of it:
  - `InvertibleMod p n A := ∃ B, MulEqMod p n n n A B (identity n)`, proved from an
    inverse by `invertibleMod_of_check`;
  - `Nonsingular n A := ∃ B d, d ≠ 0 ∧ MulEqMod 0 n n n A B (scalar n d)` (so `A` is
    invertible over ℚ), proved from the adjugate and the determinant by
    `nonsingular_of_check`.

The axioms of the soundness theorems are `propext` and `Quot.sound`. A certificate's proof
is `invertibleMod_of_check B (of_decide_eq_true (Eq.refl true))`, the term
`decide +kernel` makes; for example

```lean
example : MatCert.InvertibleMod 7 2 [[2, 1], [1, 1]] :=
  MatCert.invertibleMod_of_check [[1, 6], [6, 2]] (by decide +kernel)
```

`MatCert/Cmd.lean` adds `mat_cert name "file"`, which reads a certificate file and adds the
theorem, building the term directly as an `Expr` (integer literals as `Int.ofNat` /
`Int.negSucc` of raw `Nat` literals) in the way `bench/kernel-compute`'s `kernel_lrat` does.

## The certificates

`gen.py` (run with `python3 -I`) makes them, from splitmix64 with a given seed, so they are
synthetic and fully determined by the arguments:

- `inverse P N SEED`: a random `N × N` matrix with entries in `[0, P)` and its inverse
  modulo `P` (Gauss–Jordan). The series uses `P = 65521`, the largest prime below 2^16, so
  all intermediate sums fit a machine word.
- `nonsingular N BOUND SEED`: a random `N × N` matrix with entries in `[-BOUND, BOUND]`, its
  determinant `d` and adjugate `B` (fraction-free Gauss–Jordan), `A * B = d • 1`. The
  series uses `BOUND = 9`; the adjugate entries have hundreds of digits for `N = 128`, so
  this series is about big integers.
- `--corrupt` changes the last entry of `B` after checking: the checkers must reject those.

Every certificate is checked by multiplication in `gen.py` before it is written.
`data/certificates.tsv` lists the series with each certificate's SHA-256. The kernel work
is about `N³` multiply-adds of `Int`s.

`make-exports.sh` builds the package, makes each certificate, checks its SHA-256, states it
with `mat_cert` and exports the theorem's closure with lean4export (the commit for v4.34.0
pinned in `bench/kernel-compute/common.sh`), into `bench/kernel-compute/out/certificates/`
with a `manifest.tsv`. Certificates with `N ≤ 16` are added with Lean's kernel check on;
the larger ones with `debug.skipKernelTC true`. Every export contains the closure of the
checker and its soundness proof (about 5 MB, `inverse-1`).

```sh
bench/kernel-compute/build-checkers.sh
bench/certificates/make-exports.sh
bench/kernel-compute/measure.sh --out out/cert-measurements.tsv bench/kernel-compute/out/certificates/*.ndjson
```

## Results

See the section *Matrix certificates* of `docs/certificates.md`.
