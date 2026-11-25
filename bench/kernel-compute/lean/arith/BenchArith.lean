/-
Arithmetic checked by kernel computation on Mathlib definitions, at growing
sizes: each theorem's proof is `of_decide_eq_true (Eq.refl true)`, so a
checker has to evaluate the `Decidable` instance of its statement to `isTrue`.
Every statement is a classical fact (the answers are not computed here):

* `cartan_A n`: the determinant of the Cartan matrix of type Aₙ is n + 1
  (Laplace expansion over the n! permutations);
* `fermat p`: 3 ^ (p - 1) = 1 in ZMod p, for primes p (Fermat's little theorem);
* `qnr p`: no x in ZMod p has x² = -1, for primes p ≡ 3 (mod 4);
* `prime p`: `Nat.Prime p`, by Mathlib's trial-division instance;
* `sumsq n`: ∑_{i<n} i² = (n-1)n(2n-1)/6, over `Finset.range`.

Lean's own kernel is not run on them (`debug.skipKernelTC`): `unchecked_decide`
writes the proof term without asking the elaborator or the kernel to evaluate
it, as `lrat_reflect +kernel` does. The smallest of each family is also added
at a small size with the kernel check on (the `_checked` theorems), to confirm that Lean's
kernel accepts the same term.
-/
import Mathlib

open Lean Elab Tactic Meta

/-- Close `p` with `of_decide_eq_true (Eq.refl true)`, without evaluating it. -/
elab "unchecked_decide" : tactic => do
  let g ← getMainGoal
  let p ← g.getType
  let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
  let rfl := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  g.assign (mkApp3 (mkConst ``of_decide_eq_true) p inst rfl)

namespace BenchArith

theorem cartan_A3_checked : (CartanMatrix.A (Fin 3)).det = 4 := by decide +kernel
theorem fermat_31_checked : (3 : ZMod 31) ^ 30 = 1 := by decide +kernel
theorem qnr_31_checked : ∀ x : ZMod 31, x ^ 2 ≠ -1 := by decide +kernel
theorem prime_101_checked : Nat.Prime 101 := by decide +kernel
theorem sumsq_30_checked : ∑ i ∈ Finset.range 30, i ^ 2 = 8555 := by decide +kernel

set_option debug.skipKernelTC true

theorem cartan_A4 : (CartanMatrix.A (Fin 4)).det = 5 := by unchecked_decide
theorem cartan_A5 : (CartanMatrix.A (Fin 5)).det = 6 := by unchecked_decide
theorem cartan_A6 : (CartanMatrix.A (Fin 6)).det = 7 := by unchecked_decide
theorem cartan_A7 : (CartanMatrix.A (Fin 7)).det = 8 := by unchecked_decide
theorem cartan_A8 : (CartanMatrix.A (Fin 8)).det = 9 := by unchecked_decide
theorem cartan_A9 : (CartanMatrix.A (Fin 9)).det = 10 := by unchecked_decide

theorem fermat_101 : (3 : ZMod 101) ^ 100 = 1 := by unchecked_decide
theorem fermat_1009 : (3 : ZMod 1009) ^ 1008 = 1 := by unchecked_decide
theorem fermat_10007 : (3 : ZMod 10007) ^ 10006 = 1 := by unchecked_decide
theorem fermat_100003 : (3 : ZMod 100003) ^ 100002 = 1 := by unchecked_decide
theorem fermat_1000003 : (3 : ZMod 1000003) ^ 1000002 = 1 := by unchecked_decide

theorem qnr_103 : ∀ x : ZMod 103, x ^ 2 ≠ -1 := by unchecked_decide
theorem qnr_1019 : ∀ x : ZMod 1019, x ^ 2 ≠ -1 := by unchecked_decide
theorem qnr_10007 : ∀ x : ZMod 10007, x ^ 2 ≠ -1 := by unchecked_decide
theorem qnr_100003 : ∀ x : ZMod 100003, x ^ 2 ≠ -1 := by unchecked_decide

theorem prime_1009 : Nat.Prime 1009 := by unchecked_decide
theorem prime_10007 : Nat.Prime 10007 := by unchecked_decide
theorem prime_100003 : Nat.Prime 100003 := by unchecked_decide
theorem prime_1000003 : Nat.Prime 1000003 := by unchecked_decide

theorem sumsq_100 : ∑ i ∈ Finset.range 100, i ^ 2 = 328350 := by unchecked_decide
theorem sumsq_1000 : ∑ i ∈ Finset.range 1000, i ^ 2 = 332833500 := by unchecked_decide
theorem sumsq_10000 : ∑ i ∈ Finset.range 10000, i ^ 2 = 333283 * 1000000 + 335000 := by unchecked_decide

end BenchArith
