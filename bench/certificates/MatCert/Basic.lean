/-!
# Matrix product certificates, checked by the kernel

A certificate claims `A * B ≡ C (mod m)` for explicit integer matrices, with `m = 0`
meaning exact equality over `Int`. Matrices are lists of rows (`List (List Int)`), the
form the kernel reduces most directly: no `Array`, no well-founded recursion, only
structural recursion on lists and the `Nat`/`Int` operations.

* `MulEqMod m r k c A B C` is the statement: for every `i < r`, `j < c`,
  `m ∣ (∑ l < k, A i l * B l j) - C i j`, where `A i l` is the entry of row `i`, column `l`
  (`0` outside the list).
* `check m r k c A B C : Bool` is the checker. It computes each row of `A * B` as the
  combination `∑ l, A i l • (row l of B)` and compares it with the row of `C` modulo `m`.
* `check_sound : check m r k c A B C = true → MulEqMod m r k c A B C`.

Two statements are built on it:

* `InvertibleMod p n A`: some `B` has `A * B ≡ 1 (mod p)`; certified by the inverse
  (`invertibleMod_of_check`).
* `Nonsingular n A`: some `B` and `d ≠ 0` have `A * B = d • 1` over `Int`, so `A` is
  invertible over the rationals; certified by `B = adj A`, `d = det A`
  (`nonsingular_of_check`).

The proof of a certificate is `of_decide_eq_true (Eq.refl true)` for `check … = true`:
the kernel evaluates the checker on the literal matrices.
-/

namespace MatCert

abbrev Row := List Int
abbrev Mat := List Row

/-! ## The statement -/

/-- Entry `(i, j)` of `A`, `0` outside it. -/
def entry (A : Mat) (i j : Nat) : Int := (A.getD i []).getD j 0

/-- `sumTo n f = f 0 + f 1 + … + f (n - 1)`. -/
def sumTo : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => f 0 + sumTo n (fun l => f (l + 1))

/-- `A * B ≡ C (mod m)` for an `r × k` matrix `A` and a `k × c` matrix `B`
(`m = 0`: equal). -/
def MulEqMod (m : Int) (r k c : Nat) (A B C : Mat) : Prop :=
  ∀ i, i < r → ∀ j, j < c → m ∣ sumTo k (fun l => entry A i l * entry B l j) - entry C i j

/-- `d` times the `n × n` identity matrix. -/
def scalar (n : Nat) (d : Int) : Mat :=
  (List.range n).map fun i => (List.range n).map fun j => if i = j then d else 0

/-- The `n × n` identity matrix. -/
def identity (n : Nat) : Mat := scalar n 1

/-- `A` (read as an `n × n` matrix) has an inverse modulo `p`. -/
def InvertibleMod (p : Int) (n : Nat) (A : Mat) : Prop :=
  ∃ B, MulEqMod p n n n A B (identity n)

/-- `A` (read as an `n × n` matrix) is nonsingular: `A * B = d • 1` for some `B` and `d ≠ 0`. -/
def Nonsingular (n : Nat) (A : Mat) : Prop :=
  ∃ B d, d ≠ 0 ∧ MulEqMod 0 n n n A B (scalar n d)

/-! ## The checker -/

/-- `acc + a • b`, entrywise (as long as the shorter of the two). -/
def axpy (a : Int) : Row → Row → Row
  | x :: xs, y :: ys => (x + a * y) :: axpy a xs ys
  | _, _ => []

/-- `acc + ∑ l, xs[l] • bs[l]`. -/
def rowTimes : Row → Mat → Row → Row
  | x :: xs, b :: bs, acc => rowTimes xs bs (axpy x acc b)
  | _, _, acc => acc

/-- The two rows have the same length and agree modulo `m` entrywise. -/
def rowEqMod (m : Int) : Row → Row → Bool
  | x :: xs, y :: ys => (x - y) % m == 0 && rowEqMod m xs ys
  | [], [] => true
  | _, _ => false

/-- Row by row, `as * B ≡ cs (mod m)`, with rows of length `c`. -/
def rowsEqMod (m : Int) (c : Nat) (B : Mat) : Mat → Mat → Bool
  | a :: as, r :: rs => rowEqMod m (rowTimes a B (List.replicate c 0)) r && rowsEqMod m c B as rs
  | [], [] => true
  | _, _ => false

/-- The checker for `MulEqMod m r k c A B C`: shapes, then the product row by row. -/
def check (m : Int) (r k c : Nat) (A B C : Mat) : Bool :=
  A.length == r && A.all (·.length == k) && B.length == k && B.all (·.length == c) &&
    rowsEqMod m c B A C

/-! ## Soundness -/

theorem length_axpy (a : Int) : ∀ xs ys : Row, (axpy a xs ys).length = min xs.length ys.length
  | _ :: xs, _ :: ys => by simp [axpy, length_axpy a xs ys, Nat.succ_min_succ]
  | [], _ => by simp [axpy]
  | _ :: _, [] => by simp [axpy]

theorem getD_axpy (a : Int) : ∀ (xs ys : Row) (j : Nat), j < xs.length → j < ys.length →
    (axpy a xs ys).getD j 0 = xs.getD j 0 + a * ys.getD j 0
  | x :: xs, y :: ys, 0, _, _ => by simp [axpy]
  | x :: xs, y :: ys, j + 1, h₁, h₂ => by
    simp only [axpy, List.getD_cons_succ]
    exact getD_axpy a xs ys j (by simpa using h₁) (by simpa using h₂)
  | [], _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h => by simp at h

theorem rowTimes_spec (c : Nat) : ∀ (xs : Row) (bs : Mat) (acc : Row),
    xs.length ≤ bs.length → (∀ b ∈ bs, b.length = c) → acc.length = c →
    (rowTimes xs bs acc).length = c ∧
      ∀ j, j < c → (rowTimes xs bs acc).getD j 0 =
        acc.getD j 0 + sumTo xs.length (fun l => xs.getD l 0 * (bs.getD l []).getD j 0)
  | [], bs, acc, _, _, hacc => by
    cases bs <;> exact ⟨by simpa [rowTimes] using hacc, fun j _ => by simp [rowTimes, sumTo]⟩
  | _ :: _, [], _, h, _, _ => by simp at h
  | x :: xs, b :: bs, acc, hlen, hb, hacc => by
    have hb' : ∀ b' ∈ bs, b'.length = c := fun b' h => hb b' (List.mem_cons_of_mem _ h)
    have hbc : b.length = c := hb b List.mem_cons_self
    have hax : (axpy x acc b).length = c := by simp [length_axpy, hbc, hacc]
    have ih := rowTimes_spec c xs bs (axpy x acc b) (by simpa using hlen) hb' hax
    refine ⟨by simpa [rowTimes] using ih.1, fun j hj => ?_⟩
    simp only [rowTimes, List.length_cons, sumTo, List.getD_cons_zero, List.getD_cons_succ]
    rw [ih.2 j hj, getD_axpy x acc b j (by omega) (by omega)]
    simp only [Int.add_assoc]

theorem rowEqMod_spec (m : Int) : ∀ u v : Row, rowEqMod m u v = true →
    u.length = v.length ∧ ∀ j, j < u.length → m ∣ u.getD j 0 - v.getD j 0
  | x :: xs, y :: ys, h => by
    simp only [rowEqMod, Bool.and_eq_true, beq_iff_eq] at h
    have ih := rowEqMod_spec m xs ys h.2
    refine ⟨by simp [ih.1], fun j hj => ?_⟩
    cases j with
    | zero => exact Int.dvd_of_emod_eq_zero (by simpa using h.1)
    | succ j => simpa using ih.2 j (by simpa using hj)
  | [], [], _ => ⟨rfl, fun _ h => by simp at h⟩
  | [], _ :: _, h => by simp [rowEqMod] at h
  | _ :: _, [], h => by simp [rowEqMod] at h

theorem rowsEqMod_spec (m : Int) (c : Nat) (B : Mat) : ∀ as cs : Mat, rowsEqMod m c B as cs = true →
    ∀ i, i < as.length →
      rowEqMod m (rowTimes (as.getD i []) B (List.replicate c 0)) (cs.getD i []) = true
  | a :: as, r :: rs, h, i, hi => by
    simp only [rowsEqMod, Bool.and_eq_true] at h
    cases i with
    | zero => simpa using h.1
    | succ i => simpa using rowsEqMod_spec m c B as rs h.2 i (by simpa using hi)
  | [], _, _, _, hi => by simp at hi
  | _ :: _, [], h, _, _ => by simp [rowsEqMod] at h

theorem check_sound {m : Int} {r k c : Nat} {A B C : Mat} (h : check m r k c A B C = true) :
    MulEqMod m r k c A B C := by
  simp only [check, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hA, hAk⟩, hB⟩, hBc⟩, hrows⟩ := h
  intro i hi j hj
  have hrow := rowsEqMod_spec m c B A C hrows i (by omega)
  have hlenA : (A.getD i []).length = k := by
    have : A.getD i [] ∈ A := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < A.length by omega)]
      exact List.getElem_mem _
    exact hAk _ this
  have hspec := rowTimes_spec c (A.getD i []) B (List.replicate c 0) (by omega)
    (fun b hb => hBc b hb) (by simp)
  have hu := rowEqMod_spec m _ _ hrow
  have hd := hu.2 j (by omega)
  rw [hspec.2 j hj, hlenA] at hd
  simpa [entry, List.getElem?_replicate, hj] using hd

theorem entry_scalar {n : Nat} {d : Int} {i j : Nat} (hi : i < n) (hj : j < n) :
    entry (scalar n d) i j = if i = j then d else 0 := by
  simp [entry, scalar, List.getD_eq_getElem?_getD, hi, hj]

/-- An inverse modulo `p`, checked by the kernel, proves `InvertibleMod p n A`. -/
theorem invertibleMod_of_check {p : Int} {n : Nat} {A : Mat} (B : Mat)
    (h : check p n n n A B (identity n) = true) : InvertibleMod p n A :=
  ⟨B, check_sound h⟩

/-- `A * B = d • 1` with `d ≠ 0`, checked by the kernel, proves `Nonsingular n A`. -/
theorem nonsingular_of_check {n : Nat} {A : Mat} (B : Mat) (d : Int)
    (h : (d != 0 && check 0 n n n A B (scalar n d)) = true) : Nonsingular n A := by
  simp only [Bool.and_eq_true, bne_iff_ne] at h
  exact ⟨B, d, h.1, check_sound h.2⟩

end MatCert
