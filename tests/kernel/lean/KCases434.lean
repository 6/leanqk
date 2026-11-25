/-! Valid source of the kernel test cases built with Lean v4.34.0, for the
evaluator's fast paths that are only for versions before v4.36.0 (where
`Decidable` is the inductive type with `isTrue` and `isFalse`). Every
statement is proved by `sorry`; kernel-cases replaces the proof by `Eq.refl`. -/

namespace K34

-- Pairs of a subtype and a `Bool`, the literals of the LRAT checker.
abbrev Pos := {x : Nat // 0 < x}
def ev_pos (n : Nat) : Pos := ⟨n + 1, Nat.succ_pos n⟩
def ev_lits (n : Nat) : List (Pos × Bool) :=
  (List.range n).map fun i => (ev_pos (i % 7), i % 3 == 0)

theorem ev_deceq : decide (ev_lits 30 = ev_lits 30) = true := sorry
theorem ev_deceq_wrong : decide (ev_lits 30 = ev_lits 31) = true := sorry
theorem ev_deceq_ne : decide ((ev_pos 3, true) = (ev_pos 3, false)) = false := sorry
theorem ev_deceq_ne_wrong : decide ((ev_pos 3, true) = (ev_pos 4, true)) = true := sorry
theorem ev_beq : ((ev_lits 40).filter (· == (ev_pos 2, false))).length = 4 := sorry
theorem ev_beq_wrong : ((ev_lits 40).filter (· == (ev_pos 2, false))).length = 5 := sorry
theorem ev_nodup : decide (ev_lits 8).Nodup = true := sorry
theorem ev_nodup_wrong : decide (ev_lits 9).Nodup = true := sorry
theorem ev_dedup : (ev_lits 40).eraseDups.length = 14 := sorry
theorem ev_dedup_wrong : (ev_lits 40).eraseDups.length = 13 := sorry
theorem ev_elem : ((ev_lits 20).elem (ev_pos 5, true), (ev_lits 20).elem (ev_pos 7, true)) = (true, false) := sorry
theorem ev_elem_wrong : (ev_lits 20).elem (ev_pos 7, true) = true := sorry

-- Decisions whose proof is needed after all: a cast over it (a `K`-like
-- major premise), and a value holding a decision that is read back.
def ev_cast (a b : Nat) : Nat :=
  if h : (a, true) = (b, true) then cast (congrArg (fun _ => Nat) h) (a + 1) else 0
theorem ev_cast_ok : decide (ev_cast 4 4 = 5) = true := sorry
theorem ev_cast_wrong : decide (ev_cast 4 4 = 0) = true := sorry
def ev_hold (a b : Nat) : Option (Decidable ((a, true) = (b, true))) :=
  let d := decEq (a, true) (b, true)
  match d with
  | isTrue _ => some d
  | isFalse _ => none
def ev_hold_n (a b : Nat) : Nat :=
  match ev_hold a b with
  | some (isTrue _) => 1
  | some (isFalse _) => 2
  | none => 0
theorem ev_hold_ok : ev_hold 2 2 = some (isTrue rfl) := sorry
theorem ev_hold_wrong : ev_hold 2 2 = none := sorry
theorem ev_hold_n_ok : ev_hold_n 2 2 + ev_hold_n 2 3 = 1 := sorry
theorem ev_hold_n_wrong : ev_hold_n 2 2 + ev_hold_n 2 3 = 3 := sorry

-- A pair that is not a constructor: the fast paths leave it to the
-- definition, and the comparison is stuck, as in Lean's kernel.
axiom ev_ax : Pos × Bool
theorem ev_ax_eq : [ev_ax].elem ev_ax = true := sorry

-- `List` operations.
theorem ev_lists :
    ((List.range 50).any (· == 49), (List.range 50).all (· < 49),
      ((List.range 50).filter (· % 7 == 0)).getLast?,
      (List.range 50).foldl (· + ·) 0, (List.range 5).reverse) =
    (true, false, some 49, 1225, [4, 3, 2, 1, 0]) := sorry
theorem ev_lists_wrong : (List.range 50).foldl (· + ·) 0 = 1224 := sorry
theorem ev_filter_lazy : ((List.range 10).filter (fun i => i == 0 || 10 / i > 2)).head? = some 0 := sorry
theorem ev_filter_lazy_wrong : ((List.range 10).filter (fun i => i == 0 || 10 / i > 2)).head? = some 1 := sorry

end K34
