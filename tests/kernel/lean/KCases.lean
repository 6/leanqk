/-
Source for the base exports used by `gen.py`. Every declaration here is valid;
`gen.py` exports the closure of a few of them and applies one mutation per case.
Statements proved by `sorry` are only there to give a well-typed statement; the
generator replaces the proof.
-/
set_option autoImplicit false
set_option linter.unusedVariables false

namespace K

/-! Structure eta and unit-like eta -/
structure U where
structure UP (α : Type) where
theorem U.uniq (a b : U) : a = b := rfl
theorem UP.uniq (a b : UP Nat) : a = b := rfl
theorem prod_eta (p : Nat × Nat) : p = (p.1, p.2) := rfl

/-- One constructor, recursive: structure-like in shape, but no eta. -/
inductive R : Type where
  | mk : R → R
noncomputable def R.get (x : R) : R := R.rec (motive := fun _ => R) (fun r _ => r) x
theorem R.eta (x : R) : x = R.mk (R.get x) := by cases x; rfl

/-- One constructor with an index: no eta. -/
inductive V : Nat → Type where
  | mk : Nat → V 0
def V.get {n : Nat} : V n → Nat
  | .mk a => a
theorem V.eta (x : V 0) : x = V.mk (V.get x) := by cases x; rfl

/-- Zero fields with an index: not unit-like. -/
inductive W : Nat → Type where
  | mk : W 0
theorem W.uniq (a b : W 0) : a = b := by cases a; cases b; rfl

/-- A plain structure, used for metadata and projection mutations. -/
structure S where
  x : Nat
  y : Bool
theorem S.eta (s : S) : s = S.mk s.x s.y := rfl

/-! Positivity: built unsafe so Lean emits the recursors, then flipped to safe. -/
unsafe inductive Neg : Type where
  | mk : (Neg → Nat) → Neg
unsafe inductive NonStrict : Type where
  | mk : ((NonStrict → Nat) → Nat) → NonStrict
unsafe inductive NegNested : Type where
  | mk : List (NegNested → Nat) → NegNested
structure Wrap (α : Type) where
  f : α → Nat
unsafe inductive NegWrap : Type where
  | mk : Wrap NegWrap → NegWrap
mutual
unsafe inductive NegA : Type where
  | mk : (NegB → Nat) → NegA
unsafe inductive NegB : Type where
  | mk : NegA → NegB
end
mutual
unsafe inductive NegNA : Type where
  | mk : List NegNB → NegNA
unsafe inductive NegNB : Type where
  | mk : (NegNA → Bool) → NegNB
end
/-- Positive control cases. -/
inductive PosNested : Type where
  | mk : List (Nat → PosNested) → PosNested
mutual
inductive PosA : Type where
  | nil : PosA
  | mk : List PosB → PosA
inductive PosB : Type where
  | mk : (Nat → PosA) → PosB
end

/-! Mutual blocks -/
mutual
inductive MA (α : Type) : Type where
  | nil : MA α
  | cons : α → MB α → MA α
inductive MB (α : Type) : Type where
  | cons : α → MA α → MB α
end
mutual
inductive MU.{u} (α : Type u) : Type u where
  | nil : MU α
  | cons : α → MV α → MU α
inductive MV.{u} (α : Type u) : Type u where
  | cons : α → MU α → MV α
end

/-! Elimination from Prop -/
inductive P2 : Prop where
  | a | b
inductive Ex : Prop where
  | mk : Nat → Ex
/-! Universe levels -/
theorem lp.{u} (α : Sort u) (a : α) : a = a := rfl

/-! Quotients -/
theorem q_lift_mk_q {r : Nat → Nat → Prop} (f : Nat → Nat) (h : ∀ a b, r a b → f a = f b)
    (a : Nat) (_q : Quot r) : Quot.lift f h (Quot.mk r a) = f a := rfl
theorem q_lift_mk_fun_q {r : Nat → Nat → Prop} (f : Nat → Nat → Nat)
    (h : ∀ a b, r a b → f a = f b) (a c : Nat) (_q : Quot r) :
    Quot.lift f h (Quot.mk r a) c = f a c := rfl
theorem q_lift_var {r : Nat → Nat → Prop} (f : Nat → Nat) (h : ∀ a b, r a b → f a = f b)
    (q : Quot r) (a : Nat) : Quot.lift f h q = f a := sorry
theorem q_mk_rel {r : Nat → Nat → Prop} (a b : Nat) (h : r a b) :
    Quot.mk r a = Quot.mk r b := Quot.sound h
theorem q_ind_mk {r : Nat → Nat → Prop} (p : Quot r → Prop) (h : ∀ a, p (Quot.mk r a))
    (a : Nat) : Quot.ind h (Quot.mk r a) = h a := rfl

/-! Proof irrelevance -/
theorem pi_fun (p : Nat → Prop) (f g : ∀ n, p n) : f = g := rfl
theorem pi_imax.{u} (α : Sort u) (β : α → Prop) (f g : ∀ a, β a) : f = g := rfl
theorem pi_beta (a b : (fun _ : Nat => True) 0) : a = b := rfl
theorem pi_data (P : Prop) (a b : P → Nat) : a = b := sorry
theorem pi_sort.{u} (α : Sort u) (a b : α) : a = b := sorry
theorem pi_bool (a b : Bool) : a = b := sorry
def ex_wit (h : ∃ _ : Nat, True) : Nat := 0
theorem and_left (A B : Prop) (h : A ∧ B) : A := h.1

/-! Malformed-export base -/
theorem triv : True := True.intro

/-! Strings -/
def str_ab : String := "ab"

/-! Evaluation of closed terms (the evaluator in `src/check/eval/`) -/
def ev_sum (n : Nat) : Nat := (List.range n).foldl (· + ·) 0
theorem ev_decide : decide (ev_sum 100 = 4950) = true := rfl
theorem ev_decide_false : decide (ev_sum 100 = 4951) = true := sorry
axiom ev_ax_bad : (0 : Nat) = 1
axiom ev_ax_ok : (2 + 2 : Nat) = 4
noncomputable def ev_cast_bad : Nat := @Eq.rec Nat 0 (fun _ _ => Nat) 5 1 ev_ax_bad
theorem ev_k_stuck : ev_cast_bad = 5 := sorry
noncomputable def ev_cast_ok : Nat := @Eq.rec Nat (2 + 2) (fun _ _ => Nat) 5 4 ev_ax_ok
theorem ev_k_ok : ev_cast_ok = 5 := sorry
axiom ev_pair : Nat × Nat
noncomputable def ev_fst : Nat := Prod.rec (motive := fun _ => Nat) (fun a _ => a) ev_pair
theorem ev_struct_eta : ev_fst = ev_pair.1 := sorry
theorem ev_struct_eta_wrong : ev_fst = ev_pair.2 := sorry
theorem ev_quot_ok :
    Quot.lift (fun n : Nat => n + 1) (fun _ _ (h : _ = _) => congrArg (· + 1) h)
      (Quot.mk (· = ·) (ev_sum 4)) = 7 := sorry
theorem ev_quot_wrong :
    Quot.lift (fun n : Nat => n + 1) (fun _ _ (h : _ = _) => congrArg (· + 1) h)
      (Quot.mk (· = ·) (ev_sum 4)) = 6 := sorry
theorem ev_str_len : "abc".length = 3 := sorry
theorem ev_str_len_wrong : "abc".length = 4 := sorry
def ev_deep (n : Nat) : Nat := (List.replicate n 1).foldr (· + ·) 0
theorem ev_deep_ok : ev_deep 20000 = 20000 := sorry
theorem ev_deep_wrong : ev_deep 20000 = 19999 := sorry
theorem ev_pap : Nat.add 1 = fun x => Nat.add 1 x := sorry
theorem ev_pap_wrong : Nat.add 1 = fun x => Nat.add 2 x := sorry
def ev_rec (n : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun _ ih => ih + 2) n
theorem ev_rec_lit : ev_rec 1000 = 2000 := sorry
theorem ev_rec_lit_wrong : ev_rec 1000 = 2001 := sorry
theorem ev_big : decide (2 ^ 100 - (2 ^ 100 - 7) = 7) = true := sorry
theorem ev_big_wrong : decide (2 ^ 100 - (2 ^ 100 - 7) = 8) = true := sorry
def ev_let : Nat := let x := ev_sum 1000; x + x
theorem ev_let_ok : ev_let = 999000 := sorry
theorem ev_let_wrong : ev_let = 999001 := sorry
def ev_fn : Nat → Nat := (List.range 5).foldl (fun f _ => fun x => f x + 1) id
theorem ev_fn_ok : ev_fn 3 = 8 := sorry
theorem ev_fn_wrong : ev_fn 3 = 7 := sorry

def ev_arr (n : Nat) : Array Nat := (List.range n).foldl (fun a i => a.push (i * i)) #[]
theorem ev_arr_get : (ev_arr 50)[49]! + (ev_arr 50).getD 50 7 = 2408 := sorry
theorem ev_arr_get_wrong : (ev_arr 50)[49]! + (ev_arr 50).getD 50 7 = 2401 := sorry
theorem ev_arr_set : ((ev_arr 50).set! 3 100).toList.take 5 = [0, 1, 4, 100, 16] := sorry
theorem ev_arr_set_wrong : ((ev_arr 50).set! 3 100).toList.take 5 = [0, 1, 4, 9, 16] := sorry
theorem ev_arr_oob : ((ev_arr 5).set! 9 1).size + (ev_arr 5)[9]! = 5 := sorry
theorem ev_arr_oob_wrong : ((ev_arr 5).set! 9 1).size + (ev_arr 5)[9]! = 6 := sorry
theorem ev_arr_eq : decide (ev_arr 20 = (List.range 20).toArray.map (fun i => i * i)) = true := sorry
theorem ev_arr_eq_wrong : decide (ev_arr 20 = (List.range 20).toArray) = true := sorry
def ev_arr_fns : Array (Nat → Nat) := #[(· + 1), (· * 2)] |>.push (· + 10)
theorem ev_arr_fn : ev_arr_fns[2]! 5 + ev_arr_fns[1]! 4 = 23 := sorry
theorem ev_arr_fn_wrong : ev_arr_fns[2]! 5 + ev_arr_fns[1]! 4 = 24 := sorry

end K
