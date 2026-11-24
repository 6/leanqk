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

end K
