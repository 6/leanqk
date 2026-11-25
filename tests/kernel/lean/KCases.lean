/-
Source for the base exports of `cargo xtask kernel-cases`. Every declaration is
valid; it exports the closure of a few of them and applies one mutation per case.
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
theorem ev_arr_vers :
    (let a := ev_arr 10; let b := a.set! 2 7; let c := b.push 5; let d := a.set! 2 8
     a[2]! + b[2]! + c[10]! + d[2]! + c.size + a.size + b[2]! + a[2]!) = 56 := sorry
theorem ev_arr_vers_wrong :
    (let a := ev_arr 10; let b := a.set! 2 7; let c := b.push 5; let d := a.set! 2 8
     a[2]! + b[2]! + c[10]! + d[2]! + c.size + a.size + b[2]! + a[2]!) = 57 := sorry
def ev_m2 : List Nat → List Nat → Nat
  | x :: xs, y :: ys => x * y + ev_m2 xs ys
  | [], ys => ys.length
  | xs, [] => xs.length + 100
def ev_m3 : Option (Nat × Nat) → Nat → Nat
  | some (a, b), 0 => a + b
  | some (a, _), n+1 => a * n
  | none, n => n + 7
def ev_m4 (l : List Nat) : List Nat := match l with
  | a :: b :: rest => b :: a :: rest
  | other => other
def ev_m5 : Bool → Bool → Nat → Nat
  | true, true, _ => 1
  | true, false, n => n
  | false, _, 3 => 30
  | false, b, n => if b then n * 2 else n + 1
theorem ev_match :
    (ev_m2 [1, 2, 3] [4, 5, 6, 7], ev_m2 [] [1, 2], ev_m2 [1, 2, 3] [], ev_m3 (some (3, 4)) 0,
      ev_m3 (some (3, 4)) 5, ev_m3 none 2, ev_m4 [1, 2, 3], ev_m4 [9],
      [ev_m5 true true 0, ev_m5 true false 4, ev_m5 false true 3, ev_m5 false true 5,
        ev_m5 false false 5]) =
    (33, 2, 103, 7, 12, 9, [2, 1, 3], [9], [1, 4, 30, 10, 6]) := sorry
theorem ev_match_wrong :
    (ev_m2 [1, 2, 3] [4, 5, 6, 7], ev_m2 [] [1, 2], ev_m2 [1, 2, 3] [], ev_m3 (some (3, 4)) 0,
      ev_m3 (some (3, 4)) 5, ev_m3 none 2, ev_m4 [1, 2, 3], ev_m4 [9],
      [ev_m5 true true 0, ev_m5 true false 4, ev_m5 false true 3, ev_m5 false true 5,
        ev_m5 false false 5]) =
    (33, 2, 103, 7, 12, 9, [1, 2, 3], [9], [1, 4, 30, 10, 6]) := sorry
def ev_sel (n : Nat) : Nat :=
  (if n % 2 = 0 then (· + 1) else (· * 3)) n + (if _ : n < 5 then n + 100 else 7) +
    (if decide (n = 3) then 1000 else 0) + (dite (n = 4) (fun _ => 20) (fun _ => 30))
theorem ev_select : ((List.range 10).map ev_sel).foldl (· + ·) 0 = 1935 := sorry
theorem ev_select_wrong : ((List.range 10).map ev_sel).foldl (· + ·) 0 = 1936 := sorry
def ev_arr_hist : List (Array Nat) :=
  (List.range 20).foldl (fun vs i => match vs with
    | v :: _ => (if i % 3 == 0 then v.push i else v.set! (i % 7) (i + 100)) :: vs
    | [] => []) [ev_arr 7]
theorem ev_arr_hist_ok : (ev_arr_hist.map (fun v => v.foldl (· + ·) 0 + v.size)).sum = 12068 := sorry
theorem ev_arr_hist_wrong : (ev_arr_hist.map (fun v => v.foldl (· + ·) 0 + v.size)).sum = 12067 := sorry

-- `List` operations with fast paths.
theorem ev_lists :
    ((List.range 50).any (· == 49), (List.range 50).all (· < 49),
      ((List.range 50).filter (· % 7 == 0)).getLast?,
      (List.range 50).foldl (· + ·) 0, (List.range 5).reverse,
      (List.range 9).elem 8, ((List.range 30).map (· % 4)).eraseDups) =
    (true, false, some 49, 1225, [4, 3, 2, 1, 0], true, [0, 1, 2, 3]) := sorry
theorem ev_lists_wrong : (List.range 50).foldl (· + ·) 0 = 1224 := sorry
theorem ev_filter_lazy : ((List.range 10).filter (fun i => i == 0 || 10 / i > 2)).head? = some 0 := sorry
theorem ev_filter_lazy_wrong : ((List.range 10).filter (fun i => i == 0 || 10 / i > 2)).head? = some 1 := sorry

-- `Int` operations on every sign, zero divisors and big values, hashed,
-- and lazy `List.map`, `zipWith`, `append` and `length`.
def ev_xs : List Int := [-7, -1, 0, 1, 7, (1234567890 * 10 ^ 10 + 1234567890) * 1000 + 123, -(9876543210 * 10 ^ 10 + 9876543210)]
def ev_ys : List Int := [-3, -1, 0, 1, 3, -12345678901, 98765432109]
def ev_ints : List Int := ev_xs.flatMap fun x => ev_ys.flatMap fun y =>
  [x + y, x - y, x * y, -x, x / y, x % y, x.tdiv y, x.tmod y, x ^ (y.natAbs % 5),
   Int.subNatNat x.natAbs y.natAbs, Int.negOfNat y.natAbs, (x.natAbs : Int), (x.toNat : Int)]
theorem ev_int : ev_ints.foldl (fun a b => (a * 31 + b) % 1000000007) 0 = 131563993 := sorry
theorem ev_int_wrong : ev_ints.foldl (fun a b => (a * 31 + b) % 1000000007) 0 = 131563994 := sorry
def ev_zip : List Nat := ((List.range 30).map (· * 3)).zipWith (· + ·) ((List.range 40) ++ [7, 8])
theorem ev_lists2 : (ev_zip.length, ev_zip.foldl (· + ·) 0) = (30, 1740) := sorry
theorem ev_lists2_wrong : ev_zip.length = 31 := sorry

-- Erased proofs that are needed after all: a cast over a theorem applied to
-- a variable (a `K`-like major premise), `And.rec` on a constructed proof,
-- and an answer holding a proof.
theorem ev_tn (n : Nat) : (fun _ : Nat => Nat) n = Nat := rfl
def ev_castv (n : Nat) : Nat := cast (ev_tn n) (n + 1)
theorem ev_cast_thm : ev_castv 4 = 5 := sorry
theorem ev_cast_thm_wrong : ev_castv 4 = 4 := sorry
def ev_and (n : Nat) : Nat := (And.intro (Eq.refl n) (Eq.refl n) : n = n ∧ n = n).elim (fun _ _ => n + 1)
theorem ev_and_ok : ev_and 3 = 4 := sorry
theorem ev_and_wrong : ev_and 3 = 5 := sorry
def ev_sub (n : Nat) : {x : Nat // x = n + 1} := ⟨n + 1, Eq.refl (n + 1)⟩
theorem ev_sub_ok : ev_sub 3 = ⟨4, Eq.refl 4⟩ := sorry
theorem ev_sub_wrong : (ev_sub 3).val = 3 := sorry

-- Class methods at many instances: `+` through instances built from a
-- number (more of them than the evaluator remembers per method), through
-- an instance passed as an argument, and through a computed field.
def ev_addN (n : Nat) : Add Nat := ⟨fun a b => a + b + n⟩
def ev_plus {α} [Add α] (x y : α) : α := x + y
def ev_methods : Nat :=
  (List.range 20).foldl (fun s n => s + @HAdd.hAdd Nat Nat Nat (@instHAdd Nat (ev_addN n)) n 1) 0
  + (List.range 20).foldl (fun s n => s + @ev_plus Nat (ev_addN (n % 3)) n n) 0
  + @ev_plus Nat ⟨fun a b => a * b + (List.range 10).foldl (· + ·) 0⟩ 6 7
theorem ev_methods_ok : ev_methods = 886 := sorry
theorem ev_methods_wrong : ev_methods = 887 := sorry

-- Matches, run through `casesOn` and the sparse `casesOn` of matchers:
-- several constructors, wildcards (the sparse form's `else`), a `Nat`
-- literal scrutinee, a structure, an `Option` of a function, and a match
-- whose result is a function applied to more arguments.
inductive EvShape | dot | seg (n : Nat) | tri (a b : Nat) (s : EvShape)
def ev_shape_size : EvShape → Nat
  | .dot => 1
  | .seg n => n + 2
  | .tri a b s => a * b + ev_shape_size s
def ev_shapes (n : Nat) : EvShape :=
  (List.range n).foldl (fun s i => if i % 3 == 0 then .tri i (i + 1) s else s) (.seg n)
def ev_kind : Nat → List Nat → Nat
  | 0, _ => 7
  | n + 1, x :: _ => n + x
  | _, _ => 100
def ev_pick (o : Option (Nat → Nat)) : Nat → Nat := match o with
  | some f => f
  | none => (· + 1)
def ev_pair2 : Nat × Nat → Nat | (a, b) => a * 10 + b
def ev_cases : Nat :=
  ev_shape_size (ev_shapes 30) + ev_kind 0 [] + ev_kind 5 [9] + ev_kind 4 [] +
  ev_pick (some (· * 2)) 21 + ev_pick none 41 + ev_pair2 (3, 4)
theorem ev_cases_ok : ev_cases = 2970 := sorry
theorem ev_cases_wrong : ev_cases = 2971 := sorry

/-! Found by differential fuzzing (tests/fuzz) -/
theorem fz_quot_direct :
    Quot.lift (fun n : Nat => n + 1) (fun _ _ (h : _ = _) => congrArg (· + 1) h)
      (Quot.mk (· = ·) 4) = 5 := rfl
theorem fz_str_deceq : decide ("abc" = "abc") = true := by decide
def fz_two : Nat := 2

end K
