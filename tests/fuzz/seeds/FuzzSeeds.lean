/-
Seed declarations for the differential fuzzer (tests/fuzz). Every
declaration here is valid; `seeds.py` exports them with `leanexport` and the
fuzzer mutates the exports. Theorems are small on purpose: a mutant is
checked in milliseconds.
-/
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

namespace FZ

/-! ## Kernel computation: Nat literals -/
theorem n_add : 123456789 + 987654321 = 1111111110 := rfl
theorem n_add64 : 18446744073709551615 + 1 = 18446744073709551616 := rfl
theorem n_sub : 1000 - 1001 = 0 := rfl
theorem n_sub_big : 2 ^ 70 - 2 ^ 69 = 590295810358705651712 := rfl
theorem n_mul : 4294967296 * 4294967296 = 18446744073709551616 := rfl
theorem n_div : 1000000007 / 13 = 76923077 := rfl
theorem n_div0 : 17 / 0 = 0 := rfl
theorem n_mod : 1000000007 % 13 = 6 := rfl
theorem n_mod0 : 17 % 0 = 17 := rfl
theorem n_gcd : Nat.gcd 1071 462 = 21 := rfl
theorem n_gcd0 : Nat.gcd 0 5 = 5 := rfl
theorem n_pow : 3 ^ 40 = 12157665459056928801 := rfl
theorem n_log2 : Nat.log2 1000000 = 19 := rfl
theorem n_land : 0xF0F0 &&& 0x3C3C = 0x3030 := rfl
theorem n_lor : 0xF0F0 ||| 0x0F0F = 0xFFFF := rfl
theorem n_xor : 0xFFFF ^^^ 0x0F0F = 0xF0F0 := rfl
theorem n_shl : 1 <<< 65 = 36893488147419103232 := rfl
theorem n_shr : 36893488147419103232 >>> 64 = 2 := rfl
theorem n_beq : Nat.beq 12345678901234567890 12345678901234567890 = true := rfl
theorem n_beq_f : Nat.beq 12345678901234567890 12345678901234567891 = false := rfl
theorem n_ble : Nat.ble 18446744073709551616 18446744073709551615 = false := rfl
theorem n_ble_t : Nat.ble 7 7 = true := rfl
theorem n_succ : Nat.succ 18446744073709551615 = 18446744073709551616 := rfl
theorem n_pred : Nat.pred 0 = 0 := rfl
theorem n_dec : decide (2 ^ 64 = 18446744073709551616) = true := rfl
theorem n_dec_lt : decide (2 ^ 64 < 2 ^ 64 + 1) = true := rfl
theorem n_dec_le : decide (100 ≤ 99) = false := rfl
theorem n_dec_ne : decide ((7 : Nat) ≠ 8) = true := rfl
theorem n_min : min 3 9 = 3 := rfl
theorem n_max : max 3 9 = 9 := rfl
theorem n_mix : (2 ^ 64 + 5) % 7 * 3 / 2 = 0 := rfl

/-! ## Kernel computation: recursion over Nat and lists -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n
theorem r_sum : sumTo 100 = 5050 := rfl
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
theorem r_fib : fib 20 = 6765 := by decide
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n
theorem r_fact : fact 25 = 15511210043330985984000000 := rfl
theorem r_rec : Nat.rec (motive := fun _ => Nat) 1 (fun _ ih => 2 * ih) 30 = 1073741824 := rfl
theorem l_len : (List.range 300).length = 300 := rfl
theorem l_sum : (List.range 101).foldl (· + ·) 0 = 5050 := rfl
theorem l_rev : [1, 2, 3, 4].reverse = [4, 3, 2, 1] := rfl
theorem l_map : [1, 2, 3].map (· * 10) = [10, 20, 30] := rfl
theorem l_filter : ((List.range 20).filter (· % 3 == 0)).length = 7 := rfl
theorem l_all : (List.range 50).all (· < 50) = true := rfl
theorem l_any : (List.range 50).any (· == 77) = false := rfl
theorem l_mem : decide (17 ∈ List.range 20) = true := by decide
theorem l_get : [5, 6, 7].getD 2 0 = 7 := rfl
theorem l_append : ([1, 2] ++ [3]).length = 3 := rfl

/-! ## Kernel computation: Bool and decide -/
theorem b_and : (true && false) = false := rfl
theorem b_or : (false || true) = true := rfl
theorem b_not : (!true) = false := rfl
theorem b_xor : xor true true = false := rfl
theorem b_ite : (if 3 < 4 then 10 else 20) = 10 := rfl
theorem b_cond : cond (Nat.ble 3 2) 1 2 = 2 := rfl
theorem d_ball : ∀ x, x < 40 → x * x % 4 < 2 := by decide
theorem d_exists : decide (∃ x, x < 30 ∧ x * x = 196) = true := by decide
theorem d_and : (3 < 5 ∧ 5 < 7) := by decide
theorem d_or : (3 > 5 ∨ 5 < 7) := by decide
theorem d_not : ¬ (10 = 11) := by decide
theorem d_iff : decide ((1 = 1) ↔ (2 = 2)) = true := by decide
theorem d_fin : ∀ i : Fin 6, i.val < 6 := by decide
theorem d_bool : ∀ b : Bool, (b || !b) = true := by decide
theorem d_prod : decide ((3, 4) = (3, 4)) = true := by decide
theorem d_list : decide ([1, 2, 3] = [1, 2, 3]) = true := by decide
theorem d_opt : decide ((some 3 : Option Nat) ≠ none) = true := by decide

/-! ## Kernel computation: Array -/
def arr (n : Nat) : Array Nat := (List.range n).foldl (fun a i => a.push (i * i)) #[]
theorem a_size : (arr 30).size = 30 := rfl
theorem a_get : (arr 30)[29]! = 841 := rfl
theorem a_getD : (arr 3).getD 10 42 = 42 := rfl
theorem a_set : ((arr 5).set! 2 100).toList = [0, 1, 100, 9, 16] := rfl
theorem a_set_oob : ((arr 5).set! 9 1).size = 5 := rfl
theorem a_push : (#[1, 2] |>.push 3).toList = [1, 2, 3] := rfl
theorem a_pop : (#[1, 2, 3].pop).size = 2 := rfl
theorem a_map : (#[1, 2, 3].map (· + 1)).toList = [2, 3, 4] := by decide +kernel
theorem a_foldl : (arr 10).foldl (· + ·) 0 = 285 := rfl
theorem a_lit : #[3, 1, 2].toList.length = 3 := rfl
theorem a_append : (#[1, 2] ++ #[3, 4]).size = 4 := rfl
theorem a_dec : decide (arr 4 = #[0, 1, 4, 9]) = true := by decide
theorem a_mk : (Array.mk [7, 8, 9])[1]! = 8 := rfl
theorem a_replicate : (Array.replicate 5 'x').size = 5 := rfl
theorem a_contains : (arr 10).contains 49 = true := by decide +kernel
theorem a_range : (Array.range 6).toList = [0, 1, 2, 3, 4, 5] := rfl
theorem a_rev : (#[1, 2, 3].reverse).toList = [3, 2, 1] := by decide +kernel
def arrFns : Array (Nat → Nat) := #[(· + 1), (· * 2)] |>.push (· + 10)
theorem a_fn : arrFns[2]! 5 + arrFns[1]! 4 = 23 := rfl

/-! ## Kernel computation: String and Char -/
theorem s_len : "hello".length = 5 := by decide
theorem s_append : ("ab" ++ "cd").length = 4 := by decide
theorem s_eq : decide ("abc" = "abc") = true := by decide
theorem s_ne : decide ("abc" = "abd") = false := by decide
theorem c_val : 'A'.toNat = 65 := rfl

/-! ## Fin and UInt -/
theorem f_add : ((3 : Fin 5) + 4).val = 2 := rfl
theorem f_mul : ((3 : Fin 7) * 5).val = 1 := rfl
theorem u_add : ((255 : UInt8) + 1).toNat = 0 := rfl
theorem u_mul : ((65536 : UInt32) * 65536).toNat = 0 := rfl
theorem u64 : ((2 ^ 63 : UInt64) * 2).toNat = 0 := rfl

/-! ## Structures, projections and eta -/
structure Pt where
  x : Nat
  y : Nat
deriving DecidableEq

structure PPair (p q : Prop) : Prop where
  l : p
  r : q

def pt : Pt := ⟨3, 4⟩
theorem p_proj : pt.x + pt.y = 7 := rfl
theorem p_eta (p : Pt) : p = ⟨p.x, p.y⟩ := rfl
theorem p_eta2 (p : Pt) : Pt.mk p.1 p.2 = p := rfl
theorem p_prod_eta (p : Nat × Bool) : (p.1, p.2) = p := rfl
theorem p_prop (a b : Prop) (h : PPair a b) : a := h.l
theorem p_prop2 (a b : Prop) (h : PPair a b) : PPair b a := ⟨h.r, h.l⟩
theorem p_unit (u v : Unit) : u = v := rfl
theorem p_punit (u v : PUnit.{3}) : u = v := rfl
theorem p_sig (s : { n : Nat // n > 0 }) : s = ⟨s.1, s.2⟩ := rfl
theorem p_sigma (s : (n : Nat) × Fin (n + 1)) : s = ⟨s.1, s.2⟩ := rfl
def swapPt (p : Pt) : Pt := { x := p.y, y := p.x }
theorem p_swap (p : Pt) : swapPt (swapPt p) = p := rfl
theorem p_dec : decide (Pt.mk 1 2 = Pt.mk 1 2) = true := by decide
theorem p_rec (p : Pt) : Pt.rec (motive := fun _ => Nat) (fun a b => a + b) p = p.x + p.y := rfl

/-! ## Proof irrelevance, unit eta, K-like reduction -/
theorem pi_irrel (p : Prop) (h1 h2 : p) : h1 = h2 := rfl
theorem k_eq (h : (2 : Nat) = 2) : (Eq.rec (motive := fun _ _ => Nat) 5 h : Nat) = 5 := rfl
theorem k_true (h : True) : (True.rec (motive := fun _ => Nat) 9 h : Nat) = 9 := rfl
def castNat (h : Nat = Nat) (n : Nat) : Nat := cast h n
theorem k_cast : castNat rfl 4 = 4 := rfl

/-! ## Quotients -/
def rel (a b : Nat) : Prop := a % 3 = b % 3
def Q := Quot rel
def qmk (n : Nat) : Q := Quot.mk rel n
def qlift (q : Q) : Nat := Quot.lift (fun n => n % 3) (fun _ _ h => h) q
theorem q_lift : qlift (qmk 10) = 1 := rfl
theorem q_lift_id : Quot.lift (fun n : Nat => n + 1) (fun _ _ (h : _ = _) => congrArg (· + 1) h)
    (Quot.mk (· = ·) 4) = 5 := rfl
theorem q_ind (q : Q) : qlift q < 3 :=
  Quot.ind (β := fun q => qlift q < 3) (fun n => Nat.mod_lt n (by decide)) q
theorem q_sound : qmk 1 = qmk 4 := Quot.sound rfl
theorem q_eta (q : Q) : Quot.lift (Quot.mk rel) (fun _ _ h => Quot.sound h) q = q :=
  Quot.ind (β := fun q => Quot.lift (Quot.mk rel) (fun _ _ h => Quot.sound h) q = q)
    (fun _ => rfl) q

/-! ## Let-bindings and de Bruijn indices -/
def letN : Nat := let x := 5; let y := x + 1; x * y
theorem lt_val : letN = 30 := rfl
theorem lt_dep : (let n := 3; (⟨2, by decide⟩ : Fin n)).val = 2 := rfl
theorem lt_shadow : (let x := 1; let x := x + 10; x * 2) = 22 := rfl
def lamk (a b c : Nat) : Nat := a * 100 + b * 10 + c
theorem lt_bvar : (fun a b c : Nat => lamk c a b) 1 2 3 = 312 := rfl
theorem lt_nested : (fun f : Nat → Nat → Nat => f 2 5) (fun a b => a - b) = 0 := rfl
theorem lt_binder (f : Nat → Nat) (x : Nat) : (fun y => f y) x = f x := rfl
theorem lt_eta (f : Nat → Nat) : (fun y => f y) = f := rfl

/-! ## Definitional heights, unfolding, opaque -/
def h1 (n : Nat) : Nat := n + 1
def h2 (n : Nat) : Nat := h1 (h1 n)
def h3 (n : Nat) : Nat := h2 (h2 n)
@[reducible] def hr (n : Nat) : Nat := h3 n
abbrev ha (n : Nat) : Nat := hr n + 0
theorem h_eq : h3 5 = 9 := rfl
theorem h_cross (n : Nat) : h3 n = h2 (h1 (h1 n)) := rfl
theorem h_abbrev (n : Nat) : ha n = h3 n := rfl
opaque op : Nat
theorem h_op : op + 0 = op := rfl
@[irreducible] def hirr : Nat := 42
theorem h_irr : hirr = 42 := by unfold hirr; rfl

/-! ## Inductive types -/
inductive Tree where
  | leaf : Tree
  | node : Tree → Nat → Tree → Tree
def Tree.size : Tree → Nat
  | leaf => 0
  | node l _ r => l.size + 1 + r.size
theorem i_tree : (Tree.node (.node .leaf 1 .leaf) 2 .leaf).size = 2 := rfl

inductive Vec (α : Type u) : Nat → Type u where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)
def Vec.head : Vec α (n + 1) → α
  | .cons a _ => a
theorem i_vec : (Vec.cons 7 (Vec.cons 8 Vec.nil)).head = 7 := rfl

mutual
inductive Ev : Nat → Prop
  | zero : Ev 0
  | succ : Od n → Ev (n + 1)
inductive Od : Nat → Prop
  | succ : Ev n → Od (n + 1)
end
theorem i_ev : Ev 2 := .succ (.succ .zero)

inductive Rose where
  | node : List Rose → Rose
def Rose.isLeaf : Rose → Bool
  | .node [] => true
  | _ => false
theorem i_rose : (Rose.node [.node []]).isLeaf = false := rfl

inductive W (α : Type) (β : α → Type) where
  | sup (a : α) (f : β a → W α β) : W α β

inductive Le : Nat → Nat → Prop
  | refl : Le n n
  | step : Le n m → Le n (m + 1)
theorem i_le : Le 2 4 := .step (.step .refl)

inductive Color where
  | red | green | blue
deriving DecidableEq
def Color.next : Color → Color
  | .red => .green
  | .green => .blue
  | .blue => .red
theorem i_color : Color.red.next.next.next = Color.red := rfl
theorem i_color_dec : decide (Color.red ≠ Color.blue) = true := by decide

inductive MyEq {α : Sort u} (a : α) : α → Prop
  | refl : MyEq a a
theorem i_myeq_k (h : MyEq 3 3) : (MyEq.rec (motive := fun _ _ => Nat) 1 h : Nat) = 1 := rfl

inductive Acc' {α : Sort u} (r : α → α → Prop) : α → Prop where
  | intro (x : α) (h : (y : α) → r y x → Acc' r y) : Acc' r x

structure Wrap (α : Type u) where
  val : α
theorem i_wrap (w : Wrap Nat) : w = ⟨w.val⟩ := rfl

class Size (α : Type) where
  size : α → Nat
instance : Size Pt := ⟨fun p => p.x + p.y⟩
theorem i_class : Size.size pt = 7 := rfl

/-! ## Universe polymorphism -/
def idU {α : Sort u} (a : α) : α := a
theorem u_id : idU (idU 3) = 3 := rfl
def constU {α : Sort u} {β : Sort v} (a : α) (_ : β) : α := a
theorem u_const : constU.{1, 0} 5 True.intro = 5 := rfl
def ulift (n : Nat) : ULift.{3} Nat := ⟨n⟩
theorem u_ulift : (ulift 9).down = 9 := rfl
theorem u_plift : (PLift.up (Eq.refl 3)).down = Eq.refl 3 := rfl
def sortMax (α : Sort u) (β : Sort v) : Sort (max 1 u v) := PProd α β
theorem u_imax : (∀ x : Nat, x = x) = (∀ y : Nat, y = y) := rfl

end FZ
