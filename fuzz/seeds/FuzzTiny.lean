/- A module with no imports, so the .olean reader target can load it on its own. -/
prelude

universe u v

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcProof {α : Prop} : α
unsafe axiom lcUnreachable {α : Sort u} : α

inductive PNat where
  | zero : PNat
  | succ : PNat → PNat

noncomputable def PNat.add (n m : PNat) : PNat :=
  PNat.rec (motive := fun _ => PNat) n (fun _ ih => PNat.succ ih) m

inductive PEq {α : Sort u} (a : α) : α → Prop where
  | refl : PEq a a

theorem PNat.add_zero (n : PNat) : PEq (PNat.add n PNat.zero) (PNat.add n PNat.zero) :=
  PEq.refl

inductive PPair (α : Type u) (β : Type v) where
  | mk : α → β → PPair α β

noncomputable def PPair.swap {α : Type u} {β : Type v} (p : PPair α β) : PPair β α :=
  PPair.rec (motive := fun _ => PPair β α) (fun a b => PPair.mk b a) p

inductive PList (α : Type u) where
  | nil : PList α
  | cons : α → PList α → PList α

noncomputable def lit : PNat := let x := PNat.succ PNat.zero; PNat.add x x
