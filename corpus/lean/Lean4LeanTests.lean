import Tutorial.Meta

/-!
Test cases taken from the regression tests of lean4lean
(https://github.com/digama0/lean4lean, `Lean4Lean/Tests/*.lean`, Apache-2.0,
by Mario Carneiro and the lean4lean contributors).

lean4lean runs these declarations through its own `addDecl` from Lean code. Here
each declaration is exported as a test case instead, with the Lean Kernel Arena
test machinery (`Tutorial.Meta`): `good_decl` declarations go through Lean's
kernel, `bad_decl` ones bypass it so that the export contains them. The
declarations are copied unchanged; only the names of the helpers differ.

Left out: the cases that Lean's inductive compiler rejects even when kernel type
checking is skipped (`nestedAuxRealDecl`, `nestedIllTypedParams` and
`NestedInductive.badDecl`; the Arena's `bugs/nested-unused-param` covers
leanprover/lean4#14577), the well-formed nested inductive of `NestedInductive.lean`, on which the
export machinery panics, the free variable and metavariable cases, which the
export format cannot express, and the unit tests of lean4lean's own API (levels,
fuel and numeral size limits).
-/

open Lean

namespace L4LTests

/-! ## `Lean4Lean/Tests/KernelHardening.lean` -/

def universeTy : Expr :=
  .forallE `x (.sort (.param `u)) (.sort (.param `u)) .default

def universeVal : Expr :=
  .lam `x (.sort (.param `u)) (.bvar 0) .default

def mkPartial (n : Name) (lparams : List Name) (type value : Expr) : DefinitionVal :=
  { name := n, levelParams := lparams, type, value, hints := .opaque, safety := .partial }

def imaxProp : Expr := .sort (.imax (.succ .zero) .zero)

def imaxDataDecl : Declaration :=
  .inductDecl [] 0 [{
    name := `L4LKIPData
    type := imaxProp
    ctors := [{
      name := `L4LKIPData.mk
      type := .forallE `b (.const ``Bool []) (.const `L4LKIPData []) .default }]
  }] false

def imaxLeakDecl : Declaration :=
  .defnDecl {
    name := `L4LKIPLeak
    levelParams := []
    type := .forallE `proof (.const `L4LKIPData []) (.const ``Bool []) .default
    value := .lam `proof (.const `L4LKIPData []) (.proj `L4LKIPData 0 (.bvar 0)) .default
    hints := .abbrev, safety := .safe }

end L4LTests

structure L4LKC where b : Bool
inductive L4LKW : Type where | mk (p : Bool)
inductive L4LKL (α : Type) (b : Bool) : Type where | mk
structure ProjB where b : Nat

namespace L4LTests

partial def deepNat : Nat → Expr
  | 0 => .const ``Nat.zero []
  | n + 1 => .app (.const ``Nat.succ []) (deepNat n)

end L4LTests

open L4LTests

/-- lean4lean KernelHardening (leanprover/lean4#14608): the definitions of a
mutual block must have the same universe parameters. -/
bad_decl (.mutualDefnDecl [
  mkPartial `L4LMutA [`u] universeTy universeVal,
  mkPartial `L4LMutB [] universeTy universeVal])

/-- lean4lean KernelHardening (control case): a well-formed mutual block of two
partial definitions. -/
good_decl (.mutualDefnDecl [
  mkPartial `L4LMutGoodA [] (.const ``Nat []) (mkRawNatLit 0),
  mkPartial `L4LMutGoodB [] (.const ``Bool []) (.const ``Bool.true [])])

/-- lean4lean KernelHardening (leanprover/lean4#14613, #14615): an inductive in
`Sort (imax 1 0)`, which is `Prop` after normalization, is a proposition and
gets a recursor with small elimination only. -/
good_decl imaxDataDecl

/-- lean4lean KernelHardening (leanprover/lean4#14613): projecting the field out
of a proof of the `Sort (imax 1 0)` inductive `L4LKIPData` breaks proof
irrelevance (it would separate `mk false` from `mk true`) and must be rejected. -/
bad_decl imaxLeakDecl

/-- lean4lean KernelHardening (leanprover/lean4#14632): a projection with an
index past `2^32` is out of range and must not be truncated to a valid one. -/
bad_decl (.defnDecl {
  name := `L4LProjHuge, levelParams := [], type := .const ``Nat []
  value := .proj ``ProjB 4294967296 (.app (.const ``ProjB.mk []) (mkRawNatLit 7))
  hints := .abbrev, safety := .safe })

/-- lean4lean KernelHardening (control case): the in-range projection reduces. -/
good_decl (.thmDecl {
  name := `L4LProjGood, levelParams := []
  type := mkApp3 (.const ``Eq [1]) (.const ``Nat [])
    (.proj ``ProjB 0 (.app (.const ``ProjB.mk []) (mkRawNatLit 7))) (mkRawNatLit 7)
  value := mkApp2 (.const ``Eq.refl [1]) (.const ``Nat []) (mkRawNatLit 7) })

/-- lean4lean KernelHardening (leanprover/lean4#13956): a term of nesting depth
100 checks with the default recursion limit. -/
good_decl (.defnDecl {
  name := `L4LDeepNat, levelParams := [], type := .const ``Nat []
  value := deepNat 100, hints := .abbrev, safety := .safe })
