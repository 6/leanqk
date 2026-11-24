import Tutorial.Meta
/-!
Reproducers for historical soundness bugs (wrong acceptances) of the official Lean 4 kernel
(and of the replay layer in front of it), as exports for a kernel checker's correctness corpus.

Each test case bypasses the kernel when the bad declarations are added, so that the export
contains them. Run with `OUT=... lake env lean HistoricalBugs.lean` from the tutorial project.
-/
set_option linter.unusedVariables false
set_option linter.defProp false
open Lean Elab Command

/--
`hb_inject name : type := value` adds a theorem without kernel type checking and without
registering a test case. The value is elaborated against the type only if wrapped in `unchecked`.
-/
elab "hb_inject " name:ident " : " type:term " := " value:term : command => liftTermElabM do
  let typeExpr ← Term.elabTermAndSynthesize type none
  let valueExpr ← Term.elabTermAndSynthesize value (some typeExpr)
  Term.synthesizeSyntheticMVarsNoPostponing
  let typeExpr ← instantiateMVars typeExpr
  let valueExpr ← instantiateMVars valueExpr
  withOptions (debug.skipKernelTC.set · true) <| addDecl <| .thmDecl {
    name := name.getId, levelParams := [], type := typeExpr, value := valueExpr }

/-- Adds a raw declaration without kernel type checking and without registering a test case. -/
def injectDecl (d : Declaration) : CoreM Unit :=
  withOptions (debug.skipKernelTC.set · true) <| addDecl d

/-! ## leanprover/lean4#1781: `imax u v + N` normalized to `imax u v` -/

namespace HB1781

/--
`down.{u,v} : Sort (imax u v + 1) → Sort (imax u v) := fun x => x`.

The value has type `Sort (imax u v + 1) → Sort (imax u v + 1)`, which the buggy level normalizer
identified with the declared type.
-/
def downDecl : Declaration :=
  let l := Level.imax (.param `u) (.param `v)
  .defnDecl {
    name := `HB1781.down
    levelParams := [`u, `v]
    type := .forallE `x (.sort (.succ l)) (.sort l) .default
    value := .lam `x (.sort (.succ l)) (.bvar 0) .default
    hints := .abbrev
    safety := .safe }

run_meta injectDecl downDecl

/-- A proposition that is computationally `Bool` -/
def myProp : Prop := down.{0,0} Bool
def toP (b : Bool) : myProp := b
def ofP (p : myProp) : Bool := p

theorem boom : False :=
  have h : toP true = toP false := rfl
  Bool.noConfusion (show true = false from congrArg ofP h)

end HB1781

/--
Proof of `False` via an unsound level normalization of `imax`.

The kernel normalized `imax u v + N` to `imax u v` regardless of `N`, so it accepted

    def down.{u,v} : Sort (imax u v + 1) → Sort (imax u v) := fun x => x

At `u = v = 0` this collapses `Type` into `Prop`: `myProp := down.{0,0} Bool` is a
proposition whose proofs are booleans, proof irrelevance equates `true` and `false`, and
`boom : False` follows without axioms.

Origin: leanprover/lean4#1781, fixed by digama0 after a report on Zulip ("Bug in kernel level
normalization"; the original Zulip reporter is not named in the PR); the bug was introduced in fb5440a and was not present in Lean 3.
Fixed in October 2022, before Lean v4.0.0 (nightly 2022-10-26 onward).
-/
bad_consts #[`HB1781.boom]

/--
Control for leanprover/lean4#1781: `Sort (imax u v + 1) → Sort (imax u v + 1)` is the correct
type of the identity on `Sort (imax u v + 1)`.
-/
good_decl (.defnDecl {
  name := `HB1781.upCtrl
  levelParams := [`u, `v]
  type := .forallE `x (.sort (.succ (.imax (.param `u) (.param `v))))
    (.sort (.succ (.imax (.param `u) (.param `v)))) .default
  value := .lam `x (.sort (.succ (.imax (.param `u) (.param `v)))) (.bvar 0) .default
  hints := .abbrev
  safety := .safe })

/-! ## leanprover/lean4#2125: an inductive type occurring in its own index -/

namespace HB2125

noncomputable def f (α : Type) : Bool := @decide (Nonempty α) (Classical.propDecidable _)

opaque placeholder : Type

/-- The well-formed variant: `inductive C : Bool → Type | c : C (f placeholder)` -/
def wellFormed : Declaration :=
  .inductDecl [] 0 [{
    name := `HB2125.C
    type := .forallE `b (mkConst ``Bool) (.sort 1) .default
    ctors := [{
      name := `HB2125.C.c
      type := mkApp (mkConst `HB2125.C) (mkApp (mkConst ``HB2125.f) (mkConst ``placeholder)) }] }]
    false

/-- `placeholder` becomes `C false` -/
def patch : ConstantInfo → ConstantInfo :=
  mapConstInfoExprs <| Expr.replace fun
    | .const ``placeholder _ => some (mkApp (mkConst `HB2125.C) (mkConst ``Bool.false))
    | _ => none

run_meta addPatchedInductive wellFormed patch

theorem unsound : False :=
  (Classical.em (Nonempty (C false))).elim
    (fun h => h.elim fun x =>
      have idx : false = f (C false) := C.rec (motive := fun b _ => b = f (C false)) rfl x
      have hf : f (C false) = true := by unfold f; exact @decide_eq_true _ (Classical.propDecidable _) h
      Bool.noConfusion (idx.trans hf))
    (fun hn =>
      have hf : f (C false) = false := by unfold f; exact @decide_eq_false _ (Classical.propDecidable _) hn
      hn ⟨hf ▸ C.c⟩)

end HB2125

/--
Proof of `False` from an inductive type that occurs in its own index.

    noncomputable def f (α : Type) : Bool := decide (Nonempty α)
    inductive C : Bool → Type
      | c : C (f (C false))

The kernel did not reject occurrences of the inductive type being defined in the indices of
the constructor's result type. `C false` is inhabited iff it is empty: if `c : C false`, its
index `false` must be `f (C false) = true`; otherwise `f (C false) = false` and `C.c : C false`.

Origin: leanprover/lean4#2125, reported by gebner (crediting nikswamy for the pointer); fixed
by gebner in leanprover/lean4#2127 ("reject occurrences of inductive type in index"),
February 2023, before Lean v4.0.0.
-/
bad_consts #[`HB2125.unsound]

/-! ## leanprover/lean4#1433: `Nat.mod` with a big dividend and a medium divisor -/

namespace HB1433

def dividend := 2^65
def divisor := 2^33+1
def correctQuot := 2^32-1
def correctRem := 2^32+1
def wrongRem := 1

theorem correct₁ : dividend / divisor = correctQuot := rfl
theorem correct₂ : dividend = divisor * correctQuot + correctRem := rfl

hb_inject HB1433.wrong : dividend % divisor = wrongRem := unchecked (Eq.refl wrongRem)

theorem unsound : False := by
  have : wrongRem = correctRem := by
    have h := Nat.div_add_mod dividend divisor
    rw [wrong, correct₁, correct₂] at h
    apply Nat.add_left_cancel h
  contradiction

end HB1433

/--
Proof of `False` via a wrong GMP-accelerated `Nat.mod` in the kernel.

On 64-bit platforms the C++ `Nat.mod` returned a wrong value when the dividend was a big number
and the divisor between `2^32` and `2^64`: `get_unsigned_int` truncated the divisor. So the
kernel accepted `wrong : 2^65 % (2^33+1) = 1 := rfl` (the true remainder is `2^32+1`), and with
`Nat.div_add_mod` one derives `False` (`unsound`).

Origin: leanprover/lean4#1433, reported by pcpthm; fixed in August 2022, before Lean v4.0.0.
(The bug was in the runtime's `lean_nat_mod`, which the kernel's literal arithmetic uses.)
-/
bad_consts #[`HB1433.unsound]

/-- Control for leanprover/lean4#1433: the correct remainder, `2^65 % (2^33+1) = 2^32+1`. -/
good_thm HB1433.correctCtrl : (2^65 : Nat) % (2^33+1) = 2^32+1 := rfl

/-! ## leanprover/lean4#8060: `Nat.pow` reduction on a non-literal -/

namespace HB8060
noncomputable section

def g.{u} : PUnit.{u} → Nat := fun _ => open Classical in if Type = Type then 0 else 0

def T : Nat → Prop := fun x => if x = 0 then False else True

def POW! := Nat.pow (g.{0} ⟨⟩) 1

run_meta injectDecl <| .defnDecl {
  name := `HB8060.mythm
  hints := .regular 0
  safety := .safe
  type := .app (.const `HB8060.T []) (.const `HB8060.POW! [])
  levelParams := []
  value := .const ``True.intro [] }

theorem g_eq_zero : g.{u} n = 0 := by
  unfold g
  split <;> rfl

theorem show_false : False := by
  change T (Nat.pow 0 1)
  rw [← g_eq_zero]
  exact mythm

end
end HB8060

/--
Proof of `False` via `Nat.pow` reduction on an argument that is not a numeral.

`type_checker::reduce_pow` did not check that the weak head normal form of the base was a
`Nat` literal before reading it as a GMP number. With `g ⟨⟩` (a stuck `Classical` `if`) as
base, the kernel read the `Expr.const` object as a huge number, so `POW! := Nat.pow (g ⟨⟩) 1`
reduced to a nonzero numeral and `mythm : T POW! := True.intro` was accepted, while
`g ⟨⟩ = 0` is provable. (The exact behaviour depends on memory layout; without GMP the kernel
crashed instead.)

Origin: found by datokrat and TwoFX while fuzzing the kernel; fixed in leanprover/lean4#8060
(April 2025, Lean v4.20.0). The test file is the one from that PR.
-/
bad_consts #[`HB8060.show_false]

/-! ## leanprover/lean4#12746 / #13602: projection indices truncated to 32 bits -/

namespace HB12746

structure PairBox where
  first : Nat
  second : Nat

def hugeIdx : Nat := 4294967297

end HB12746

/--
A theorem `{ first := 0, second := 1 }.4294967297 = 1` (as a raw `Expr.proj` with index
`2^32 + 1` on a structure with two fields), proved by `Eq.refl 1`.

`infer_proj`, `reduce_proj` and `lazy_delta_proj_reduction` stored the projection index in a
32-bit `unsigned` after checking only `is_small()`, so index `2^32 + 1` was silently treated as
index 1 and the invalid projection reduced to the second field.

Origin: leanprover/lean4#12746, reported by tcosmo, and its duplicate
leanprover/lean4#13602, reported by trackoor; fixed in leanprover/lean4#16279 (merged
November 2026, after the v4.36.0 release branch). Note: `leanchecker --from-export` of v4.36.0
already rejects this export ("invalid projection"), so on that path the truncation does not bite;
the issues report acceptance through `addDecl` on Lean 4.31-era toolchains.
-/
bad_decl (.thmDecl {
  name := `HB12746.hugeProj
  levelParams := []
  type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat)
    (mkProj ``HB12746.PairBox 4294967297
      (mkApp2 (mkConst ``HB12746.PairBox.mk) (mkNatLit 0) (mkNatLit 1)))
    (mkNatLit 1)
  value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 1) })

/-- Control for leanprover/lean4#12746: the valid projection `{ first := 0, second := 1 }.2 = 1`. -/
good_decl (.thmDecl {
  name := `HB12746.smallProjCtrl
  levelParams := []
  type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat)
    (mkProj ``HB12746.PairBox 1
      (mkApp2 (mkConst ``HB12746.PairBox.mk) (mkNatLit 0) (mkNatLit 1)))
    (mkNatLit 1)
  value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 1) })

/-! ## leanprover/lean4#16279: `numParams` of an inductive truncated to 32 bits -/

namespace HB16279

inductive Box (α : Type) : Type where
  | mk : α → Box α

def boxNat : Box Nat := .mk 0

end HB16279

run_meta do
  let some (.inductInfo v) := (← getEnv).find? ``HB16279.Box | throwError "no Box"
  addConstInfos #[.inductInfo { v with numParams := 2^32 + 1 }]

/--
An inductive type `Box (α : Type) : Type` whose declaration claims `numParams := 2^32 + 1`
(its type has a single binder).

The kernel stored the number of parameters of an inductive declaration in a 32-bit `unsigned`,
so it accepted `numParams := 2^32 + 1` as `numParams = 1` (the PR's example: `2^32` accepted as
`0`). A checker must reject a declaration whose number of parameters exceeds the arity of its
type.

Origin: fixed in leanprover/lean4#16279 by nomeata ("stop truncating kernel counts and indices to
32 bits", November 2026, after the v4.36.0 release branch). Found while fixing
leanprover/lean4#12746 (reported by tcosmo).
-/
bad_consts #[`HB16279.boxNat]

/-! ## leanprover/lean4#15908: native `Nat.add` reduction trusts the name -/

namespace HB15908

def myadd (a b : Nat) : Nat := 0
theorem key (a b : Nat) : myadd a b = 0 := rfl
theorem four_ne_zero : (4 : Nat) = 0 → False := fun h => Nat.noConfusion h

end HB15908

-- `contra` is a `def` (of type `False`) rather than a theorem only because the tutorial's
-- renaming exporter does not traverse theorem values when collecting what to rename.
run_meta injectDecl <| .defnDecl {
  name := `HB15908.contra
  levelParams := []
  type := mkConst ``False
  value := mkApp (mkConst ``HB15908.four_ne_zero)
    (mkApp2 (mkConst ``HB15908.key) (mkNatLit 2) (mkNatLit 2))
  hints := .opaque
  safety := .safe }

/--
Proof of `False` from a non-standard `Nat.add`.

    def Nat.add (_ _ : Nat) : Nat := 0
    theorem key (a b : Nat) : Nat.add a b = 0 := rfl
    theorem four_ne_zero : (4 : Nat) = 0 → False := fun h => Nat.noConfusion h
    def contra : False := four_ne_zero (key 2 2)

The kernel's native `Nat` reducer dispatches on the constant's name and never checks that the
environment's `Nat.add` is the canonical definition. `key` holds by unfolding the body, while
`Nat.add 2 2` reduces natively to `4`.

Origin: leanprover/lean4#15908, reported by Leo0506. Closed as not a kernel bug: the official
kernel assumes the standard prelude, and comparator checks the built-in declarations. An
independent checker must still reject it (lean4lean does: "invalid form for primitive def
Nat.add"). Lean v4.36.0 is expected to accept.
-/
bad_consts #[`HB15908.contra]
  renaming #[(`HB15908.myadd, `Nat.add)]

/-! ## leanprover/lean4#16730: forged `numParams`/`numIndices` in a mutual block -/

namespace HB16730

mutual
inductive PA2 : Type
  | mk : PA2
inductive PB2 : Bool → Type
  | mk : (b : Bool) → (h : b = false) → PB2 true
end

def px : PB2 true := PB2.mk false rfl

end HB16730

namespace HB16730Ctrl
mutual
inductive PA2 : Type
  | mk : PA2
inductive PB2 : Bool → Type
  | mk : (b : Bool) → (h : b = false) → PB2 true
end
def px : PB2 true := PB2.mk false rfl
end HB16730Ctrl

run_meta do
  let some (.inductInfo v) := (← getEnv).find? ``HB16730.PB2 | throwError "no PB2"
  addConstInfos #[.inductInfo { v with numParams := 1, numIndices := 0 }]

run_meta injectDecl <| .thmDecl {
  name := `HB16730.tf
  levelParams := []
  type := mkApp3 (.const ``Eq [1]) (.const ``Bool []) (.const ``Bool.true []) (.const ``Bool.false [])
  value := .proj ``HB16730.PB2 0 (.const ``HB16730.px []) }

theorem HB16730.boom : False := Bool.noConfusion HB16730.tf

/--
Proof of `False` via a forged `InductiveVal` of the second member of a mutual block.

    mutual
    inductive PA2 : Type | mk : PA2
    inductive PB2 : Bool → Type | mk : (b : Bool) → (h : b = false) → PB2 true
    end

The export claims `PB2` has `numParams := 1, numIndices := 0` (truth: 0 and 1). `infer_proj`
trusts the stored `numParams`, so in `px.1` for `px : PB2 true` it substitutes the index `true`
for the constructor's first binder `b`, and field 0 (`h : b = false`) gets the type
`true = false`. `Kernel.Environment.replay` took `nparams` from whichever member it reached
first and never compared the other members' stored `InductiveVal` with the generated one.

Origin: leanprover/lean4#16730, reported by MariusVanDerWijden; replay is fixed by
leanprover/lean4#16717 (November 2026). The issue reports that the `--from-export` path of
v4.36.0 rejects this, but the `.olean` modes of `leanchecker` accepted it. Which error the
official checker gives depends on which block member replay meets first (here it complains
about `PA2` not being applied to the claimed parameter).
-/
bad_consts #[`HB16730.boom]

/--
Control for leanprover/lean4#16730: with the honest `InductiveVal` (`numParams := 0`,
`numIndices := 1`), field 0 of `px : PB2 true` is `b : Bool`, here `false`.
-/
good_decl (.thmDecl {
  name := `HB16730.honestProjCtrl
  levelParams := []
  type := mkApp3 (.const ``Eq [1]) (.const ``Bool [])
    (.proj ``HB16730Ctrl.PB2 0 (.const ``HB16730Ctrl.px [])) (.const ``Bool.false [])
  value := mkApp2 (.const ``Eq.refl [1]) (.const ``Bool []) (.const ``Bool.false []) })
