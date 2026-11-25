import MatCert.Basic
import Lean

/-!
`mat_cert name "file"` reads a certificate written by `cargo xtask matcert gen` and adds
the theorem

* `name : MatCert.InvertibleMod p n A`, proved by
  `invertibleMod_of_check B (of_decide_eq_true (Eq.refl true))`, for `inverse p n`;
* `name : MatCert.Nonsingular n A`, proved by
  `nonsingular_of_check B d (of_decide_eq_true (Eq.refl true))`, for `nonsingular n d`.

The term is built directly as an `Expr`, with the matrices as `List (List Int)` literals
(`Int.ofNat`/`Int.negSucc` of raw `Nat` literals), the way the elaborator would state it
but without instances in the literals. Use it under `set_option debug.skipKernelTC true` to
record a theorem whose kernel check would take long: the declaration is then added without
being checked, and the exports are what the checkers are given to check.
-/

open Lean Elab Command

namespace MatCert

def lit (n : Nat) : Expr := mkRawNatLit n

def intE : Int → Expr
  | .ofNat n => mkApp (mkConst ``Int.ofNat) (lit n)
  | .negSucc n => mkApp (mkConst ``Int.negSucc) (lit n)

/-- `0 : Int` as the elaborator writes it. -/
def zeroE : Expr := mkApp3 (mkConst ``OfNat.ofNat [0]) (mkConst ``Int) (lit 0) (mkApp (mkConst ``instOfNat) (lit 0))

def listE (ty : Expr) (xs : Array Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) ty x acc) (mkApp (mkConst ``List.nil [0]) ty)

def rowT : Expr := mkApp (mkConst ``List [0]) (mkConst ``Int)

def matE (rows : Array (Array Int)) : Expr :=
  listE rowT (rows.map fun r => listE (mkConst ``Int) (r.map intE))

/-- `of_decide_eq_true (Eq.refl true) : b = true` for a closed `b : Bool`. -/
def byKernel (b : Expr) : Expr :=
  let t := mkConst ``Bool.true
  let eqTy := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) b t
  let inst := mkApp2 (mkConst ``instDecidableEqBool) b t
  mkApp3 (mkConst ``of_decide_eq_true) eqTy inst (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) t)

def parseInt (s : String) : Except String Int :=
  match s.toInt? with
  | some i => .ok i
  | none => .error s!"not an integer: {s}"

def parseRows (lines : Array String) (start n : Nat) : Except String (Array (Array Int)) := do
  let mut rows := #[]
  for i in [start:start + n] do
    let some line := lines[i]? | throw s!"line {i + 1}: missing"
    let row ← (line.splitOn " ").toArray.mapM parseInt
    unless row.size == n do throw s!"line {i + 1}: {row.size} entries, expected {n}"
    rows := rows.push row
  return rows

/-- The statement and its proof for a certificate file's contents. -/
def certDecl (contents : String) : Except String (Expr × Expr) := do
  let lines := ((contents.splitOn "\n").filter (· ≠ "")).toArray
  let some header := lines[0]? | throw "empty certificate"
  match header.splitOn " " with
  | ["inverse", p, n] =>
    let p ← parseInt p
    let some n := n.toNat? | throw s!"bad size {n}"
    let A := matE (← parseRows lines 1 n)
    let B := matE (← parseRows lines (1 + n) n)
    let pE := intE p
    let nE := lit n
    let chk := mkAppN (mkConst ``check) #[pE, nE, nE, nE, A, B, mkApp (mkConst ``identity) nE]
    return (mkApp3 (mkConst ``InvertibleMod) pE nE A,
      mkAppN (mkConst ``invertibleMod_of_check) #[pE, nE, A, B, byKernel chk])
  | ["nonsingular", n, d] =>
    let some n := n.toNat? | throw s!"bad size {n}"
    let d ← parseInt d
    let A := matE (← parseRows lines 1 n)
    let B := matE (← parseRows lines (1 + n) n)
    let nE := lit n
    let dE := intE d
    let chk := mkAppN (mkConst ``check) #[zeroE, nE, nE, nE, A, B, mkApp2 (mkConst ``scalar) nE dE]
    let ne := mkApp4 (mkConst ``bne [0]) (mkConst ``Int)
      (mkApp2 (mkConst ``instBEqOfDecidableEq [0]) (mkConst ``Int) (mkConst ``Int.instDecidableEq))
      dE zeroE
    let b := mkApp2 (mkConst ``and) ne chk
    return (mkApp2 (mkConst ``Nonsingular) nE A,
      mkAppN (mkConst ``nonsingular_of_check) #[nE, A, B, dE, byKernel b])
  | _ => throw s!"unknown header: {header}"

elab "mat_cert " n:ident ppSpace file:str : command => do
  let contents ← IO.FS.readFile file.getString
  match certDecl contents with
  | .error e => throwError "mat_cert: {e}"
  | .ok (type, value) =>
    let name := (← getCurrNamespace) ++ n.getId
    liftCoreM <| addDecl <| .thmDecl { name, levelParams := [], type, value }

end MatCert
