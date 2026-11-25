import LRATCatcher.Reflect

/-!
`kernel_lrat name "f.cnf" "f.lrat"` adds the theorem
`name : (CNF literal).Unsat`, exactly the term the `+kernel` mode of `lrat_reflect`
produces (`checkKernel_sound cnf actions (of_decide_eq_true (Eq.refl true))`),
but built directly as an `Expr` instead of through the elaborator. Use it under
`set_option debug.skipKernelTC true` to record theorems whose kernel check would
take too long: the declaration is added without being checked, and the export
checkers are then given the whole proof to check.
-/
open Lean Elab Command LRATCatcher Std.Tactic.BVDecide.LRAT

namespace BenchLrat

def natT : Expr := mkConst ``Nat
def boolT : Expr := mkConst ``Bool
def lit (n : Nat) : Expr := mkRawNatLit n

def listE (u : Level) (ty : Expr) (xs : Array Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [u]) ty x acc) (mkApp (mkConst ``List.nil [u]) ty)

def arrayE (ty : Expr) (xs : Array Expr) : Expr :=
  mkApp2 (mkConst ``List.toArray [0]) ty (listE 0 ty xs)

def intE : Int → Expr
  | .ofNat n => mkApp (mkConst ``Int.ofNat) (lit n)
  | .negSucc n => mkApp (mkConst ``Int.negSucc) (lit n)

def natsE (xs : Array Nat) : Expr := arrayE natT (xs.map lit)

def litE (l : Nat × Bool) : Expr :=
  mkApp4 (mkConst ``Prod.mk [0, 0]) natT boolT (lit l.1) (mkConst (if l.2 then ``Bool.true else ``Bool.false))

def natBoolT : Expr := mkApp2 (mkConst ``Prod [0, 0]) natT boolT

def arrIntT : Expr := mkApp (mkConst ``Array [0]) (mkConst ``Int)

def actionT : Expr := mkApp2 (mkConst ``Action [0, 0]) arrIntT natT

def actionE : IntAction → Expr
  | .addEmpty id rup => mkApp4 (mkConst ``Action.addEmpty [0, 0]) arrIntT natT (lit id) (natsE rup)
  | .addRup id c rup =>
    mkApp5 (mkConst ``Action.addRup [0, 0]) arrIntT natT (lit id)
      (arrayE (mkConst ``Int) (c.map intE)) (natsE rup)
  | .addRat id c p rup rat =>
    mkAppN (mkConst ``Action.addRat [0, 0]) #[arrIntT, natT, lit id,
      arrayE (mkConst ``Int) (c.map intE), litE p, natsE rup,
      arrayE (mkApp2 (mkConst ``Prod [0, 0]) natT (mkApp (mkConst ``Array [0]) natT))
        (rat.map fun (a, b) => mkApp4 (mkConst ``Prod.mk [0, 0]) natT (mkApp (mkConst ``Array [0]) natT) (lit a) (natsE b))]
  | .del ids => mkApp3 (mkConst ``Action.del [0, 0]) arrIntT natT (natsE ids)

def cnfE (cnf : Std.Sat.CNF Nat) : Expr :=
  let clauseT := mkApp (mkConst ``List [0]) natBoolT
  let clauses := cnf.clauses.map fun cl => listE 0 natBoolT (cl.toArray.map litE)
  mkApp2 (mkConst ``Std.Sat.CNF.mk [0]) natT (arrayE clauseT clauses)

elab "kernel_lrat " n:ident ppSpace cnfFile:str ppSpace lratFile:str : command => do
  let cnfStr ← loadCnf cnfFile
  let (_, proof) ← loadLrat "kernel_lrat" lratFile
  let cnf := cnfE (parseDimacs cnfStr)
  let actions := listE 0 actionT (proof.map actionE)
  let ty := mkApp2 (mkConst ``Std.Sat.CNF.Unsat [0]) natT cnf
  let eqTy := mkApp3 (mkConst ``Eq [1]) boolT
    (mkApp2 (mkConst ``LRATCatcher.checkKernel) cnf actions) (mkConst ``Bool.true)
  let inst := mkApp2 (mkConst ``instDecidableEqBool)
    (mkApp2 (mkConst ``LRATCatcher.checkKernel) cnf actions) (mkConst ``Bool.true)
  let h := mkApp3 (mkConst ``of_decide_eq_true) eqTy inst
    (mkApp2 (mkConst ``Eq.refl [1]) boolT (mkConst ``Bool.true))
  let val := mkApp3 (mkConst ``LRATCatcher.checkKernel_sound) cnf actions h
  let name := (← getCurrNamespace) ++ n.getId
  liftCoreM <| addDecl <| .thmDecl { name, levelParams := [], type := ty, value := val }

end BenchLrat
