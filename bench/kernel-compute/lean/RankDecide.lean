import Lean
open Lean

/-- usage: lean --run RankDecide.lean OUT.tsv MODULE-PREFIX ROOTMODULE...
Times the kernel on every theorem of the modules with the given prefix whose proof term
uses `of_decide_eq_true`, by re-adding a renamed copy to the environment.
Writes `name<TAB>nanoseconds<TAB>module<TAB>accepted<TAB>distinct-objects-in-proof-term` lines. -/
def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  match args with
  | out :: pre :: roots =>
    let pre := pre.toName
    let env ← importModules (roots.toArray.map fun m => { module := m.toName : Import }) {}
    let mut lines : Array String := #[]
    let mut n := 0
    for (nm, ci) in env.constants.map₁.toList do
      let .thmInfo ti := ci | continue
      if nm.isInternal then continue
      let some idx := env.getModuleIdxFor? nm | continue
      let m := env.header.moduleNames[idx.toNat]!
      unless pre.isPrefixOf m do continue
      unless ti.value.getUsedConstants.contains ``of_decide_eq_true do continue
      n := n + 1
      let decl := Declaration.thmDecl { ti with name := nm ++ `_bench_copy }
      let t0 ← IO.monoNanosNow
      let ok ← IO.lazyPure fun _ => match env.toKernelEnv.addDecl {} decl none with | Except.ok _ => true | Except.error _ => false
      let t1 ← IO.monoNanosNow
      let objs ← ti.value.numObjs
      lines := lines.push s!"{nm.toString (escape := true)}\t{t1 - t0}\t{m}\t{ok}\t{objs}"
    IO.FS.writeFile out ("\n".intercalate lines.toList ++ "\n")
    IO.eprintln s!"{n} candidates"
  | _ => IO.eprintln "usage"
