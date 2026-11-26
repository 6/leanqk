import LeanExport.Basic

open Lean

def readName (parts : Array Json) : Except String Name :=
  parts.foldlM (fun parent part =>
    match part with
    | .str text => pure (.str parent text)
    | _ => return .num parent (← part.getNat?))
    .anonymous

def main (args : List String) : IO Unit := do
  let [input] := args | throw (IO.userError "usage: OrderedExport.lean ROOTS.jsonl")
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Mathlib }] {}
  let lines ← IO.FS.lines input
  let roots ← lines.toList.mapM fun line =>
    IO.ofExcept ((Json.parse line).bind Json.getArr? |>.bind readName)
  LeanExport.dumpEnv env (some roots)
