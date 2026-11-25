import Lean
open Lean

/-- usage: lean --run ListOwn.lean OUTFILE ROOTMODULE... ; lists the non-internal
constants declared in modules whose name has the prefix of one of PREFIX... (args after `--`) -/
def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let (roots, prefixes) := args.span (· != "--")
  let prefixes := prefixes.drop 1 |>.map String.toName
  let imports := roots.toArray.map fun m => { module := m.toName : Import }
  let env ← importModules imports {}
  let mut out : Array String := #[]
  for (n, _) in env.constants.map₁.toList do
    if n.isInternal then continue
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      if prefixes.any (·.isPrefixOf m) then out := out.push (toString (n.toString (escape := true)))
    | none => pure ()
  for s in out.qsort (· < ·) do IO.println s
