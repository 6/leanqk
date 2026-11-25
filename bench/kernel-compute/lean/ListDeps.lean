import Lean
open Lean

/-- usage: lean --run ListDeps.lean ROOTMODULE... -- PREFIX...
Lists the constants outside the modules with the given prefixes that are used directly by
(non-internal or internal) constants declared in those modules. Exporting these gives the
dependency closure without the own declarations. -/
def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let (roots, prefixes) := args.span (· != "--")
  let prefixes := prefixes.drop 1 |>.map String.toName
  let env ← importModules (roots.toArray.map fun m => { module := m.toName : Import }) {}
  let own (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some idx => prefixes.any (·.isPrefixOf env.header.moduleNames[idx.toNat]!)
    | none => false
  let mut deps : NameSet := {}
  for (n, ci) in env.constants.map₁.toList do
    if own n && !n.isInternal then
      for u in ci.getUsedConstantsAsSet.toList do
        if !own u && !u.isInternal then deps := deps.insert u
  for n in deps.toList.map (·.toString (escape := true)) |>.toArray.qsort (· < ·) do IO.println n
