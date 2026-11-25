import Lean
open Lean

/-- usage: lean --run ListDepsOfNames.lean NAMESFILE ROOTMODULE...
Prints the constants used directly by the named constants (their types and values), without the
named ones themselves, and fails if one of them depends on an axiom other than
propext, Classical.choice and Quot.sound (for example the one `native_decide` adds). -/
def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match args with
  | file :: roots =>
    let names := (← IO.FS.readFile file).splitOn "\n" |>.filter (· ≠ "") |>.map String.toName
    let env ← importModules (roots.toArray.map fun m => { module := m.toName : Import }) {}
    let own := names.foldl (fun s n => s.insert n) ({} : NameSet)
    let mut deps : NameSet := {}
    let mut bad := false
    for n in names do
      let some ci := env.find? n | do IO.eprintln s!"unknown constant {n}"; return 1
      for u in ci.getUsedConstantsAsSet.toList do
        unless own.contains u do deps := deps.insert u
      let (axs, _) ← (collectAxioms n : CoreM _).toIO { fileName := "", fileMap := default } { env := env }
      for ax in axs do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          IO.eprintln s!"{n} depends on axiom {ax}"; bad := true
    if bad then return 1
    for n in deps.toList.map (·.toString (escape := true)) |>.toArray.qsort (· < ·) do IO.println n
    return 0
  | _ => IO.eprintln "usage: ListDepsOfNames NAMESFILE ROOTMODULE..."; return 2
