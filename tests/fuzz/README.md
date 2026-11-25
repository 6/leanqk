# Differential fuzzing against Lean's kernel

`difffuzz` mutates valid exports so that most mutants should be rejected, runs
`nitrolean check` and Lean's `leanchecker --from-export` (Lean v4.36.0, pinned
in `../kernel/lean-toolchain`) on each, and records every mutant on which they
disagree about accept or reject. Crashes, timeouts and declined inputs are
recorded too, as anomalies.

Accepting good proofs is the easy half: the point is that nitrolean rejects
everything Lean rejects, and accepts nothing Lean would not.

## Running

`cargo xtask difffuzz` (the code is in `xtask/src/difffuzz/`). Build
nitrolean first (`cargo build --release`) and fetch the corpus (`cargo xtask
fetch-corpus`).

    cargo xtask difffuzz seeds                    # export and screen the seeds (about 2 minutes)
    cargo xtask difffuzz seeds --mathlib ~/mathlib4   # also the slices of seeds/mathlib-slices.txt
    cargo xtask difffuzz run --count 10000 --jobs 8   # mutants 0..9999 into tests/fuzz/out/run/
    cargo xtask difffuzz run --count 3000 --start 10000 --categories eval
    cargo xtask difffuzz summary                  # verdict pairs per category and operator
    cargo xtask difffuzz triage                   # disagreements grouped by message shape
    cargo xtask difffuzz replay 1234 > m.ndjson   # write mutant 1234 again
    cargo xtask difffuzz minimize tests/fuzz/out/run/disagree/eval-1234.ndjson
    cargo xtask difffuzz seed-corpus              # the cargo-fuzz corpora of fuzz/

`NITROLEAN` and `LEANCHECKER` override the two binaries, `FUZZ_TMP` where
mutants are written while they are checked (a tmpfs helps), and
`FUZZ_MEMORY_MB` the address-space limit of each checker run (6144 by
default; past it the run is an anomaly, not a hang of the machine). Each
check has a 30 s timeout. Every run appends to `OUT/results.jsonl` and skips
mutant numbers already in it, so an interrupted run resumes when run again.
`--base` picks another campaign: every mutant number gets a new plan.

## Seeds

Seeds are exports that both checkers accept:

- `out/seeds/fz-*.ndjson`: the closure of each theorem of `seeds/FuzzSeeds.lean`,
  exported on its own with `leanexport`. These are small proofs by `rfl` and
  `decide`, built for the mutations: Nat literal arithmetic (with every
  accelerated operation, around 2^32, 2^64 and up), recursion over Nat and lists,
  `Bool` and `decide` over bounded quantifiers, `Array` (push, set, get, map,
  fold, out of bounds), strings, `Fin` and `UInt`, structures with projections
  and eta, `Prop` structures, unit eta, K-like reduction, quotients, lets,
  de Bruijn indices, definitional heights, reducibility attributes, opaque
  constants, and inductive types (recursive, indexed, mutual, nested,
  reflexive, `Prop`-valued).
- the corpus (`corpus/exports/`) and the committed kernel cases
  (`tests/kernel/exports/`) that both accept;
- optionally, Mathlib slices: the closures of a few constants per line of
  `seeds/mathlib-slices.txt`.

`seeds` writes `tests/fuzz/out/seeds.tsv` with both verdicts for every candidate.
Seeds over 4 MB (32 MB for Mathlib slices) are left out.

## Mutations

A mutant changes one declaration of a seed. Changed terms are rebuilt along
their path to the root, so the hash-consed terms shared with other
declarations stay as they were. New records go right before the mutated
declaration. Nat literals are decimal strings, so values past 2^64 need no
big integers. A third of the mutants also drop every declaration after it. A
mutant is reproduced from its seed, category and number, so `results.jsonl`
does not store mutants that agree.

| category | operators (in `xtask/src/difffuzz/mutate.rs`) |
|---|---|
| `subterm` | a subterm replaced by another subterm of the same declaration that is in scope; a constant replaced by one of the same type (else the same universe arity); the arguments of `f a b` swapped; an argument dropped or duplicated; a theorem given another declaration's statement; a proof replaced by another theorem |
| `universe` | a `Sort` level changed (succ added or removed, zero, another parameter, `max`/`imax` swapped, an undeclared parameter); the universe arguments of a constant dropped, added, swapped or changed; a declaration's universe parameters dropped, duplicated, reordered or extended |
| `natlit` | a Nat literal perturbed (±1, doubled, halved, a bit flipped, values around 2^32 and 2^64); a string literal changed (a character added, removed or changed, non-ASCII and NUL included); a literal `n` written as `Nat.succ (n-1)` (should be accepted) |
| `inductive` | a count or flag of an inductive block changed (`numParams`, `numIndices`, `numFields`, `cidx`, `numMotives`, `numMinors`, `nfields`, `k`, `isRec`, `isReflexive`, `numNested`, `isUnsafe`, the `all` and `ctors` lists, a rule's constructor or right-hand side); a constructor, type or recursor term rewritten: a negative occurrence of a binder type (positivity), the final sort or a motive's sort changed, a bound variable redirected, a constant swapped for another of the block, a binder type swapped |
| `proj` | a projection's index or structure changed; a subterm wrapped in a projection or a projection removed; `x.i` expanded to `(S.mk x.0 … x.n).i` (structure eta: should be accepted), or the same with two fields swapped |
| `quot` | a `quot` declaration's kind, universe parameters or type changed; a quotient constant swapped for another one, or an argument of `Quot.lift`/`Quot.ind`/`Quot.mk` replaced |
| `let` | a `let`'s type and value swapped, its value replaced, its body shifted one binder, the `let` dropped; a literal written as `let x : Nat := n; x` (accept) or with `n+1`; a de Bruijn index shifted, or past its binders; a lambda turned into a Pi (or back), a binder type swapped |
| `hints` | reducibility hints changed (`abbrev`, `opaque`, other heights: should be accepted); definition, theorem, opaque and axiom turned into one another; safety flags; the `all` list |
| `eval` | on computation seeds: a number in a computation theorem's statement changed (its proof stays `rfl`/`decide`); a number or an operation in a definition the computation runs through; an accelerated operation swapped for a sibling (`Nat.add`/`Nat.mul`/…, `Nat.beq`/`Nat.ble`, `true`/`false`, `Array.push`/`Array.pop`, instances, `foldl`/`foldr`, `Decidable.isTrue`/`isFalse`) |
| `equiv` | mutations that should keep the export valid: binder names, binder info, an `mdata` node, literal unfolding, `let` introduction, hints |

The `eval` category draws only from computation seeds (`fz-n_*`, `fz-a_*`,
`fz-d_*`, …, kernel and corpus seeds named `eval` or `decide`, Mathlib
slices), so it goes through the evaluator of `src/check/eval/`.

## Results

`OUT/results.jsonl` has one line per mutant: seed, category, operator,
mutated declaration, both verdicts and times. Disagreements are copied to
`OUT/disagree/`, anomalies to `OUT/anomaly/`.

A disagreement of a class already understood gets a `known` tag
(`known` in `xtask/src/difffuzz/mod.rs`): the deliberate divergences of
`corpus/divergences.md` (a redefined built-in, a count over 2^32 that Lean
v4.36.0 truncates), and the classes found by earlier runs and recorded as
kernel cases. `triage` groups disagreements by direction and by the shape of
both messages, so a run of 100,000 mutants reads as a few dozen lines.

`minimize` shrinks a disagreement while both verdicts stay the same: the
shortest prefix of declarations, then single declarations and chunks dropped,
definitions and theorems turned into axioms, then unreferenced records dropped
and ids renumbered. Minimised disagreements that are real go to
`tests/kernel/` as cases (section "Disagreements with Lean found
by the differential fuzzer" of `xtask/src/kernel_cases/cases.rs`) with their
expected verdict; the ones nitrolean
still gets wrong are listed in `tests/kernel/open.tsv`.

## What this does not cover

`FINDINGS.md` has the results of the first campaigns and, under "Coverage
gaps", what the fuzzer and the tests do not reach.
