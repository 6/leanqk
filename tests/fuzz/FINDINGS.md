# Findings of the differential fuzzer

Campaigns against Lean v4.36.0's `leanchecker --from-export`:

- 13,000 mutants (12,593 generated) on 12 cores, 4,058 of them aimed at the
  kernel evaluator (`eval`), with the first version of the harness;
- 10,000 mutants (9,678 generated) with `cargo xtask difffuzz`, `--base 7`,
  every category;
- 20 minutes × 4 workers of each cargo-fuzz target (`fuzz/`).

| category | first campaign | second campaign |
|---|---:|---:|
| subterm | 960 | 1,046 |
| universe | 959 | 1,001 |
| natlit | 996 | 998 |
| inductive | 1,001 | 935 |
| proj | 981 | 1,045 |
| quot | 806 | 761 |
| let | 994 | 1,024 |
| hints | 962 | 977 |
| eval | 3,969 | 948 |
| equiv | 965 | 943 |

Verdict pairs (nitrolean/Lean), first and second campaign:
reject/reject 8,289 and 6,333; accept/accept 3,792 and 2,894; reject/accept
352 and 317; accept/reject 109 and 103; the rest are anomalies (below).

No mutant gave a proof of `False` that nitrolean accepts. All 881
disagreements (461 and 420) fall into the classes below. Each class has a minimised case in
`tests/kernel` (`fuzz-*`). The verdicts below describe the campaigns.
The nine open verdict cases now run with their corrected expectations in
`tests/kernel/cases.tsv`. The Nat literal resource failure below now returns
a diagnostic and a declined verdict.

## nitrolean accepts, Lean rejects

None of these lets a safe declaration prove anything false. They are
malformed declaration records that nitrolean is more lenient about.

| case | what |
|---|---|
| `fuzz-mdata-ctor-type`, `fuzz-mdata-rec-rule`, `fuzz-mdata-quot-type` | `mdata` inside a constructor type, a recursor rule or a quotient declaration's type. nitrolean sees through it. Lean compares these records structurally and rejects ("invalid return type", "Invalid recursor", "Quotient constant mismatch", also "invalid occurrence of datatype"). 196 mutants. |
| `fuzz-type-unsafe-flag`, `fuzz-type-unsafe-flag-neg` | an inductive block whose type record says `isUnsafe` while its constructors and recursor say safe. Lean rejects ("No such constructor"). nitrolean accepts the block as unsafe, so a non-positive type passes without the positivity check. Safe declarations that use it are still rejected ("uses unsafe declaration"); a forged proof of `False` through such a type was tried and rejected. 16 mutants. |

## nitrolean rejects, Lean accepts

| case | what |
|---|---|
| `fuzz-hints-regular-u32` (and `numParams` & co., 009_HB16279) | a `UInt32` field over 2^32 − 1: Lean v4.36.0 truncates it, nitrolean refuses it as malformed. This is the documented policy, so these mutants are tagged as known. 424 mutants. |
| `fuzz-ctor-unsafe-flag`, `fuzz-rec-unsafe-flag`, `fuzz-type-isrec-flag` | a constructor, recursor or type record whose derived fields (`isUnsafe`, `isRec`, `isReflexive`, `numNested`, …) are wrong. Lean derives them itself and ignores the exported values. nitrolean compares them and rejects. 241 mutants. |
| `fuzz-quot-type-alone` | the quot declaration of `Quot` without `Quot.mk`, `Quot.lift` and `Quot.ind`, and without their names in the name table: nitrolean says "unexpected quotient declaration". With the three names present but unused, it accepts. Lean accepts both. 2 mutants. |
| built-in internals | a mutant of a built-in's definition or of one of its auxiliaries (`Nat.shiftLeft._f`, `Nat.beq._f`, …), even one that keeps its meaning (a literal written as `Nat.succ n`). nitrolean then stops accelerating the built-in and fails or runs out of resources on the large literals of the proof that follows; Lean accelerates by name and accepts. This is the deliberate divergence of `historical/010_HB15908.contra`, and these mutants are tagged as known. 2 mutants. |

## Lean questionable

These are valid exports that Lean's `--from-export` path rejects. Lean
compiles them, `leanchecker` accepts the `.olean`, and `nitrolean compare`
finds the export identical to the `.olean`. nitrolean accepts them. Neither
is a soundness problem.

| case | what |
|---|---|
| `fuzz-str-deceq` | `decide ("abc" = "abc") = true` by `decide`: "application type mismatch", as if `String.decEq` did not reduce. |
| `fuzz-quot-lift-direct` | a theorem stated with `Quot.lift` and `Quot.mk`: "unknown constant Quot.lift". The verdict depends only on names: with the same export under other names (theorem, namespace, module, a hygienic name), Lean accepts. This points to the order in which `--from-export` replays declarations. |

## Robustness (no verdict)

The checkers ran with a 30 s timeout and a 6 GB address-space limit. Without
the limit, one mutant made the machine reach 30 GB.

- **nitrolean runs out of memory and aborts** on mutants of the Nat-literal
  corpus tests whose prelude it no longer recognises (built-in auxiliaries
  rewritten, `Unit.unit` made opaque, `OfNat.mk` or `Nat.below` renamed). The
  evaluator then reduces large literals by unfolding. Its stack segments
  (`stacker`) and its heap grow without bound. At the memory limit it panics
  in `stacker` ("mmap failed to allocate stack"), or an allocation of
  0.5–2 GB fails and it aborts (exit 134). Lean checks the same exports in
  0.01 s. The cargo-fuzz target `check_export` found the same thing:
  `arena/other/nat-lit-sub` with one changed name (`OfNat.mk` becomes
  `zero.mk`) or one changed index in `Nat.pred` runs for over 120 s and 6 GB.
  `nat-lit-ble` with `Nat.below` renamed takes 2 s and 3.5 GB. 14 such
  mutants in the second campaign, 9 timeouts in the first. Expected
  behaviour: a clean "declined" (exit 2) at a resource limit.
- **Lean crashes** (`INTERNAL PANIC: too many bound variables`, exit 1) on de
  Bruijn indices near 2^32: 40 mutants, all rejected by nitrolean. Three more
  Lean runs were killed (signal 9) under the memory limit.
- cargo-fuzz: `read_ndjson` (about 4.5 M executions, coverage 3,730) and
  `read_olean` (about 5 M executions, coverage 3,729) found nothing.
  `check_export` (coverage 11,362) found only the timeouts above. A reported
  leak in `read_ndjson` did not reproduce.

## Coverage gaps

What the current tests and this fuzzer do not exercise, in plain words:

- **Coordinated forgeries.** Every mutant changes one declaration. Real
  attacks change several records consistently: a type with its recursor and
  its rules, or a built-in redefined together with the lemmas about it. The
  fuzzer does not build those.
- **Bugs both checkers share.** Lean is the oracle. A wrong rule that
  nitrolean and Lean both implement, or a malformed input both accept, looks
  like agreement. Built-ins are the prominent case: if nitrolean's check that
  a built-in has its standard definition were too lax, it would accept the
  same false proof Lean accepts, and nobody would see a disagreement. A few
  accepted mutants of built-ins were checked by hand, and nitrolean did turn
  the fast path off. That check is not automatic: it needs a third checker,
  or a run with the built-ins turned off.
- **Deep definitional equality.** Most mutants are ill-typed in an obvious
  way, and both checkers reject them early. Only a third reach
  accept/accept, so lazy delta reduction, proof irrelevance under binders,
  eta for structures with parameters or indices, and K-like reduction with
  indices are hit rarely. The type-correct mutations (`equiv`) are few and
  cosmetic.
- **Kernel computation at scale.** The `eval` seeds are small closed
  computations: Nat literals up to 2^128 and some special values, arrays of
  tens of elements, short strings. Not covered: random large arithmetic,
  arrays near their size limits, `UInt` and `Fin` beyond a few operations,
  `String` operations beyond length and equality, `Decidable` instances
  built by Mathlib's tactics, and proofs by reflection.
- **Mathlib.** The slices of `seeds/mathlib-slices.txt` were not exported in
  these runs, so typeclass-heavy terms and Mathlib's `decide` proofs are not
  in the seed set.
- **Mutual and nested inductive types.** Nested types are translated through
  auxiliary types, and that translation is only touched by single-field
  changes. Reflexive types' recursor rules, and elimination restrictions
  (large elimination from `Prop`, subsingletons), are not targeted.
- **Universes.** There are no stress tests of level normalisation (deep
  `max`/`imax` terms, many parameters) and no instantiation with large
  levels.
- **Heights and hints.** They only change how fast things are checked, so
  the fuzzer sees a wrong unfolding order only as a timeout.
- **The `.olean` path.** The differential runs only on exports. `read_olean`
  looks for crashes, not wrong environments, and no fuzzer compares the
  `.olean` reader with the export.
- **Parallel checking.** The checker runs declarations on several threads.
  The fuzzer's exports are small and checked with default settings, so races
  are not targeted.
- **Format corner cases.** The JSON itself (duplicate keys, deep nesting,
  huge numbers, invalid UTF-8) is left to the cargo-fuzz targets. Those
  report crashes, not disagreements with Lean.
