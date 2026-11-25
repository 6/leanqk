# Changelog

## Unreleased

- Declarations are checked on several threads (`check --jobs N`, or
  `NITROLEAN_JOBS`; default: all cores). The verdict, and the failure
  reported, do not depend on it. While the process holds more than
  `NITROLEAN_MEM_BUDGET_MIB` (1 GiB by default), a thread starts a new
  block only if no other is busy. Known limitation: the budget is checked
  only when a block starts, so blocks that start together before memory
  grows all run. On the corpus, three neighbouring declarations of about
  2.6 GB each reach 5.3 GB on two threads (2.7 GB on one).
- A closed-term evaluator for proofs by kernel computation, with fast paths
  for `Nat`, `Int`, `Array` and `List` operations, the core `DecidableEq`
  instances, class methods such as `+` at a known instance and `casesOn`
  (so `match`), enabled on the definitions of known Lean versions
  (`docs/kernel-compute.md`). Arrays are persistent, so `set` and `push`
  take constant time even while an old version is still referenced.

## 0.1.0-alpha.1

Early pre-release.

- Checks Lean 4 NDJSON exports and compiled `.olean` files.
- Agrees with the expected verdicts on the public corpus (289 cases) and on the
  targeted kernel cases (173).
- Accepts all of Mathlib v4.36.0.
- Differs from Lean on purpose in a few cases, listed in
  `corpus/divergences.md`: built-ins with non-standard definitions, inductives
  declaring more parameters than their type has, and the order of structure
  eta.
