# Changelog

## Unreleased

- Declarations are checked on several threads (`check --jobs N`, or
  `NITROLEAN_JOBS`; default: all cores). The verdict, and the failure
  reported, do not depend on it. While the process holds more than
  `NITROLEAN_MEM_BUDGET_MIB` (1 GiB by default), only one thread is busy.
- A closed-term evaluator for proofs by kernel computation, with fast paths
  for `Nat`, `Array` and `List` operations and the core `DecidableEq`
  instances, enabled on the definitions of known Lean versions
  (`docs/kernel-compute.md`).

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
