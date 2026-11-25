# Changelog

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
