# Results: Lean Kernel Arena test set, 2026-11-25

nitrolean at commit `54d36c9` (0.1.0-alpha.1), run with `bench/arena/run.sh` (now `cargo xtask arena run`)
on all 270 tests of the arena at commit `8a7d0dce`. Every export was rebuilt
by `fetch.sh` (now `cargo xtask arena fetch`) and was byte-identical to the export the arena checked (270 of
270 SHA-256s). Raw rows: `run-2026-11-25.tsv`.

The machine is not the arena's: aarch64 Linux, 12 usable cores of a
heterogeneous CPU (Cortex-X925 and Cortex-A725), runs pinned to 8 of them
with `taskset -c 0-7`, one at a time, with the arena's timeouts doubled.
Those 8 cores mix fast and slow ones, so absolute times are not comparable
with the arena's 8-core amd64 runner. Times measured "here" are comparable
with each other. The "(arena)" columns are the arena's own published
numbers (`published.tsv`). Lean's checker is `leanchecker` of Lean v4.35.0,
as on the arena; gruszka (0.2.0) and nano-lean (v0.4.2) were built with
their arena build commands (PGO) and use 4 threads; nitrolean uses one.

## Summary

| checker | correct | either | declined | error or timeout | incorrect |
|---|---|---|---|---|---|
| nitrolean | 239 | 30 | 0 | 1 (reachability: timeout) | 0 |
| official (Lean v4.35.0) | 240 | 28 | 0 | 2 (two `either` corner cases: timeout, as on the arena) | 0 |
| gruszka | 240 | 30 | 0 | 0 | 0 |
| nano-lean | 239 | 28 | 3 (`bugs/nat-shift-huge`, two `either` corner cases) | 0 | 0 |

No checker gave a verdict opposite to the expected one. nitrolean's one
failure is `reachability` (6 proofs by `decide +kernel` over graph search):
killed at the 440 s timeout. An earlier run with a 32 GB memory limit was
killed for memory at 32.6 GB after 327 s.

Total wall time on the 261 small tests: nitrolean 133 s, official 429 s,
gruszka 15 s, nano-lean 23 s.

## Real-world tests

| test | expected | nitrolean | wall s | CPU s | peak RSS | official (here) | gruszka (here) | nano-lean (here) | official (arena) | gruszka (arena) | nano-lean (arena) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| cedar | accept | accept | 30.9 | 32.6 | 564 MiB | accept 82.3 s, 1.4 GiB | accept 2.38 s, 702 MiB | accept 4.17 s, 1.4 GiB | accept 97.1 s, 1.4 GiB | accept 4.33 s, 590 MiB | accept 5.46 s, 1.4 GiB |
| con-leche | accept | accept | 60.3 | 61.5 | 2.8 GiB | accept 130 s, 7.0 GiB | accept 1.97 s, 680 MiB | accept 3.59 s, 1.7 GiB | accept 168 s, 7.0 GiB | accept 2.85 s, 582 MiB | accept 4.63 s, 1.8 GiB |
| cslib | accept | accept | 151 | 156 | 1.6 GiB | accept 344 s, 3.5 GiB | accept 7.04 s, 1.4 GiB | accept 10.7 s, 2.4 GiB | accept 486 s, 3.5 GiB | accept 11.1 s, 1.2 GiB | accept 13.5 s, 2.4 GiB |
| init | accept | accept | 14.4 | 15.0 | 232 MiB | accept 35.7 s, 610 MiB | accept 0.90 s, 449 MiB | accept 1.58 s, 966 MiB | accept 46.7 s, 592 MiB | accept 1.32 s, 432 MiB | accept 1.79 s, 910 MiB |
| init-prelude | accept | accept | 0.04 | 0.05 | 9 MiB | accept 0.21 s, 117 MiB | accept 0.03 s, 165 MiB | accept 0.02 s, 166 MiB | accept 0.20 s, 100 MiB | accept 0.04 s, 152 MiB | accept 0.02 s, 163 MiB |
| mathlib | accept | accept | 613 | 624 | 4.6 GiB | accept 1578 s, 9.9 GiB | accept 19.4 s, 2.7 GiB | accept 29.1 s, 5.0 GiB | accept 2234 s, 9.9 GiB | accept 29.5 s, 2.6 GiB | accept 36.8 s, 5.0 GiB |
| navier-stokes-euler | accept | accept | 192 | 195 | 960 MiB | accept 443 s, 2.5 GiB | accept 4.83 s, 834 MiB | accept 7.13 s, 2.0 GiB | accept 676 s, 2.5 GiB | accept 5.92 s, 811 MiB | accept 8.36 s, 2.0 GiB |
| reachability | accept | **timeout** | 440 |  |  | accept 18.6 s, 1.6 GiB | accept 0.96 s, 901 MiB | accept 0.70 s, 1.4 GiB | accept 25.2 s, 1.6 GiB | accept 1.29 s, 860 MiB | accept 0.92 s, 1.3 GiB |
| std | accept | accept | 24.8 | 25.8 | 374 MiB | accept 61.3 s, 957 MiB | accept 1.57 s, 573 MiB | accept 2.66 s, 1.1 GiB | accept 87.9 s, 940 MiB | accept 2.12 s, 568 MiB | accept 3.12 s, 1.1 GiB |

## All tests

`MISMATCH` marks a verdict opposite to the expected one (there are none);
bold marks an error or timeout. Wall and CPU time in seconds.

| test | expected | nitrolean | wall s | CPU s | peak RSS | official (here) | gruszka (here) | nano-lean (here) | official (arena) | gruszka (arena) | nano-lean (arena) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| bugs/closure-level-subst | reject | reject | 0.01 | 0.01 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 81 MiB | reject 0.01 s, 24 MiB | reject 0.07 s, 102 MiB | reject 0.04 s, 68 MiB | reject 0.03 s, 16 MiB |
| bugs/constlevels | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 109 MiB | reject 0.02 s, 123 MiB | reject 0.01 s, 32 MiB | reject 0.04 s, 102 MiB | reject 0.02 s, 106 MiB | reject 0.01 s, 22 MiB |
| bugs/ctor-num-fields | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.05 s, 110 MiB | reject 0.02 s, 133 MiB | reject 0.01 s, 42 MiB | reject 0.12 s, 93 MiB | reject 0.02 s, 118 MiB | reject 0.01 s, 38 MiB |
| bugs/eta-ctor-alias | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 107 MiB | reject 0.01 s, 26 MiB | reject 0.04 s, 93 MiB | reject 0.02 s, 94 MiB | reject 0.01 s, 20 MiB |
| bugs/k-rec-conv | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 107 MiB | reject 0.01 s, 33 MiB | reject 0.04 s, 93 MiB | reject 0.02 s, 96 MiB | reject 0.01 s, 20 MiB |
| bugs/large-elim-param | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 109 MiB | reject 0.01 s, 87 MiB | reject 0.01 s, 26 MiB | reject 0.04 s, 102 MiB | reject 0.02 s, 68 MiB | reject 0.01 s, 20 MiB |
| bugs/large-elim-prop-bool | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 109 MiB | reject 0.02 s, 109 MiB | reject 0.01 s, 34 MiB | reject 0.04 s, 93 MiB | reject 0.07 s, 86 MiB | reject 0.01 s, 24 MiB |
| bugs/level-imax-leq | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 110 MiB | reject 0.01 s, 73 MiB | reject 0.01 s, 28 MiB | reject 0.04 s, 102 MiB | reject 0.02 s, 54 MiB | reject 0.01 s, 22 MiB |
| bugs/level-imax-normalization | reject | reject | 0.00 | 0.00 | 7 MiB | reject 0.04 s, 111 MiB | reject 0.02 s, 91 MiB | reject 0.01 s, 26 MiB | reject 0.04 s, 102 MiB | reject 0.02 s, 82 MiB | reject 0.01 s, 22 MiB |
| bugs/loose-bvar-value | reject | reject | 0.00 | 0.00 | 7 MiB | reject 0.04 s, 109 MiB | reject 0.02 s, 71 MiB | reject 0.00 s, 20 MiB | reject 0.04 s, 102 MiB | reject 0.02 s, 62 MiB | reject 0.01 s, 15 MiB |
| bugs/nat-rec-k-lie | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 110 MiB | reject 0.02 s, 81 MiB | reject 0.00 s, 28 MiB | reject 0.04 s, 103 MiB | reject 0.02 s, 78 MiB | reject 0.01 s, 22 MiB |
| bugs/nat-rec-rules | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 111 MiB | reject 0.02 s, 77 MiB | reject 0.01 s, 27 MiB | reject 0.04 s, 103 MiB | reject 0.02 s, 62 MiB | reject 0.01 s, 22 MiB |
| bugs/nat-shift-huge | accept | accept | 0.01 | 0.01 | 5 MiB | accept 0.07 s, 110 MiB | accept 0.02 s, 147 MiB | declined 11.4 s, 11.4 GiB | accept 0.09 s, 94 MiB | accept 0.03 s, 138 MiB | declined 12.8 s, 11.0 GiB |
| bugs/nested-name-capture | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 117 MiB | reject 0.00 s, 35 MiB | reject 0.04 s, 103 MiB | reject 0.03 s, 100 MiB | reject 0.01 s, 30 MiB |
| bugs/nested-rec-rule-nfields | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 115 MiB | reject 0.01 s, 38 MiB | reject 0.05 s, 93 MiB | reject 0.03 s, 104 MiB | reject 0.01 s, 30 MiB |
| bugs/nested-unused-param | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 112 MiB | reject 0.02 s, 121 MiB | reject 0.01 s, 45 MiB | reject 0.04 s, 93 MiB | reject 0.02 s, 114 MiB | reject 0.01 s, 36 MiB |
| bugs/open-term-cache-context | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 63 MiB | reject 0.01 s, 12 MiB | reject 0.04 s, 93 MiB | reject 0.02 s, 54 MiB | reject 0.01 s, 12 MiB |
| bugs/orphan-rec | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 109 MiB | reject 0.02 s, 61 MiB | reject 0.01 s, 18 MiB | reject 0.04 s, 102 MiB | reject 0.02 s, 54 MiB | reject 0.01 s, 12 MiB |
| bugs/pi-closure-context | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 75 MiB | reject 0.00 s, 22 MiB | reject 0.04 s, 102 MiB | reject 0.02 s, 64 MiB | reject 0.01 s, 13 MiB |
| bugs/proj-non-structure | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 110 MiB | reject 0.02 s, 93 MiB | reject 0.00 s, 28 MiB | reject 0.04 s, 93 MiB | reject 0.02 s, 84 MiB | reject 0.01 s, 20 MiB |
| bugs/proj-of-imax-prop | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 101 MiB | reject 0.01 s, 30 MiB | reject 0.04 s, 93 MiB | reject 0.02 s, 92 MiB | reject 0.01 s, 24 MiB |
| bugs/proj-of-stuck-prop | reject | reject | 0.01 | 0.01 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 157 MiB | reject 0.01 s, 72 MiB | reject 0.05 s, 93 MiB | reject 0.02 s, 148 MiB | reject 0.01 s, 60 MiB |
| bugs/proj-of-subst-prop | reject | reject | 0.01 | 0.01 | 5 MiB | reject 0.06 s, 110 MiB | reject 0.02 s, 153 MiB | reject 0.01 s, 66 MiB | reject 0.05 s, 94 MiB | reject 0.02 s, 142 MiB | reject 0.01 s, 56 MiB |
| bugs/quot-bad-type | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 83 MiB | reject 0.01 s, 26 MiB | reject 0.04 s, 93 MiB | reject 0.02 s, 68 MiB | reject 0.01 s, 20 MiB |
| bugs/rec-k-lie | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 85 MiB | reject 0.01 s, 22 MiB | reject 0.04 s, 93 MiB | reject 0.02 s, 64 MiB | reject 0.01 s, 22 MiB |
| bugs/rec-missing-ih | reject | reject | 0.01 | 0.01 | 5 MiB | reject 0.05 s, 111 MiB | reject 0.02 s, 155 MiB | reject 0.01 s, 74 MiB | reject 0.06 s, 104 MiB | reject 0.02 s, 148 MiB | reject 0.01 s, 63 MiB |
| bugs/rec-of-subst-prop | reject | reject | 0.01 | 0.01 | 7 MiB | reject 0.06 s, 110 MiB | reject 0.02 s, 149 MiB | reject 0.01 s, 78 MiB | reject 0.05 s, 94 MiB | reject 0.02 s, 142 MiB | reject 0.01 s, 68 MiB |
| bugs/rec-rule-proof-irrel | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 121 MiB | reject 0.01 s, 33 MiB | reject 0.04 s, 94 MiB | reject 0.02 s, 106 MiB | reject 0.01 s, 24 MiB |
| bugs/rec-rule-proof-irrel-nested | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 110 MiB | reject 0.02 s, 129 MiB | reject 0.01 s, 31 MiB | reject 0.04 s, 94 MiB | reject 0.02 s, 122 MiB | reject 0.01 s, 32 MiB |
| bugs/rec-rule-wrong-arg | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 112 MiB | reject 0.02 s, 131 MiB | reject 0.01 s, 38 MiB | reject 0.04 s, 94 MiB | reject 0.02 s, 122 MiB | reject 0.03 s, 28 MiB |
| bugs/rec-type-proof-irrel | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 110 MiB | reject 0.02 s, 119 MiB | reject 0.01 s, 31 MiB | reject 0.04 s, 94 MiB | reject 0.02 s, 104 MiB | reject 0.01 s, 28 MiB |
| bugs/str-lit-utf8 | accept | accept | 0.01 | 0.01 | 5 MiB | accept 0.07 s, 113 MiB | accept 0.02 s, 147 MiB | accept 0.01 s, 96 MiB | accept 0.06 s, 96 MiB | accept 0.03 s, 138 MiB | accept 0.01 s, 88 MiB |
| bugs/str-lit-utf8-bad | reject | reject | 0.02 | 0.02 | 6 MiB | reject 0.09 s, 114 MiB | reject 0.02 s, 153 MiB | reject 0.01 s, 100 MiB | reject 0.07 s, 98 MiB | reject 0.03 s, 134 MiB | reject 0.01 s, 92 MiB |
| bugs/unit-rec-rule | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 79 MiB | reject 0.01 s, 28 MiB | reject 0.05 s, 103 MiB | reject 0.02 s, 72 MiB | reject 0.01 s, 24 MiB |
| cedar | accept | accept | 30.9 | 32.6 | 564 MiB | accept 82.3 s, 1.4 GiB | accept 2.38 s, 702 MiB | accept 4.17 s, 1.4 GiB | accept 97.1 s, 1.4 GiB | accept 4.33 s, 590 MiB | accept 5.46 s, 1.4 GiB |
| con-leche | accept | accept | 60.3 | 61.5 | 2.8 GiB | accept 130 s, 7.0 GiB | accept 1.97 s, 680 MiB | accept 3.59 s, 1.7 GiB | accept 168 s, 7.0 GiB | accept 2.85 s, 582 MiB | accept 4.63 s, 1.8 GiB |
| corner-cases/alg-conv-trans-acc | either | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 139 MiB | reject 0.01 s, 43 MiB | reject 0.05 s, 94 MiB | reject 0.03 s, 124 MiB | reject 0.01 s, 38 MiB |
| corner-cases/alg-conv-trans-acc-left | either | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.02 s, 135 MiB | accept 0.01 s, 40 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 128 MiB | accept 0.01 s, 32 MiB |
| corner-cases/alg-conv-trans-acc-right | either | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 135 MiB | accept 0.01 s, 43 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 124 MiB | accept 0.01 s, 38 MiB |
| corner-cases/alg-conv-trans-quot | either | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 110 MiB | reject 0.01 s, 81 MiB | reject 0.00 s, 26 MiB | reject 0.04 s, 93 MiB | reject 0.02 s, 70 MiB | reject 0.01 s, 18 MiB |
| corner-cases/alg-conv-trans-quot-left | either | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 83 MiB | reject 0.00 s, 26 MiB | reject 0.04 s, 93 MiB | reject 0.02 s, 70 MiB | reject 0.01 s, 20 MiB |
| corner-cases/alg-conv-trans-quot-left-def | either | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 111 MiB | accept 0.02 s, 89 MiB | accept 0.00 s, 28 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 76 MiB | accept 0.01 s, 24 MiB |
| corner-cases/alg-conv-trans-quot-right | either | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.01 s, 83 MiB | accept 0.00 s, 26 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 74 MiB | accept 0.01 s, 20 MiB |
| corner-cases/eta-ctor | either | reject | 0.00 | 0.00 | 7 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 101 MiB | reject 0.00 s, 28 MiB | reject 0.04 s, 94 MiB | reject 0.03 s, 82 MiB | reject 0.01 s, 20 MiB |
| corner-cases/eta-rec-struct | either | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 97 MiB | reject 0.00 s, 28 MiB | reject 0.04 s, 93 MiB | reject 0.02 s, 86 MiB | reject 0.01 s, 24 MiB |
| corner-cases/eta-rule-k | either | reject | 0.00 | 0.00 | 7 MiB | reject 0.03 s, 110 MiB | reject 0.01 s, 85 MiB | reject 0.00 s, 26 MiB | reject 0.04 s, 94 MiB | reject 0.02 s, 76 MiB | reject 0.01 s, 20 MiB |
| corner-cases/eta-struct-major-and | either | accept | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | accept 0.02 s, 115 MiB | reject 0.00 s, 32 MiB | reject 0.04 s, 94 MiB | accept 0.02 s, 94 MiB | reject 0.01 s, 24 MiB |
| corner-cases/eta-struct-major-and-no-whnf | either | accept | 0.00 | 0.00 | 5 MiB | timeout 120 s, 20 MiB | accept 0.02 s, 111 MiB | declined 1.27 s, 3.5 GiB | timeout 60.0 s, 0 MiB | accept 0.02 s, 106 MiB | declined 3.12 s, 3.5 GiB |
| corner-cases/eta-struct-major-no-whnf | either | accept | 0.00 | 0.00 | 5 MiB | timeout 120 s, 22 MiB | accept 0.02 s, 123 MiB | declined 1.28 s, 3.5 GiB | timeout 60.0 s, 0 MiB | accept 0.02 s, 84 MiB | declined 2.01 s, 3.5 GiB |
| corner-cases/eta-unit-like-nested | either | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 103 MiB | reject 0.01 s, 32 MiB | reject 0.04 s, 93 MiB | reject 0.02 s, 92 MiB | reject 0.01 s, 28 MiB |
| corner-cases/eta-unit-like-pi | either | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 79 MiB | reject 0.00 s, 26 MiB | reject 0.04 s, 94 MiB | reject 0.02 s, 82 MiB | reject 0.01 s, 20 MiB |
| corner-cases/eta-unit-like-proof-field | either | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 110 MiB | reject 0.02 s, 99 MiB | reject 0.00 s, 28 MiB | reject 0.05 s, 93 MiB | reject 0.02 s, 82 MiB | reject 0.01 s, 24 MiB |
| corner-cases/eta-unit-like-struct | either | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 112 MiB | reject 0.02 s, 95 MiB | reject 0.01 s, 28 MiB | reject 0.04 s, 93 MiB | reject 0.02 s, 92 MiB | reject 0.01 s, 22 MiB |
| corner-cases/imax-nested-absorption | either | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 110 MiB | reject 0.01 s, 61 MiB | accept 0.00 s, 14 MiB | reject 0.04 s, 93 MiB | reject 0.02 s, 50 MiB | accept 0.01 s, 10 MiB |
| corner-cases/imax-right-successor | either | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 110 MiB | reject 0.02 s, 59 MiB | accept 0.00 s, 12 MiB | reject 0.04 s, 93 MiB | reject 0.02 s, 56 MiB | accept 0.01 s, 10 MiB |
| corner-cases/large-elim-maybe-prop | either | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 109 MiB | reject 0.01 s, 73 MiB | reject 0.00 s, 24 MiB | reject 0.03 s, 102 MiB | reject 0.02 s, 54 MiB | reject 0.01 s, 18 MiB |
| corner-cases/let-value-type-mismatch | either | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 109 MiB | reject 0.02 s, 53 MiB | reject 0.00 s, 10 MiB | reject 0.03 s, 102 MiB | reject 0.03 s, 46 MiB | reject 0.01 s, 10 MiB |
| corner-cases/nested-nonuniform-param | either | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 109 MiB | accept 0.01 s, 93 MiB | accept 0.01 s, 26 MiB | reject 0.04 s, 93 MiB | accept 0.02 s, 76 MiB | accept 0.01 s, 24 MiB |
| corner-cases/nested-redex-aux | either | accept | 0.00 | 0.00 | 5 MiB | accept 0.05 s, 109 MiB | accept 0.02 s, 113 MiB | accept 0.01 s, 39 MiB | accept 0.04 s, 92 MiB | accept 0.03 s, 94 MiB | accept 0.01 s, 30 MiB |
| corner-cases/positivity-whnf | either | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 109 MiB | reject 0.02 s, 83 MiB | reject 0.00 s, 24 MiB | reject 0.03 s, 102 MiB | reject 0.02 s, 72 MiB | reject 0.01 s, 20 MiB |
| corner-cases/proj-maybe-prop | either | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.01 s, 93 MiB | accept 0.00 s, 31 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 84 MiB | accept 0.01 s, 24 MiB |
| corner-cases/proj-maybe-prop-past | either | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 95 MiB | accept 0.00 s, 26 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 94 MiB | accept 0.01 s, 24 MiB |
| corner-cases/proof-param-ok | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 63 MiB | accept 0.01 s, 18 MiB | accept 0.03 s, 101 MiB | accept 0.02 s, 60 MiB | accept 0.01 s, 13 MiB |
| corner-cases/proof-param-swap | either | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 109 MiB | reject 0.01 s, 65 MiB | reject 0.00 s, 18 MiB | reject 0.03 s, 102 MiB | reject 0.02 s, 60 MiB | reject 0.01 s, 14 MiB |
| corner-cases/subject-reduction-redex | either | accept | 0.01 | 0.01 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 135 MiB | accept 0.01 s, 47 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 124 MiB | accept 0.01 s, 38 MiB |
| corner-cases/subject-reduction-reduct | either | reject | 0.01 | 0.01 | 5 MiB | reject 0.05 s, 110 MiB | reject 0.02 s, 133 MiB | reject 0.01 s, 42 MiB | reject 0.04 s, 94 MiB | reject 0.02 s, 124 MiB | reject 0.01 s, 24 MiB |
| corner-cases/vanishing-occurrence | either | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 87 MiB | accept 0.00 s, 22 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 78 MiB | accept 0.01 s, 18 MiB |
| cslib | accept | accept | 151 | 156 | 1.6 GiB | accept 344 s, 3.5 GiB | accept 7.04 s, 1.4 GiB | accept 10.7 s, 2.4 GiB | accept 486 s, 3.5 GiB | accept 11.1 s, 1.2 GiB | accept 13.5 s, 2.4 GiB |
| init | accept | accept | 14.4 | 15.0 | 232 MiB | accept 35.7 s, 610 MiB | accept 0.90 s, 449 MiB | accept 1.58 s, 966 MiB | accept 46.7 s, 592 MiB | accept 1.32 s, 432 MiB | accept 1.79 s, 910 MiB |
| init-prelude | accept | accept | 0.04 | 0.05 | 9 MiB | accept 0.21 s, 117 MiB | accept 0.03 s, 165 MiB | accept 0.02 s, 166 MiB | accept 0.20 s, 100 MiB | accept 0.04 s, 152 MiB | accept 0.02 s, 163 MiB |
| mathlib | accept | accept | 613 | 624 | 4.6 GiB | accept 1578 s, 9.9 GiB | accept 19.4 s, 2.7 GiB | accept 29.1 s, 5.0 GiB | accept 2234 s, 9.9 GiB | accept 29.5 s, 2.6 GiB | accept 36.8 s, 5.0 GiB |
| navier-stokes-euler | accept | accept | 192 | 195 | 960 MiB | accept 443 s, 2.5 GiB | accept 4.83 s, 834 MiB | accept 7.13 s, 2.0 GiB | accept 676 s, 2.5 GiB | accept 5.92 s, 811 MiB | accept 8.36 s, 2.0 GiB |
| other/extra-rec | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 109 MiB | reject 0.02 s, 63 MiB | reject 0.00 s, 20 MiB | reject 0.03 s, 102 MiB | reject 0.01 s, 38 MiB | reject 0.01 s, 11 MiB |
| other/inductive-undeclared-universe | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 109 MiB | reject 0.02 s, 63 MiB | reject 0.01 s, 18 MiB | reject 0.04 s, 102 MiB | reject 0.01 s, 44 MiB | reject 0.01 s, 12 MiB |
| other/level-index-out-of-order | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 108 MiB | accept 0.02 s, 55 MiB | accept 0.00 s, 8 MiB | accept 0.03 s, 101 MiB | accept 0.02 s, 44 MiB | accept 0.01 s, 8 MiB |
| other/nat-lit-add | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.02 s, 123 MiB | accept 0.00 s, 33 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 66 MiB | accept 0.01 s, 28 MiB |
| other/nat-lit-add-bad | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 127 MiB | reject 0.01 s, 33 MiB | reject 0.04 s, 93 MiB | reject 0.02 s, 106 MiB | reject 0.01 s, 28 MiB |
| other/nat-lit-ble | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 127 MiB | accept 0.01 s, 37 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 104 MiB | accept 0.01 s, 30 MiB |
| other/nat-lit-sub | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.02 s, 105 MiB | accept 0.01 s, 37 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 104 MiB | accept 0.01 s, 30 MiB |
| other/orphan-ctor | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 109 MiB | reject 0.02 s, 61 MiB | reject 0.00 s, 20 MiB | reject 0.03 s, 102 MiB | reject 0.01 s, 34 MiB | reject 0.01 s, 12 MiB |
| other/proj-of-prop | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 112 MiB | reject 0.02 s, 91 MiB | reject 0.00 s, 26 MiB | reject 0.04 s, 93 MiB | reject 0.02 s, 74 MiB | reject 0.01 s, 16 MiB |
| other/sparse-name-index | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 108 MiB | accept 0.01 s, 53 MiB | accept 0.00 s, 8 MiB | accept 0.03 s, 101 MiB | accept 0.01 s, 44 MiB | accept 0.01 s, 8 MiB |
| perf/app-lam | accept | accept | 5.71 | 5.71 | 1.1 GiB | accept 2.48 s, 1.4 GiB | accept 0.07 s, 154 MiB | accept 0.01 s, 72 MiB | accept 2.39 s, 1.4 GiB | accept 0.06 s, 150 MiB | accept 0.02 s, 66 MiB |
| perf/args-before-unfold | accept | accept | 0.01 | 0.01 | 5 MiB | accept 0.05 s, 109 MiB | accept 0.02 s, 92 MiB | accept 0.01 s, 36 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 86 MiB | accept 0.01 s, 30 MiB |
| perf/beta-ladder | accept | accept | 1.23 | 1.23 | 319 MiB | accept 0.82 s, 543 MiB | accept 0.04 s, 126 MiB | accept 0.01 s, 52 MiB | accept 0.78 s, 526 MiB | accept 0.04 s, 121 MiB | accept 0.01 s, 46 MiB |
| perf/church-numerals | accept | accept | 0.01 | 0.01 | 11 MiB | accept 0.06 s, 122 MiB | accept 0.02 s, 99 MiB | accept 0.01 s, 40 MiB | accept 0.05 s, 104 MiB | accept 0.03 s, 101 MiB | accept 0.01 s, 32 MiB |
| perf/discarded-argument | accept | accept | 0.04 | 0.04 | 5 MiB | accept 0.08 s, 109 MiB | accept 0.02 s, 103 MiB | accept 0.00 s, 28 MiB | accept 0.13 s, 92 MiB | accept 0.03 s, 84 MiB | accept 0.01 s, 24 MiB |
| perf/discarded-argument-match | accept | accept | 0.05 | 0.04 | 5 MiB | accept 0.09 s, 111 MiB | accept 0.01 s, 121 MiB | accept 0.00 s, 36 MiB | accept 0.07 s, 94 MiB | accept 0.02 s, 98 MiB | accept 0.01 s, 22 MiB |
| perf/folded-constant-first | accept | accept | 0.01 | 0.01 | 5 MiB | accept 0.05 s, 112 MiB | accept 0.02 s, 92 MiB | accept 0.01 s, 44 MiB | accept 0.04 s, 95 MiB | accept 0.02 s, 85 MiB | accept 0.01 s, 35 MiB |
| perf/folded-constant-last | accept | accept | 0.01 | 0.01 | 5 MiB | accept 0.04 s, 114 MiB | accept 0.02 s, 116 MiB | accept 0.01 s, 40 MiB | accept 0.04 s, 95 MiB | accept 0.05 s, 103 MiB | accept 0.01 s, 43 MiB |
| perf/fueled-chain | accept | accept | 0.03 | 0.03 | 8 MiB | accept 0.10 s, 118 MiB | accept 0.03 s, 157 MiB | accept 0.02 s, 117 MiB | accept 0.08 s, 102 MiB | accept 0.04 s, 146 MiB | accept 0.02 s, 119 MiB |
| perf/gf3-matrix-product | accept | accept | 9.89 | 9.89 | 3.2 GiB | accept 2.07 s, 3.6 GiB | accept 1.35 s, 325 MiB | accept 0.53 s, 3.6 GiB | accept 2.73 s, 3.5 GiB | accept 1.37 s, 364 MiB | accept 0.81 s, 3.6 GiB |
| perf/grind-ring-5 | accept | accept | 0.55 | 0.56 | 60 MiB | accept 1.25 s, 271 MiB | accept 0.15 s, 288 MiB | accept 0.16 s, 336 MiB | accept 1.38 s, 254 MiB | accept 0.20 s, 278 MiB | accept 0.17 s, 329 MiB |
| perf/identical-nesting | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.01 s, 95 MiB | accept 0.01 s, 26 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 78 MiB | accept 0.01 s, 22 MiB |
| perf/irrelevance-before-evaluation | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 95 MiB | accept 0.01 s, 32 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 84 MiB | accept 0.01 s, 28 MiB |
| perf/irrelevance-refutes | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.02 s, 109 MiB | accept 0.01 s, 27 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 90 MiB | accept 0.01 s, 24 MiB |
| perf/ite-taken-branch | accept | accept | 9.17 | 9.17 | 386 MiB | accept 14.0 s, 1.7 GiB | accept 0.03 s, 171 MiB | accept 0.03 s, 194 MiB | accept 16.4 s, 1.7 GiB | accept 0.04 s, 165 MiB | accept 0.03 s, 179 MiB |
| perf/ite-taken-branch-bad | reject | reject | 3.09 | 3.09 | 387 MiB | reject 4.86 s, 1.7 GiB | reject 0.36 s, 447 MiB | reject 0.17 s, 347 MiB | reject 5.98 s, 1.7 GiB | reject 0.46 s, 428 MiB | reject 0.20 s, 324 MiB |
| perf/let-fold | accept | accept | 0.01 | 0.01 | 5 MiB | accept 0.07 s, 111 MiB | accept 0.02 s, 147 MiB | accept 0.01 s, 82 MiB | accept 0.06 s, 94 MiB | accept 0.05 s, 138 MiB | accept 0.01 s, 69 MiB |
| perf/let-ladder | accept | accept | 0.54 | 0.54 | 166 MiB | accept 0.52 s, 347 MiB | accept 0.02 s, 125 MiB | accept 0.01 s, 56 MiB | accept 0.49 s, 330 MiB | accept 0.02 s, 101 MiB | accept 0.01 s, 51 MiB |
| perf/loop-unfolded-once | accept | accept | 0.09 | 0.09 | 10 MiB | accept 0.28 s, 120 MiB | accept 0.03 s, 178 MiB | accept 0.02 s, 183 MiB | accept 0.28 s, 102 MiB | accept 0.04 s, 170 MiB | accept 0.03 s, 182 MiB |
| perf/loop-unfolded-once-bad | reject | reject | 0.68 | 0.68 | 10 MiB | reject 6.40 s, 118 MiB | reject 0.03 s, 180 MiB | reject 0.03 s, 183 MiB | reject 6.89 s, 104 MiB | reject 0.04 s, 172 MiB | reject 0.03 s, 166 MiB |
| perf/magma-list-deep-n21 | accept | accept | 1.32 | 1.32 | 153 MiB | accept 1.78 s, 705 MiB | accept 0.04 s, 179 MiB | accept 0.03 s, 151 MiB | accept 2.25 s, 688 MiB | accept 0.05 s, 170 MiB | accept 0.04 s, 144 MiB |
| perf/magma-list-deep-n36 | accept | accept | 33.3 | 33.3 | 1.4 GiB | accept 34.6 s, 7.8 GiB | accept 0.32 s, 332 MiB | accept 0.22 s, 455 MiB | accept 42.8 s, 7.8 GiB | accept 0.35 s, 321 MiB | accept 0.34 s, 443 MiB |
| perf/magma-list-pair-n21 | accept | accept | 16.7 | 16.7 | 2.2 GiB | accept 15.9 s, 4.0 GiB | accept 2.50 s, 1.0 GiB | accept 2.06 s, 1.8 GiB | accept 20.8 s, 4.0 GiB | accept 4.45 s, 986 MiB | accept 3.00 s, 1.8 GiB |
| perf/magma-list-pair-n7 | accept | accept | 0.96 | 0.96 | 192 MiB | accept 1.33 s, 471 MiB | accept 0.20 s, 309 MiB | accept 0.15 s, 268 MiB | accept 1.75 s, 455 MiB | accept 0.28 s, 294 MiB | accept 0.29 s, 280 MiB |
| perf/magma-string-n4 | accept | accept | 0.72 | 0.74 | 30 MiB | accept 1.84 s, 164 MiB | accept 0.08 s, 217 MiB | accept 0.11 s, 382 MiB | accept 2.55 s, 150 MiB | accept 0.12 s, 202 MiB | accept 0.17 s, 373 MiB |
| perf/magma-string-pair-n9 | accept | accept | 3.11 | 3.13 | 303 MiB | accept 4.99 s, 1.0 GiB | accept 0.31 s, 407 MiB | accept 0.26 s, 510 MiB | accept 6.55 s, 1008 MiB | accept 0.40 s, 392 MiB | accept 0.33 s, 494 MiB |
| perf/proj-app-lazy-delta | accept | accept | 1.46 | 1.46 | 307 MiB | accept 2.04 s, 622 MiB | accept 0.02 s, 143 MiB | accept 0.01 s, 50 MiB | accept 2.53 s, 612 MiB | accept 0.02 s, 138 MiB | accept 0.01 s, 48 MiB |
| perf/proj-applied-struct | accept | accept | 8.37 | 8.37 | 531 MiB | accept 15.7 s, 1.4 GiB | accept 0.02 s, 145 MiB | accept 0.01 s, 51 MiB | accept 21.3 s, 1.4 GiB | accept 0.05 s, 136 MiB | accept 0.01 s, 41 MiB |
| perf/proj-applied-struct-arg-bad | reject | reject | 2.75 | 2.75 | 513 MiB | reject 5.34 s, 1.4 GiB | reject 0.83 s, 668 MiB | reject 0.82 s, 3.3 GiB | reject 6.99 s, 1.4 GiB | reject 1.09 s, 621 MiB | reject 1.29 s, 3.2 GiB |
| perf/proj-applied-struct-bad | reject | reject | 2.76 | 2.76 | 512 MiB | reject 5.60 s, 1.4 GiB | reject 0.77 s, 662 MiB | reject 0.69 s, 1.1 GiB | reject 7.30 s, 1.4 GiB | reject 1.12 s, 614 MiB | reject 0.98 s, 1.1 GiB |
| perf/proj-cheap-struct | accept | accept | 0.01 | 0.01 | 5 MiB | accept 0.05 s, 109 MiB | accept 0.02 s, 129 MiB | accept 0.01 s, 44 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 118 MiB | accept 0.02 s, 40 MiB |
| perf/proj-lazy-struct | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 121 MiB | accept 0.00 s, 40 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 96 MiB | accept 0.01 s, 32 MiB |
| perf/proj-stuck-struct | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.02 s, 119 MiB | accept 0.01 s, 43 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 110 MiB | accept 0.01 s, 28 MiB |
| perf/prop-struct-projections | accept | accept | 0.02 | 0.02 | 5 MiB | accept 0.09 s, 113 MiB | accept 0.02 s, 129 MiB | accept 0.01 s, 127 MiB | accept 0.07 s, 96 MiB | accept 0.02 s, 124 MiB | accept 0.01 s, 123 MiB |
| perf/refute-cheap-first | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.05 s, 110 MiB | reject 0.02 s, 107 MiB | reject 0.01 s, 35 MiB | reject 0.05 s, 93 MiB | reject 0.02 s, 84 MiB | reject 0.01 s, 28 MiB |
| perf/refute-cheap-last | reject | reject | 0.05 | 0.05 | 5 MiB | reject 0.12 s, 110 MiB | reject 0.02 s, 105 MiB | reject 0.01 s, 34 MiB | reject 0.10 s, 93 MiB | reject 0.02 s, 88 MiB | reject 0.01 s, 32 MiB |
| perf/repeated-subproblem | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.05 s, 109 MiB | accept 0.02 s, 91 MiB | accept 0.01 s, 30 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 88 MiB | accept 0.01 s, 26 MiB |
| perf/shared-subterm | accept | accept | 0.01 | 0.01 | 6 MiB | accept 0.06 s, 116 MiB | accept 0.02 s, 108 MiB | accept 0.01 s, 52 MiB | accept 0.05 s, 99 MiB | accept 0.02 s, 91 MiB | accept 0.01 s, 45 MiB |
| perf/shift-cascade | accept | accept | 0.01 | 0.01 | 5 MiB | accept 0.06 s, 111 MiB | accept 0.02 s, 94 MiB | accept 0.01 s, 49 MiB | accept 0.05 s, 94 MiB | accept 0.02 s, 85 MiB | accept 0.01 s, 36 MiB |
| perf/short-circuit-and | accept | accept | 7.88 | 7.89 | 360 MiB | accept 14.0 s, 1.5 GiB | accept 0.03 s, 178 MiB | accept 0.02 s, 198 MiB | accept 18.1 s, 1.5 GiB | accept 0.04 s, 166 MiB | accept 0.03 s, 185 MiB |
| perf/short-circuit-and-bad | reject | reject | 2.65 | 2.65 | 360 MiB | reject 4.69 s, 1.5 GiB | reject 1.73 s, 536 MiB | reject 0.13 s, 300 MiB | reject 6.38 s, 1.5 GiB | reject 2.18 s, 529 MiB | reject 0.16 s, 296 MiB |
| perf/unfold-before-literal | accept | accept | 8.11 | 8.11 | 532 MiB | accept 16.3 s, 1.4 GiB | accept 0.02 s, 123 MiB | accept 0.79 s, 3.2 GiB | accept 21.3 s, 1.4 GiB | accept 0.02 s, 96 MiB | accept 1.31 s, 3.2 GiB |
| perf/unfold-before-literal-bad | reject | reject | 2.79 | 2.79 | 511 MiB | reject 5.61 s, 1.4 GiB | reject 0.77 s, 650 MiB | reject 0.68 s, 1.1 GiB | reject 7.31 s, 1.4 GiB | reject 1.18 s, 603 MiB | reject 0.99 s, 1.1 GiB |
| perf/unfold-before-literal-fallback | accept | accept | 8.08 | 8.08 | 532 MiB | accept 16.6 s, 1.4 GiB | accept 1.77 s, 1.2 GiB | accept 0.99 s, 2.9 GiB | accept 22.4 s, 1.4 GiB | accept 2.65 s, 1.1 GiB | accept 1.31 s, 3.1 GiB |
| perf/unroll-versus-evaluate | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.02 s, 87 MiB | accept 0.01 s, 32 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 88 MiB | accept 0.01 s, 26 MiB |
| reachability | accept | **timeout** | 440 |  |  | accept 18.6 s, 1.6 GiB | accept 0.96 s, 901 MiB | accept 0.70 s, 1.4 GiB | accept 25.2 s, 1.6 GiB | accept 1.29 s, 860 MiB | accept 0.92 s, 1.3 GiB |
| std | accept | accept | 24.8 | 25.8 | 374 MiB | accept 61.3 s, 957 MiB | accept 1.57 s, 573 MiB | accept 2.66 s, 1.1 GiB | accept 87.9 s, 940 MiB | accept 2.12 s, 568 MiB | accept 3.12 s, 1.1 GiB |
| tutorial/001_basicDef | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 108 MiB | accept 0.01 s, 43 MiB | accept 0.00 s, 8 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 51 MiB | accept 0.01 s, 8 MiB |
| tutorial/002_badDef | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 110 MiB | reject 0.01 s, 55 MiB | reject 0.00 s, 8 MiB | reject 0.05 s, 93 MiB | reject 0.02 s, 46 MiB | reject 0.01 s, 8 MiB |
| tutorial/003_arrowType | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 108 MiB | accept 0.02 s, 57 MiB | accept 0.00 s, 12 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 50 MiB | accept 0.01 s, 11 MiB |
| tutorial/004_dependentType | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 59 MiB | accept 0.00 s, 10 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 50 MiB | accept 0.01 s, 10 MiB |
| tutorial/005_constType | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 59 MiB | accept 0.00 s, 12 MiB | accept 0.06 s, 92 MiB | accept 0.02 s, 50 MiB | accept 0.01 s, 12 MiB |
| tutorial/006_betaReduction | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.01 s, 67 MiB | accept 0.00 s, 14 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 58 MiB | accept 0.01 s, 11 MiB |
| tutorial/007_betaReduction2 | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 65 MiB | accept 0.00 s, 14 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 58 MiB | accept 0.01 s, 11 MiB |
| tutorial/008_forallSortWhnf | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.02 s, 69 MiB | accept 0.00 s, 14 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 60 MiB | accept 0.01 s, 12 MiB |
| tutorial/009_forallSortBad | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 112 MiB | reject 0.02 s, 69 MiB | reject 0.00 s, 14 MiB | reject 0.04 s, 94 MiB | reject 0.02 s, 62 MiB | reject 0.01 s, 12 MiB |
| tutorial/010_nonTypeType | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 59 MiB | reject 0.00 s, 14 MiB | reject 0.05 s, 93 MiB | reject 0.02 s, 52 MiB | reject 0.01 s, 12 MiB |
| tutorial/011_nonTypeAxiom | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 61 MiB | reject 0.00 s, 14 MiB | reject 0.06 s, 93 MiB | reject 0.02 s, 56 MiB | reject 0.01 s, 12 MiB |
| tutorial/012_nonPropThm | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 59 MiB | reject 0.00 s, 8 MiB | reject 0.06 s, 93 MiB | reject 0.02 s, 50 MiB | reject 0.01 s, 8 MiB |
| tutorial/013_thmProof | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 108 MiB | accept 0.02 s, 71 MiB | accept 0.00 s, 16 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 64 MiB | accept 0.01 s, 12 MiB |
| tutorial/014_selfProof | reject | reject | 0.00 | 0.00 | 7 MiB | reject 0.03 s, 109 MiB | reject 0.01 s, 53 MiB | reject 0.00 s, 10 MiB | reject 0.05 s, 93 MiB | reject 0.02 s, 42 MiB | reject 0.01 s, 9 MiB |
| tutorial/015_levelComp1 | accept | accept | 0.00 | 0.00 | 7 MiB | accept 0.04 s, 108 MiB | accept 0.01 s, 51 MiB | accept 0.00 s, 8 MiB | accept 0.05 s, 92 MiB | accept 0.01 s, 46 MiB | accept 0.01 s, 8 MiB |
| tutorial/016_levelComp2 | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 108 MiB | accept 0.01 s, 49 MiB | accept 0.00 s, 8 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 42 MiB | accept 0.01 s, 8 MiB |
| tutorial/017_levelComp3 | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 108 MiB | accept 0.02 s, 53 MiB | accept 0.00 s, 8 MiB | accept 0.04 s, 92 MiB | accept 0.01 s, 46 MiB | accept 0.01 s, 8 MiB |
| tutorial/018_levelParams | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.01 s, 67 MiB | accept 0.00 s, 14 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 58 MiB | accept 0.01 s, 12 MiB |
| tutorial/019_tut06_bad01 | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 109 MiB | reject 0.01 s, 51 MiB | reject 0.00 s, 7 MiB | reject 0.05 s, 93 MiB | reject 0.01 s, 44 MiB | reject 0.01 s, 8 MiB |
| tutorial/020_levelComp4 | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 108 MiB | accept 0.02 s, 55 MiB | accept 0.00 s, 8 MiB | accept 0.05 s, 92 MiB | accept 0.01 s, 38 MiB | accept 0.01 s, 8 MiB |
| tutorial/021_levelComp5 | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 108 MiB | accept 0.01 s, 57 MiB | accept 0.00 s, 8 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 40 MiB | accept 0.01 s, 8 MiB |
| tutorial/022_imax1 | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 108 MiB | accept 0.01 s, 59 MiB | accept 0.00 s, 12 MiB | accept 0.06 s, 92 MiB | accept 0.02 s, 50 MiB | accept 0.01 s, 12 MiB |
| tutorial/023_imax2 | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.02 s, 59 MiB | accept 0.00 s, 12 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 48 MiB | accept 0.01 s, 12 MiB |
| tutorial/024_levelMaxComm | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 108 MiB | accept 0.01 s, 55 MiB | accept 0.00 s, 10 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 44 MiB | accept 0.01 s, 10 MiB |
| tutorial/025_levelMaxAssoc | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 108 MiB | accept 0.02 s, 57 MiB | accept 0.00 s, 10 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 48 MiB | accept 0.01 s, 10 MiB |
| tutorial/026_levelMaxIdem | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 108 MiB | accept 0.02 s, 53 MiB | accept 0.00 s, 8 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 46 MiB | accept 0.04 s, 8 MiB |
| tutorial/027_levelMaxAbsorb | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 108 MiB | accept 0.02 s, 55 MiB | accept 0.00 s, 10 MiB | accept 0.05 s, 92 MiB | accept 0.01 s, 46 MiB | accept 0.01 s, 10 MiB |
| tutorial/028_inferVar | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 59 MiB | accept 0.00 s, 12 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 50 MiB | accept 0.01 s, 11 MiB |
| tutorial/029_defEqLambda | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 63 MiB | accept 0.00 s, 12 MiB | accept 0.06 s, 92 MiB | accept 0.02 s, 52 MiB | accept 0.01 s, 11 MiB |
| tutorial/030_peano1 | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.02 s, 87 MiB | accept 0.01 s, 22 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 70 MiB | accept 0.01 s, 17 MiB |
| tutorial/031_peano2 | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.01 s, 85 MiB | accept 0.00 s, 24 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 68 MiB | accept 0.01 s, 18 MiB |
| tutorial/032_peano3 | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 87 MiB | accept 0.00 s, 24 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 78 MiB | accept 0.01 s, 20 MiB |
| tutorial/033_letType | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.02 s, 59 MiB | accept 0.00 s, 10 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 50 MiB | accept 0.01 s, 10 MiB |
| tutorial/034_letTypeDep | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 79 MiB | accept 0.00 s, 18 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 58 MiB | accept 0.01 s, 14 MiB |
| tutorial/035_letRed | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 61 MiB | accept 0.00 s, 14 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 52 MiB | accept 0.01 s, 12 MiB |
| tutorial/036_empty | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 63 MiB | accept 0.00 s, 18 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 56 MiB | accept 0.01 s, 11 MiB |
| tutorial/037_boolType | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.01 s, 65 MiB | accept 0.00 s, 18 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 56 MiB | accept 0.01 s, 16 MiB |
| tutorial/038_twoBool | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.02 s, 73 MiB | accept 0.00 s, 26 MiB | accept 0.06 s, 92 MiB | accept 0.02 s, 66 MiB | accept 0.01 s, 16 MiB |
| tutorial/039_andType | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.01 s, 69 MiB | accept 0.00 s, 22 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 62 MiB | accept 0.01 s, 16 MiB |
| tutorial/040_prodType | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 71 MiB | accept 0.00 s, 22 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 68 MiB | accept 0.01 s, 16 MiB |
| tutorial/041_pprodType | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 75 MiB | accept 0.00 s, 22 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 50 MiB | accept 0.01 s, 16 MiB |
| tutorial/042_pUnitType | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.01 s, 69 MiB | accept 0.00 s, 18 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 60 MiB | accept 0.01 s, 14 MiB |
| tutorial/043_eqType | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 108 MiB | accept 0.02 s, 79 MiB | accept 0.00 s, 22 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 62 MiB | accept 0.01 s, 16 MiB |
| tutorial/044_natDef | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 69 MiB | accept 0.00 s, 22 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 60 MiB | accept 0.01 s, 14 MiB |
| tutorial/045_rbTreeDef | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 95 MiB | accept 0.00 s, 22 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 74 MiB | accept 0.01 s, 22 MiB |
| tutorial/046_inductBadNonSort | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 61 MiB | reject 0.00 s, 16 MiB | reject 0.04 s, 93 MiB | reject 0.02 s, 56 MiB | reject 0.01 s, 14 MiB |
| tutorial/047_inductBadNonSort2 | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 57 MiB | reject 0.00 s, 12 MiB | reject 0.05 s, 93 MiB | reject 0.02 s, 48 MiB | reject 0.01 s, 9 MiB |
| tutorial/048_inductLevelParam | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 109 MiB | reject 0.02 s, 45 MiB | reject 0.00 s, 7 MiB | reject 0.06 s, 93 MiB | reject 0.01 s, 40 MiB | reject 0.01 s, 8 MiB |
| tutorial/049_inductTooFewParams | reject | reject | 0.00 | 0.00 | 7 MiB | reject 0.04 s, 109 MiB | reject 0.02 s, 57 MiB | reject 0.00 s, 14 MiB | reject 0.04 s, 93 MiB | reject 0.02 s, 50 MiB | reject 0.01 s, 12 MiB |
| tutorial/050_inductWrongCtorParams | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 109 MiB | reject 0.01 s, 67 MiB | reject 0.00 s, 20 MiB | reject 0.04 s, 93 MiB | reject 0.02 s, 54 MiB | reject 0.01 s, 13 MiB |
| tutorial/051_inductWrongCtorResParams | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 109 MiB | reject 0.01 s, 61 MiB | reject 0.00 s, 20 MiB | reject 0.06 s, 93 MiB | reject 0.02 s, 56 MiB | reject 0.01 s, 13 MiB |
| tutorial/052_inductWrongCtorResLevel | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 109 MiB | reject 0.01 s, 59 MiB | reject 0.00 s, 20 MiB | reject 0.05 s, 93 MiB | reject 0.02 s, 52 MiB | reject 0.01 s, 13 MiB |
| tutorial/053_inductInIndex | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 109 MiB | reject 0.02 s, 61 MiB | reject 0.00 s, 20 MiB | reject 0.06 s, 93 MiB | reject 0.02 s, 52 MiB | reject 0.01 s, 14 MiB |
| tutorial/054_indNeg | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 109 MiB | reject 0.02 s, 57 MiB | reject 0.00 s, 18 MiB | reject 0.05 s, 93 MiB | reject 0.02 s, 38 MiB | reject 0.01 s, 13 MiB |
| tutorial/055_reduceCtorParam.mk | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 81 MiB | accept 0.00 s, 22 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 70 MiB | accept 0.01 s, 16 MiB |
| tutorial/056_reduceCtorType.mk | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 109 MiB | reject 0.01 s, 71 MiB | reject 0.00 s, 20 MiB | reject 0.05 s, 93 MiB | reject 0.02 s, 56 MiB | reject 0.01 s, 14 MiB |
| tutorial/057_indNegReducible | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 109 MiB | reject 0.02 s, 67 MiB | reject 0.00 s, 20 MiB | reject 0.06 s, 93 MiB | reject 0.02 s, 60 MiB | reject 0.01 s, 13 MiB |
| tutorial/058_predWithTypeField | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.02 s, 67 MiB | accept 0.01 s, 20 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 54 MiB | accept 0.01 s, 14 MiB |
| tutorial/059_typeWithTypeField | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.01 s, 65 MiB | accept 0.00 s, 20 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 64 MiB | accept 0.01 s, 14 MiB |
| tutorial/060_typeWithTypeFieldPoly | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.01 s, 65 MiB | accept 0.00 s, 20 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 60 MiB | accept 0.01 s, 14 MiB |
| tutorial/061_typeWithTooHighTypeField.mk | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 109 MiB | reject 0.02 s, 61 MiB | reject 0.00 s, 20 MiB | reject 0.06 s, 93 MiB | reject 0.02 s, 54 MiB | reject 0.01 s, 11 MiB |
| tutorial/062_emptyRec | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.02 s, 69 MiB | accept 0.00 s, 20 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 62 MiB | accept 0.01 s, 14 MiB |
| tutorial/063_boolRec | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 108 MiB | accept 0.02 s, 77 MiB | accept 0.00 s, 24 MiB | accept 0.06 s, 92 MiB | accept 0.02 s, 68 MiB | accept 0.01 s, 18 MiB |
| tutorial/064_twoBoolRec | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 87 MiB | accept 0.00 s, 20 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 76 MiB | accept 0.01 s, 18 MiB |
| tutorial/065_andRec | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.01 s, 73 MiB | accept 0.00 s, 24 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 68 MiB | accept 0.01 s, 15 MiB |
| tutorial/066_prodRec | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.01 s, 77 MiB | accept 0.01 s, 22 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 66 MiB | accept 0.01 s, 18 MiB |
| tutorial/067_pprodRec | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 75 MiB | accept 0.00 s, 24 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 66 MiB | accept 0.01 s, 16 MiB |
| tutorial/068_punitRec | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 111 MiB | accept 0.01 s, 73 MiB | accept 0.00 s, 20 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 64 MiB | accept 0.01 s, 16 MiB |
| tutorial/069_eqRec | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 75 MiB | accept 0.00 s, 22 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 68 MiB | accept 0.01 s, 18 MiB |
| tutorial/070_nRec | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 108 MiB | accept 0.01 s, 79 MiB | accept 0.00 s, 22 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 66 MiB | accept 0.01 s, 18 MiB |
| tutorial/071_rbTreeRef | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.02 s, 95 MiB | accept 0.01 s, 26 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 76 MiB | accept 0.01 s, 24 MiB |
| tutorial/072_boolPropRec | accept | accept | 0.00 | 0.00 | 7 MiB | accept 0.04 s, 109 MiB | accept 0.01 s, 73 MiB | accept 0.00 s, 22 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 68 MiB | accept 0.01 s, 15 MiB |
| tutorial/073_BogusRecursor | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 109 MiB | reject 0.02 s, 75 MiB | reject 0.00 s, 22 MiB | reject 0.05 s, 93 MiB | reject 0.04 s, 56 MiB | reject 0.01 s, 13 MiB |
| tutorial/074_existsRec | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 108 MiB | accept 0.01 s, 73 MiB | accept 0.00 s, 24 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 68 MiB | accept 0.01 s, 18 MiB |
| tutorial/075_typeSingletonRecReduction | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.02 s, 95 MiB | accept 0.00 s, 26 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 78 MiB | accept 0.01 s, 22 MiB |
| tutorial/076_sortElimPropRec | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 85 MiB | accept 0.00 s, 22 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 74 MiB | accept 0.01 s, 20 MiB |
| tutorial/077_sortElimProp2Rec | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.01 s, 91 MiB | accept 0.00 s, 22 MiB | accept 0.06 s, 92 MiB | accept 0.02 s, 80 MiB | accept 0.01 s, 20 MiB |
| tutorial/078_boolRecEqns | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 99 MiB | accept 0.01 s, 29 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 88 MiB | accept 0.01 s, 24 MiB |
| tutorial/079_prodRecEqns | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 110 MiB | accept 0.02 s, 89 MiB | accept 0.01 s, 28 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 78 MiB | accept 0.01 s, 22 MiB |
| tutorial/080_nRecReduction | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.02 s, 105 MiB | accept 0.00 s, 31 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 86 MiB | accept 0.01 s, 22 MiB |
| tutorial/081_listRecReduction | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 110 MiB | accept 0.02 s, 109 MiB | accept 0.01 s, 32 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 100 MiB | accept 0.04 s, 26 MiB |
| tutorial/082_RBTree.id_spec | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.05 s, 108 MiB | accept 0.01 s, 107 MiB | accept 0.01 s, 36 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 90 MiB | accept 0.01 s, 27 MiB |
| tutorial/083_And.right | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.02 s, 93 MiB | accept 0.01 s, 26 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 82 MiB | accept 0.01 s, 20 MiB |
| tutorial/084_Prod.snd | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.02 s, 87 MiB | accept 0.00 s, 24 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 74 MiB | accept 0.01 s, 17 MiB |
| tutorial/085_PProd.snd | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.02 s, 83 MiB | accept 0.00 s, 26 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 78 MiB | accept 0.01 s, 18 MiB |
| tutorial/086_PSigma.snd | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 87 MiB | accept 0.00 s, 26 MiB | accept 0.04 s, 92 MiB | accept 0.03 s, 74 MiB | accept 0.01 s, 18 MiB |
| tutorial/087_projOutOfRange | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.05 s, 110 MiB | reject 0.01 s, 75 MiB | reject 0.00 s, 24 MiB | reject 0.04 s, 93 MiB | reject 0.02 s, 64 MiB | reject 0.01 s, 18 MiB |
| tutorial/088_projNotStruct | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 75 MiB | reject 0.00 s, 22 MiB | reject 0.04 s, 93 MiB | reject 0.02 s, 46 MiB | reject 0.01 s, 16 MiB |
| tutorial/089_projProp1 | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 108 MiB | accept 0.02 s, 85 MiB | accept 0.00 s, 24 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 84 MiB | accept 0.01 s, 22 MiB |
| tutorial/090_projProp2 | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 110 MiB | reject 0.01 s, 95 MiB | reject 0.01 s, 26 MiB | reject 0.04 s, 94 MiB | reject 0.02 s, 64 MiB | reject 0.01 s, 22 MiB |
| tutorial/091_projProp3 | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 108 MiB | accept 0.02 s, 93 MiB | accept 0.01 s, 26 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 78 MiB | accept 0.01 s, 22 MiB |
| tutorial/092_projProp4 | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 110 MiB | reject 0.02 s, 89 MiB | reject 0.00 s, 27 MiB | reject 0.04 s, 94 MiB | reject 0.02 s, 76 MiB | reject 0.01 s, 22 MiB |
| tutorial/093_projProp5 | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 110 MiB | reject 0.02 s, 93 MiB | reject 0.01 s, 26 MiB | reject 0.04 s, 94 MiB | reject 0.02 s, 74 MiB | reject 0.01 s, 24 MiB |
| tutorial/094_projProp6 | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 112 MiB | reject 0.02 s, 93 MiB | reject 0.00 s, 24 MiB | reject 0.04 s, 93 MiB | reject 0.02 s, 84 MiB | reject 0.01 s, 20 MiB |
| tutorial/095_projDataIndexRec | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 108 MiB | accept 0.02 s, 95 MiB | accept 0.00 s, 22 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 86 MiB | accept 0.01 s, 20 MiB |
| tutorial/096_projIndexData | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 110 MiB | reject 0.02 s, 95 MiB | reject 0.00 s, 32 MiB | reject 0.05 s, 93 MiB | reject 0.02 s, 86 MiB | reject 0.01 s, 28 MiB |
| tutorial/097_projIndexData2 | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 103 MiB | reject 0.01 s, 34 MiB | reject 0.04 s, 93 MiB | reject 0.03 s, 84 MiB | reject 0.01 s, 26 MiB |
| tutorial/098_projRed | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 108 MiB | accept 0.02 s, 93 MiB | accept 0.01 s, 30 MiB | accept 0.04 s, 92 MiB | accept 0.03 s, 80 MiB | accept 0.01 s, 24 MiB |
| tutorial/099_ruleK | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 108 MiB | accept 0.02 s, 91 MiB | accept 0.00 s, 26 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 82 MiB | accept 0.01 s, 18 MiB |
| tutorial/100_ruleKbad | reject | reject | 0.00 | 0.00 | 7 MiB | reject 0.03 s, 110 MiB | reject 0.02 s, 89 MiB | reject 0.01 s, 28 MiB | reject 0.04 s, 94 MiB | reject 0.02 s, 80 MiB | reject 0.01 s, 22 MiB |
| tutorial/101_ruleKAcc | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.01 s, 99 MiB | reject 0.00 s, 29 MiB | reject 0.05 s, 94 MiB | reject 0.02 s, 72 MiB | reject 0.01 s, 22 MiB |
| tutorial/102_aNatLit | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.02 s, 67 MiB | accept 0.00 s, 20 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 62 MiB | accept 0.01 s, 15 MiB |
| tutorial/103_natLitEq | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 108 MiB | accept 0.02 s, 91 MiB | accept 0.00 s, 27 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 78 MiB | accept 0.01 s, 22 MiB |
| tutorial/104_proofIrrelevance | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 108 MiB | accept 0.01 s, 83 MiB | accept 0.00 s, 24 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 78 MiB | accept 0.01 s, 20 MiB |
| tutorial/105_proofIrrelevanceBad | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 87 MiB | reject 0.01 s, 26 MiB | reject 0.05 s, 93 MiB | reject 0.02 s, 72 MiB | reject 0.01 s, 18 MiB |
| tutorial/106_proofIrrelevanceWhnf | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 93 MiB | accept 0.00 s, 26 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 76 MiB | accept 0.01 s, 17 MiB |
| tutorial/107_proofIrrelevanceUnderBinder | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 71 MiB | accept 0.00 s, 18 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 60 MiB | accept 0.01 s, 14 MiB |
| tutorial/108_unitEta1 | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 110 MiB | accept 0.02 s, 85 MiB | accept 0.00 s, 24 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 78 MiB | accept 0.01 s, 16 MiB |
| tutorial/109_unitEta2 | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 108 MiB | accept 0.01 s, 93 MiB | accept 0.00 s, 26 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 86 MiB | accept 0.01 s, 22 MiB |
| tutorial/110_unitEta3 | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.01 s, 93 MiB | accept 0.00 s, 28 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 76 MiB | accept 0.01 s, 24 MiB |
| tutorial/111_indexedUnitEta | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.01 s, 95 MiB | reject 0.00 s, 26 MiB | reject 0.04 s, 94 MiB | reject 0.02 s, 78 MiB | reject 0.03 s, 22 MiB |
| tutorial/112_structEta | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 93 MiB | accept 0.01 s, 31 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 86 MiB | accept 0.01 s, 22 MiB |
| tutorial/113_indexedStructEta | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.02 s, 103 MiB | reject 0.01 s, 28 MiB | reject 0.04 s, 94 MiB | reject 0.02 s, 84 MiB | reject 0.01 s, 22 MiB |
| tutorial/114_funEta | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 83 MiB | accept 0.01 s, 26 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 80 MiB | accept 0.01 s, 20 MiB |
| tutorial/115_funEtaDep | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 83 MiB | accept 0.00 s, 26 MiB | accept 0.04 s, 92 MiB | accept 0.02 s, 76 MiB | accept 0.01 s, 20 MiB |
| tutorial/116_funEtaBad | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.05 s, 110 MiB | reject 0.01 s, 81 MiB | reject 0.00 s, 24 MiB | reject 0.05 s, 94 MiB | reject 0.02 s, 64 MiB | reject 0.01 s, 17 MiB |
| tutorial/117_reflOccLeft | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 109 MiB | reject 0.01 s, 71 MiB | reject 0.00 s, 28 MiB | reject 0.05 s, 93 MiB | reject 0.02 s, 58 MiB | reject 0.01 s, 18 MiB |
| tutorial/118_reflOccInIndex | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.01 s, 71 MiB | reject 0.00 s, 26 MiB | reject 0.05 s, 93 MiB | reject 0.02 s, 64 MiB | reject 0.01 s, 18 MiB |
| tutorial/119_reduceCtorParamRefl.mk | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 108 MiB | accept 0.02 s, 83 MiB | accept 0.00 s, 22 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 72 MiB | accept 0.01 s, 15 MiB |
| tutorial/120_reduceCtorParamRefl2.mk | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 81 MiB | accept 0.00 s, 22 MiB | accept 0.09 s, 92 MiB | accept 0.02 s, 72 MiB | accept 0.01 s, 16 MiB |
| tutorial/121_rTreeRec | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 85 MiB | accept 0.00 s, 26 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 76 MiB | accept 0.01 s, 20 MiB |
| tutorial/122_rtreeRecReduction | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 103 MiB | accept 0.01 s, 30 MiB | accept 0.06 s, 92 MiB | accept 0.02 s, 90 MiB | accept 0.01 s, 24 MiB |
| tutorial/123_accRecType | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 75 MiB | accept 0.00 s, 24 MiB | accept 0.06 s, 92 MiB | accept 0.03 s, 68 MiB | accept 0.01 s, 18 MiB |
| tutorial/124_accRecReduction | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 108 MiB | accept 0.02 s, 101 MiB | accept 0.00 s, 27 MiB | accept 0.06 s, 92 MiB | accept 0.02 s, 80 MiB | accept 0.01 s, 20 MiB |
| tutorial/125_accRecNoEta | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.05 s, 110 MiB | reject 0.02 s, 99 MiB | reject 0.01 s, 29 MiB | reject 0.05 s, 94 MiB | reject 0.02 s, 90 MiB | reject 0.01 s, 20 MiB |
| tutorial/126_quotMkType | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 111 MiB | accept 0.02 s, 75 MiB | accept 0.00 s, 26 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 62 MiB | accept 0.01 s, 18 MiB |
| tutorial/127_quotIndType | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.01 s, 75 MiB | accept 0.00 s, 24 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 68 MiB | accept 0.01 s, 19 MiB |
| tutorial/128_quotLiftType | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 109 MiB | accept 0.02 s, 79 MiB | accept 0.00 s, 26 MiB | accept 0.06 s, 92 MiB | accept 0.02 s, 68 MiB | accept 0.01 s, 19 MiB |
| tutorial/129_quotSoundType | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 110 MiB | accept 0.01 s, 79 MiB | accept 0.00 s, 27 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 70 MiB | accept 0.01 s, 22 MiB |
| tutorial/130_quotLiftReduction | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.04 s, 108 MiB | accept 0.02 s, 81 MiB | accept 0.00 s, 26 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 74 MiB | accept 0.01 s, 20 MiB |
| tutorial/131_quotIndReduction | accept | accept | 0.00 | 0.00 | 5 MiB | accept 0.03 s, 109 MiB | accept 0.02 s, 81 MiB | accept 0.00 s, 24 MiB | accept 0.05 s, 92 MiB | accept 0.02 s, 74 MiB | accept 0.01 s, 22 MiB |
| tutorial/132_dup_defs | reject | reject | 0.00 | 0.00 | 7 MiB | reject 0.04 s, 108 MiB | reject 0.01 s, 21 MiB | reject 0.00 s, 7 MiB | reject 0.06 s, 92 MiB | reject 0.02 s, 36 MiB | reject 0.01 s, 8 MiB |
| tutorial/133_dup_ind_def | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 108 MiB | reject 0.01 s, 18 MiB | reject 0.00 s, 9 MiB | reject 0.05 s, 92 MiB | reject 0.01 s, 4 MiB | reject 0.01 s, 10 MiB |
| tutorial/134_dup_ctor_def | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 108 MiB | reject 0.01 s, 16 MiB | reject 0.00 s, 9 MiB | reject 0.05 s, 92 MiB | reject 0.01 s, 4 MiB | reject 0.01 s, 10 MiB |
| tutorial/135_dup_rec_def | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 108 MiB | reject 0.01 s, 19 MiB | reject 0.00 s, 9 MiB | reject 0.05 s, 92 MiB | reject 0.02 s, 19 MiB | reject 0.01 s, 10 MiB |
| tutorial/136_misnamed_rec_user | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 109 MiB | reject 0.01 s, 59 MiB | reject 0.00 s, 22 MiB | reject 0.05 s, 93 MiB | reject 0.02 s, 58 MiB | reject 0.01 s, 14 MiB |
| tutorial/137_dup_rec_def2 | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 110 MiB | reject 0.01 s, 65 MiB | reject 0.00 s, 18 MiB | reject 0.05 s, 93 MiB | reject 0.02 s, 52 MiB | reject 0.01 s, 12 MiB |
| tutorial/138_dup_ctor_rec | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 108 MiB | reject 0.01 s, 21 MiB | reject 0.00 s, 9 MiB | reject 0.04 s, 92 MiB | reject 0.01 s, 4 MiB | reject 0.03 s, 10 MiB |
| tutorial/139_DupConCon | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 108 MiB | reject 0.01 s, 19 MiB | reject 0.00 s, 11 MiB | reject 0.04 s, 92 MiB | reject 0.01 s, 4 MiB | reject 0.01 s, 12 MiB |
| tutorial/140_falseFromUnsafe | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.04 s, 109 MiB | reject 0.02 s, 65 MiB | reject 0.00 s, 9 MiB | reject 0.05 s, 93 MiB | reject 0.01 s, 60 MiB | reject 0.01 s, 10 MiB |
| tutorial/141_falseFromPartial | reject | reject | 0.00 | 0.00 | 5 MiB | reject 0.03 s, 109 MiB | reject 0.02 s, 63 MiB | reject 0.00 s, 9 MiB | reject 0.05 s, 93 MiB | reject 0.02 s, 48 MiB | reject 0.01 s, 10 MiB |
