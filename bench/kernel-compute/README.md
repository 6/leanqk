# Kernel computation benchmarks

Exports of Lean developments whose proofs are checked by *computation* in the kernel
(`decide`, proof by reflection, a verified certificate checker run by the kernel), to time
kernel evaluation in `nitrolean` and in other checkers. Everything is fetched at a pinned commit
or version and checked against a pinned SHA-256, and the toolchains are pinned with elan, in the
way `scripts/fetch-corpus.sh` does it. The exports are not committed: the scripts make them
under `out/`, the sources and build trees live under `cache/` (both git-ignored; override with
`KC_OUT` / `KC_CACHE` or `--out` / `--cache`).

| Script | What it does |
| --- | --- |
| `fetch-zenodo.sh` | benchmark **a**: builds the published planar-graph result and exports it |
| `fetch-lrat.sh` | benchmark **b**: kernel-only LRAT proofs of growing size, as exports |
| `fetch-mathlib-decide.sh` | benchmark **c**: 150 Mathlib declarations proved by kernel `decide` |
| `build-checkers.sh` | builds the four checkers at pinned commits |
| `measure.sh` | runs the checkers on exports under a time and memory limit, writes a TSV |
| `tools/` | helpers run with `python3 -I`: `run_limited.py`, `lrat_trim.py`, `select_decide.py`, `summarize.py` |
| `lean/` | Lean helpers: own-declaration listing, the `kernel_lrat` command (`lrat-kernel/`), kernel timing |
| `data/` | pinned inputs: `lrat-instances.tsv`, `php-instances.tsv`, `mathlib-decide-names.txt` |

Needs `git curl unzip xz sha256sum make c++ python3`, `elan` and `rustup` (cargo). Typical run:

```sh
bench/kernel-compute/build-checkers.sh
bench/kernel-compute/fetch-zenodo.sh          # builds Mathlib from its cache: ~10 GB of disk
bench/kernel-compute/fetch-lrat.sh
bench/kernel-compute/fetch-mathlib-decide.sh  # needs fetch-zenodo.sh first
bench/kernel-compute/measure.sh --timeout 60 --out out/measurements.tsv out/lrat/*.ndjson out/zenodo/*.ndjson out/mathlib/*.ndjson
python3 -I bench/kernel-compute/tools/summarize.py out/measurements.tsv out/lrat/manifest.tsv
```

Every script has `--help`. `--update-pins` (or `KC_UPDATE_PINS=1`) reports a content hash that
differs from the pinned one instead of stopping, to update a pin on purpose.

## a. The published planar-graph result (`fetch-zenodo.sh`)

The Lean proof released as doi:10.5281/zenodo.24467489: a Lean v4.34.0 + Mathlib project
(Mathlib revision in its `lake-manifest.json`) and its `lean/catcher` subproject on Lean v4.30.0,
which imports a SAT certificate with the LRAT-Catcher library. Only the released file is used;
it is built unchanged (`lake exe cache get` for the Mathlib `.olean` files, then `lake build`).
Its kernel work is large finite checks by `decide +kernel` and a certificate checker run by
reflection. The exports are made with the `lean4export` commit that matches each toolchain
(the one that bumps to that Lean version).

Outputs in `out/zenodo/`:

* `steinberg-main.ndjson`: the closure of the project's own declarations (2739 non-internal
  names in the modules `LocalRup`, `Steinberg`, `Check`, `PublishedInput`, `Challenge`; the
  closure has about 7800 theorems and the definitions they use, from Mathlib and the core
  library).
* `steinberg-main.own-names.txt`: those names.
* `steinberg-main-deps.ndjson`: the closure of the constants the own declarations use directly,
  without them. The checking time of the full export minus that of this one is the cost of
  the own declarations.
* `steinberg-catcher.ndjson`, `.own-names.txt`, `-deps.ndjson`: the same for `lean/catcher`
  (113 own names). Almost all of its kernel work is in the library, not in its own declarations.

## b. Kernel-only LRAT proofs (`fetch-lrat.sh`)

Each export contains one theorem `bench_lratNN : (CNF literal).Unsat`, a refutation of a public
SAT Competition instance (fetched by hash from the Global Benchmark Database; the table is
`data/lrat-instances.tsv`), stated with the kernel mode of LRAT-Catcher:
`LRATCatcher.checkKernel_sound cnf actions (of_decide_eq_true (Eq.refl true))`, so the checker
has to evaluate `LRATCatcher.checkKernel cnf actions` (the verified LRAT checker of the standard
library, rewritten to be kernel friendly) on the whole certificate. The certificate is made by
CaDiCaL 2.2.1 (`--lrat --no-binary`), trimmed to the lemmas the empty clause depends on and
renumbered (`tools/lrat_trim.py`).

Lean's own kernel would need far longer than is practical for the larger ones, so the theorem is
added with `set_option debug.skipKernelTC true`; the term is built by `kernel_lrat`
(`lean/lrat-kernel/BenchLrat/Cmd.lean`), which states the theorem and its proof as
`lrat_reflect +kernel` does, directly as an `Expr`, without the elaborator (which writes small
array literals with helpers such as `mkArray4`, so the terms differ in such details). The
smallest one (lrat01) was also added with the check on, to confirm that Lean's kernel accepts
what the exports contain. `out/lrat/manifest.tsv` records per proof the CNF bytes, LRAT bytes,
export bytes and the LRAT SHA-256. Every export contains the library's closure (about 40 MB);
`base.ndjson` is the same theorem for a 4-clause formula (LRAT-Catcher's own example), so
(export bytes - base) is the size of the proof term.

A second series, `phpN`, refutes the pigeonhole formulas PHP(N+1, N) (`data/php-instances.tsv`,
N = 4 to 8, 1.7 KB to 4.5 MB of LRAT): the CNF is made by LRAT-Catcher's `examples/gen_php.py`
and the proof by the CaDiCaL of the v4.30.0 toolchain (2.1.2), untrimmed; both are checked
against pinned SHA-256s. It is one proof family, growing about 9 times a step.

## c. Mathlib declarations proved by `decide` (`fetch-mathlib-decide.sh`)

150 theorems of the Mathlib revision the published result pins, listed in
`data/mathlib-decide-names.txt`. They were chosen by looking at proof terms, not at the source:
among the ~780 Mathlib theorems whose proof term uses `of_decide_eq_true` (from `by decide`,
`decide +kernel`, `simp` closing goals by `decide`; `lean/RankDecide.lean` times the kernel on
each), the ones that take at least 1 ms to check and are slowest per object of the proof term, i.e.
the proof terms that are small and spend their time computing (`tools/select_decide.py`). They
are mostly determinants and equalities of explicit Cartan matrices, `ZMod` unit and character
computations, `Fin`/`Finset` enumerations. None uses `native_decide` or another axiom than
`propext`, `Classical.choice` and `Quot.sound` (the script checks this). The grep-level picture
of the source of that revision: about 410 `by decide`, 8 `decide +kernel`, 6 `native_decide`.
`out/mathlib/mathlib-decide.ndjson` is the closure (about 800 MB, 15 million lines);
`mathlib-decide-deps.ndjson` is the same without the 150 declarations themselves. Kernel times of
these declarations are milliseconds each: most of the export is the Mathlib definitions the
statements need, and checking is dominated by that, not by the `decide` terms.

## Checkers and measurement

`build-checkers.sh` builds, at pinned commits: `nitrolean` (this checkout), `gruszka`
(github.com/jasisz/gruszka; reads the binary form made by `susz pack`, which is not timed),
`nano-lean` (github.com/sdiehl/nano-lean, `nl-fast`), and takes `leanchecker` from the Lean
v4.36.0 toolchain (`leanchecker --from-export`). `measure.sh` runs them on each export with a
wall-clock limit and a resident-memory limit (default 60 s and 4 GiB; `tools/run_limited.py` samples
the resident set of the process group every 50 ms and kills it above the limit; `ulimit -v` is not
used because gruszka reserves address space up front and cannot start under it). The TSV has the
columns `export export_bytes checker limit_s verdict exit wall_s peak_rss_mib`; the verdict is
`accepted`, `rejected`, `timeout`, `oom`, `error` or `unavailable`. Wall time and peak memory come
from `/usr/bin/time -v`. Measure on an otherwise idle machine, one run at a time; the
numbers are from a single run each.

## Results (one machine, one run each)

12-core aarch64 Linux, limits 60 s and 4 GiB resident (`measure.sh` defaults), plus 600 s runs
for the largest sizes. `leanchecker` is Lean v4.36.0's; gruszka and nano-lean are at the commits
in `build-checkers.sh`. The gruszka and nano-lean columns for the GBD series, the published result and
Mathlib are from an earlier run on the same exports and checker builds. Wall time in seconds and
peak resident memory in MiB; `oom` is over 4 GiB, `timeout` over 60 s.

LRAT series (GBD instances, then pigeonhole), by LRAT size:

| export | LRAT bytes | nitrolean | leanchecker | gruszka | nano-lean |
| --- | ---: | --- | --- | --- | --- |
| lrat01 | 1 248 | 0.96 s, 109 | 4.7 s, 872 | rejected | 0.40 s, 266 |
| lrat02 | 1 916 | 0.90 s, 110 | 5.0 s, 1 010 | 0.27 s, 301 | 0.42 s, 275 |
| lrat11 | 6 155 | 1.9 s, 161 | oom | oom | oom |
| lrat03 | 7 687 | 1.3 s, 110 | oom | 1.7 s, 845 | 0.90 s, 738 |
| lrat12 | 11 554 | 1.3 s, 125 | oom | oom | oom |
| lrat13 | 19 770 | 1.8 s, 134 | oom | oom | oom |
| lrat04 | 22 115 | 1.6 s, 93 | oom | 15.6 s, 1 926 | 3.8 s, 2 870 |
| lrat14 | 31 206 | 2.0 s, 111 | oom | 25.3 s, 2 262 | 5.8 s, 3 969 |
| lrat05 | 66 929 | 3.8 s, 142 | oom | oom | oom |
| lrat06 | 277 861 | 15.8 s, 458 | oom | oom | oom |
| lrat07 | 695 602 | 45.2 s, 1 531 | oom | oom | oom |
| lrat08 | 1 846 216 | timeout; oom after 135 s | oom | oom | oom |
| lrat09 | 4 525 550 | timeout; oom after 263 s | oom | oom | oom |
| lrat10 | 9 634 427 | timeout; oom after 210 s | oom | oom | oom |
| php4 | 1 748 | 0.80 s, 111 | 5.6 s, 1 141 | 0.44 s, 293 | 0.46 s, 347 |
| php5 | 9 615 | 0.99 s, 109 | oom | 4.5 s, 1 195 | 1.5 s, 1 205 |
| php6 | 91 338 | 3.8 s, 161 | oom | oom | oom |
| php7 | 795 584 | 46.9 s, 1 495 | oom | oom | oom |
| php8 | 4 471 135 | timeout; oom after 325 s | oom | oom | oom |

The largest proof checked within 60 s and 4 GiB:

| series | nitrolean | leanchecker | gruszka | nano-lean |
| --- | ---: | ---: | ---: | ---: |
| GBD series | 695 602 B (lrat07) | 1 916 B (lrat02) | 31 206 B (lrat14) | 31 206 B (lrat14) |
| pigeonhole series | 795 584 B (php7) | 1 748 B (php4) | 9 615 B (php5) | 9 615 B (php5) |

gruszka rejects `lrat01` (application type mismatch), which the other three accept.

The published result and Mathlib:

| export | nitrolean | leanchecker | gruszka | nano-lean |
| --- | --- | --- | --- | --- |
| steinberg-main | 26.6 s, 248 | oom (524 s, 7 723 with no memory limit) | oom | 26.9 s, 1 904 |
| steinberg-catcher | 4.7 s, 495 | 10.1 s, 206 | 0.65 s, 519 | 1.6 s, 803 |
| mathlib-decide | 41.9 s, 740 | timeout (115 s, 1 367 at 600 s) | 0.69 s, 612 | 7.5 s, 773 |

Without its own declarations (`-deps`), `steinberg-main` takes every checker 3 s or less, so
the time is in the result's own computations. For `mathlib-decide` it is the other way round:
the export without the 150 declarations takes the same time, so the time goes into the Mathlib
definitions their statements need, not into the `decide` terms.
