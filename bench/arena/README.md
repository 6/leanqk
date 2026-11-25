# Lean Kernel Arena benchmark

This directory reproduces the test set of the
[Lean Kernel Arena](https://arena.lean-lang.org)
([source](https://github.com/leanprover/lean-kernel-arena)) at the arena's
pinned versions and runs nitrolean on it the way the arena calls a checker,
so that speed and memory are measured on well-known proofs of many kinds, not
only on our own corpus (`corpus/`).

    cargo xtask arena fetch            # build the 261 small exports (~3 min, ~300 MB)
    cargo xtask arena fetch --large    # the 9 large ones (hours, ~40 GB of disk)
    cargo build --release
    cargo xtask arena run              # nitrolean on every export built
    cargo xtask arena run --competitors --checker nitrolean   # and the others installed
    cargo xtask arena report bench/arena/results/results.tsv  # Markdown table

The commands are in `xtask/src/arena.rs`; `cargo xtask arena help` lists
them and their options.

Everything below was read from the arena at commit
[`8a7d0dceea76dfe6fd7bd7f3a6ea216f6347c6aa`](https://github.com/leanprover/lean-kernel-arena/tree/8a7d0dceea76dfe6fd7bd7f3a6ea216f6347c6aa)
(2026-11-24), the commit the live site showed at the time: its
[`results.json`](https://arena.lean-lang.org/results.json) of
2026-11-24 19:59 UTC was built from it (SHA-256
`31805254a67a9bbc0b3cb07d1a804d4f6beb7eaba31ae5ce45b043aecbc062e3`; the file
on the site changes with every build, so this copy is not fetched again).
No round had been closed at that time, so no archived round could be
pinned instead.

`cargo xtask arena fetch` fetches the arena at the pinned commit and builds
the exports with its own `lka.py build-test`; `arena pin RESULTS_JSON` writes
`tests.tsv` and `published.tsv` from a `results.json`; `arena collect` and
`arena verify` collect and verify exports; `arena run` and `arena report` are
the runner and its report.

| file | what |
|---|---|
| `tests.tsv` | the 270 tests: group, expected outcome, timeout, flags, Lean version, export format, lines, bytes and the SHA-256 of the export the arena checked |
| `published.tsv` | the arena's own results for Lean's checker, gruszka and nano-lean on its runner (verdict, wall and CPU time, peak RSS, instructions in billions) |
| `results.md`, `run-2026-11-25.tsv` | our last run: per test, nitrolean against the expected verdict and the others, and its raw rows |

## What the arena runs

### Test inputs

The 130 files `tests/**/*.yaml` at the pinned commit define 129 tests, and
the tutorial definition expands into 141 generated ones, for 270 in all. Each test has
an expected outcome: `accept`, `reject`, or `either` (corner cases where the
correct verdict is debatable; both verdicts count as fine).

| group | accept | reject | either | what |
|---|---|---|---|---|
| real-world | 9 | | | libraries and projects (table below) |
| `perf/` | 37 | 8 | | small inputs that expose algorithmic performance problems |
| `bugs/` | 2 | 32 | | soundness bugs or crashes actually found in some checker, the official one included |
| `corner-cases/` | 1 | | 30 | gaps between algorithmic and declarative conversion |
| `other/` | 5 | 5 | | synthetic tests of one check |
| `tutorial/` | 94 | 47 | | one small test per feature of the type theory, from `tutorial/Tutorial.lean` |

The adversarial cases are the `reject` tests of `bugs/`, `perf/`, `other/`
and `tutorial/` (92 in all): hand-made exports, or Lean files that build bad
declarations with the arena's tutorial machinery (`tutorial/Tutorial/Meta.lean`).

The real-world tests (`skip-on-ci: true` in the arena, except
`init-prelude`; they are built only for the published site):

| test | source | pinned at | exported | Lean | export | lines | timeout |
|---|---|---|---|---|---|---|---|
| `init-prelude` | Lean core | Lean v4.36.0 | module `Init.Prelude` | 4.36.0 | 3.8 MB | 65 k | 40 s |
| `init` | Lean core | Lean v4.36.0 | module `Init` | 4.36.0 | 348 MB | 6.5 M | 370 s |
| `std` | Lean core | Lean v4.36.0 | module `Std` | 4.36.0 | 584 MB | 10.6 M | 600 s |
| `mathlib` | [mathlib4](https://github.com/leanprover-community/mathlib4) | tag `v4.36.0`, `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` | module `Mathlib` | 4.36.0 | 6.3 GB | 112 M | 4120 s |
| `cslib` | [cslib](https://github.com/leanprover/cslib) | `main`, `e60b7760d6300ca790bc6a9adf6ded47f5773953` | module `Cslib` | 4.36.0 | 2.5 GB | 44 M | 1600 s |
| `navier-stokes-euler` | NavierStokesAndEuler ([its arena test](https://github.com/leanprover/lean-kernel-arena/blob/8a7d0dceea76dfe6fd7bd7f3a6ea216f6347c6aa/tests/navier-stokes-euler.yaml) gives the repository) | `main`, `f9e8bc5b38b6e212696e8a30e3e91517af887bbd` | 4 main theorems and their dependencies | 4.34.0-rc2 | 1.6 GB | 28.6 M | 1840 s |
| `cedar` | [cedar-spec](https://github.com/cedar-policy/cedar-spec) | `main`, `326d93c24490c90607a3e257318e9c6a049c8116` | module `Cedar` | 4.36.0 | 905 MB | 15.9 M | 640 s |
| `con-leche` | [con-leche](https://github.com/leanprover/con-leche) | `master`, `cd2eceab2e9b10404c663b468639c8aa99d0d1f2` | 3 theorems and their dependencies | 4.36.0 | 702 MB | 12.7 M | 920 s |
| `reachability` | [reachability](https://github.com/Arrow7000/reachability) | tag `v0.1.2`, `d822b1c70b4a6ec858b54ee51f12b0cb30628982` | 6 `decide +kernel` proofs and their dependencies | 4.34.1 | 19 MB | 362 k | 220 s |

`perf/gf3-matrix-product` is also marked `skip-on-ci` (it is small, 0.8 MB,
but slow to elaborate); `arena fetch --large` builds it with the others.
The "Lean" column is the Lean version in the export's header, i.e. the
toolchain of the project that was exported. Sizes, line counts and SHA-256s
of all 270 exports are in `tests.tsv`.

### How the exports are made

`lka.py build-test` (at the pinned commit) makes every export; there are
four kinds of test definition:

- **`leanfile`** (96 tests: `init`, `std`, `init-prelude`, most of `bugs/`,
  `perf/`, `other/` and `corner-cases/`): the file is copied to `Test.lean`
  in a fresh project with a trivial `lakefile.toml` and the arena's
  `tests/lean-toolchain` (`leanprover/lean4:v4.36.0`), built with
  `lake build Test` and exported with `lake env leanexport Test [-- DECLS]`.
- **`module`** (9 tests): three export a module of the arena's own
  `tutorial/` project (`dir: tutorial`) that builds bad declarations
  bypassing the kernel; for the six projects above (`url`/`rev`) the repository is
  fetched at `rev`, the test's `pre-build` runs (`lake exe cache get` for the
  Mathlib-based ones, or writing a small module that imports what is
  exported), then `lake build MODULE` and `lake env leanexport MODULE [-- DECLS]`.
  Each project uses its own `lean-toolchain`.
- **`file`** (24 tests): a hand-written `.ndjson` export in the arena's
  repository, used as it is. Their headers carry the Lean version they were
  made with (4.29.1 for 16 of them).
- **`run` with `multiple: true`** (the tutorial): `lake env lean
  Tutorial.lean` in `tutorial/` writes one export per test case into `good/`
  or `bad/`.

The exporter is the `leanexport` bundled with the project's toolchain (Lean
v4.35.0 and later ship it), writing lean4export's NDJSON format 3.1.0. For an
older toolchain `lka.py` clones
[lean4export](https://github.com/leanprover/lean4export) at its `master`
branch and builds it with that toolchain: this happens for
`navier-stokes-euler` (4.34.0-rc2) and `reachability` (4.34.1), and is the
one input the arena does not pin by commit. `arena fetch` catches any drift:
it compares every export with the SHA-256 the arena published.

### The checker interface

A checker is a YAML file in `checkers/` (schema `schemas/checker.json`):
`build` (a shell command run once in its checkout of `url` at `rev`), `run`
(a shell command run in that checkout with the export's path in `$IN`), and
optionally `declines` (tests it is not run on), `timeout` and `threads`. The
verdict is the exit code alone: **0** accepted, **1** rejected, **2**
declined (the checker cannot handle this input: e.g. it does not support an
axiom; not counted either way), anything else an error. Past the test's
`timeout` the process group is killed and the run counts as a timeout. The
tests and the checker share nothing else: no flags, no stdin, and output is
only kept for display.

The checkers compared here run as (from their YAML at the pinned commit):

| checker | version | `run` |
|---|---|---|
| `official` (Lean's kernel) | Lean v4.35.0 | `leanchecker --from-export "$IN"` |
| `gruszka` | 0.2.0, `39d03331823f084a39323998fb1ee73de374182e` | `scripts/arena-run "$IN" 4` (built with PGO; 4 threads) |
| `nano-lean` | v0.4.2, `5cd4a25de7cdd8a5fadde3fec53e41a6a8693138` | `target/release/nl-fast -q -j 4 "$IN"` (built with PGO; 4 threads) |

nitrolean is not an arena checker; called as one, it is
`nitrolean check "$IN"`, which already uses the same exit codes.

### Measurement and scoring

Each run is wrapped as `perf stat -e duration_time,task-clock,instructions --
time -f ... -- sh -c "$RUN"`: wall time (`duration_time`), CPU time
(`task-clock`, all threads), instructions, and peak RSS from GNU time
(`%M`). Without `perf`, only wall time is recorded.

A result is *correct* if an `accept` test was accepted or a `reject` test
rejected, *incorrect* otherwise; `either` tests are shown but excluded from
the scores; declines, errors and timeouts make no claim and count as
declined. Checkers are ranked by, in order: `reject` tests not rejected
(soundness), `accept` tests not accepted (completeness), the instruction
count on `mathlib` (only if it was accepted; checkers without one rank
below), and the number of declines. For the `compare-perf` tests (54: the
real-world ones and `perf/`), the site marks the fastest checker by
"virtual time" (instructions at 6 G/s) and those at least 10% faster than
the official one.

The per-test timeouts derive from the official checker's wall times
(`set-timeouts.py`: a total budget of three times its total wall time,
roughly 2x for `mathlib` and 10x or more for small tests); only 56 tests
have one.

### The machine

The checkers run on GitHub Actions jobs on Namespace runners labelled
`nscloud-ubuntu-22.04-amd64-8x16-with-cache`
([workflow](https://github.com/leanprover/lean-kernel-arena/blob/8a7d0dceea76dfe6fd7bd7f3a6ea216f6347c6aa/.github/workflows/build-and-deploy.yml)):
Ubuntu 22.04, amd64, 8 vCPUs and 16 GB of RAM, one job per checker, the
tests one after another, inside `nix develop` with the arena's
`flake.nix`. The timeouts are set for this machine.

## Reproducing the test set

`arena fetch` pins the arena commit and the SHA-256 of the files it uses
(`lka.py`, `schemas/`, `tests/`, `tutorial/`), installs
`leanprover/lean4:v4.36.0` (checking its commit,
`611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`), and runs the arena's own
`lka.py build-test` through `uv` with its Python dependencies resolved as of
2026-11-24. The projects are fetched by `lka.py` at the commits in their
test YAML, Mathlib's build cache by `lake exe cache get` (which checks its
own hashes). Every export built is compared with the SHA-256 the arena
published for it (`tests.tsv`); `arena fetch` fails on any difference, and
writes the SHA-256s of all exports to `OUT/SHA256SUMS`.

Nothing from the arena is copied into this repository. All test sources
are fetched at the pinned commit instead, since the generated exports are
only reproducible together with the arena's build tool, and fetching keeps
their attribution and licence with them. `tests.tsv` and `published.tsv`
are metadata and measurements taken from the arena's `results.json`.

Sources and licences (all fetched, none copied):

| source | licence |
|---|---|
| [lean-kernel-arena](https://github.com/leanprover/lean-kernel-arena) (tests, tutorial, `lka.py`) | Apache-2.0 |
| [Lean 4](https://github.com/leanprover/lean4) (`Init`, `Std`, `leanexport`, `leanchecker`) | Apache-2.0 |
| [mathlib4](https://github.com/leanprover-community/mathlib4) | Apache-2.0 |
| [cslib](https://github.com/leanprover/cslib) | Apache-2.0 |
| NavierStokesAndEuler ([its arena test](https://github.com/leanprover/lean-kernel-arena/blob/8a7d0dceea76dfe6fd7bd7f3a6ea216f6347c6aa/tests/navier-stokes-euler.yaml) gives the repository) | Apache-2.0 |
| [cedar-spec](https://github.com/cedar-policy/cedar-spec) | Apache-2.0 |
| [con-leche](https://github.com/leanprover/con-leche) | Apache-2.0 |
| [reachability](https://github.com/Arrow7000/reachability) | Apache-2.0 |
| [gruszka](https://github.com/jasisz/gruszka) (comparison only) | Apache-2.0 |
| [nano-lean](https://github.com/sdiehl/nano-lean) (comparison only) | MIT |

The arena's tests were written by Joachim Breitner, who started the arena,
and many contributors; the test descriptions credit the people who found
the bugs they reproduce.

The small exports are byte-identical to the arena's when built on aarch64
Linux (261 of 261). `arena fetch --large` needs about 16 GB of RAM to export
Mathlib and some 40 GB of disk; put `--out` and `--cache` on a large disk.
`lka.py` runs each test's `pre-build` with `/bin/sh`, which is bash in the
arena's nix shell; cedar's uses `shopt`, so where `/bin/sh` is dash (Debian,
Ubuntu) that test needs a bash `/bin/sh` (`arena fetch` warns).
`reachability` depends on Mathlib but its pre-build runs no
`lake exe cache get`, so Lake builds what it needs of Mathlib from source.

## Running

`cargo xtask arena run` runs each checker on each export present, one at a
time, as `sh -c CMD` with `$IN` set, in the checker's directory, and
derives verdict and correctness from the exit code exactly as the arena
does. Per run it records wall time, CPU time (user + system of the command
and the children it waited for), peak RSS (GNU time's `%M`, as the arena),
the instruction count (in billions) when `perf stat` works, and the first line of
standard error. Rows are appended to `results/results.tsv`; pairs already
there are skipped, so an interrupted run resumes.

The arena's timeouts are applied, multiplied by `--timeout-scale` (on a
slower machine than the arena's, use 2 or more; `--no-timeout` drops them).
Run it on an otherwise idle machine; `taskset -c 0-7` gives the arena's
8 cores on a larger one.

Comparison checkers (`--competitors`, or `--checker NAME`) are run if found:
`official` from `$LEANCHECKER` or elan's `leanprover/lean4:v4.35.0`,
`gruszka` from a built checkout in `$GRUSZKA_DIR`, `nano-lean` from a built
checkout in `$NANO_LEAN_DIR` (or `nl-fast` on `PATH`). `--checker NAME=CMD`
adds any other command. `cargo xtask arena report` prints a Markdown table of a run
with the arena's published numbers next to it, and marks every verdict
that differs from the expected one (`MISMATCH`) and every error or timeout.

## Results

See `results.md`. On 2026-11-25 (nitrolean 0.1.0-alpha.1), every export
matched the arena's SHA-256. nitrolean was correct on 239 tests and failed
one, `reachability` (timeout; over 32 GB of memory). It gave no verdict
opposite to the expected one. It accepted Mathlib in 613 s with a peak of
4.6 GiB, against 1578 s and 9.9 GiB for Lean's checker and 19 s and 29 s
for gruszka and nano-lean (4 threads each), all on the same machine.
