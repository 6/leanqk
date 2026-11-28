# xtask

The repository's tooling, in Rust: `cargo xtask <command>` (an alias in
`.cargo/config.toml` for `cargo run --package xtask --profile xtask --quiet --`).
It is a member of the Cargo workspace but not part of the published
`nitrolean` crate. `cargo xtask --help` and `cargo xtask <command> --help`
list every option.

| command | what |
|---|---|
| `public-check [RANGE \| --tree-only]` | nothing private in the tree or in the messages of the commits in RANGE (default `origin/main..HEAD`); binary and large files must be listed in `public-check.allow` |
| `public-check-test` | `public-check` on planted violations, in a temporary repository |
| `selfcheck` | the corpus tables agree with each other and with `corpus/divergences.md`, and the corpus runner classifies results correctly (on a fake checker) |
| `fetch-corpus` | fetch the correctness corpus at pinned commits and export it into `corpus/exports` |
| `corpus` | run `target/release/nitrolean check` on every export of the corpus and compare the verdicts |
| `corpus-checksums` | print or check the SHA-256 of every export of the corpus |
| `lean-verdicts` | rerun Lean's `leanchecker` on the corpus and rewrite `corpus/expected-*.tsv` |
| `olean-equivalence MODULE` | the `.olean` reader gives the same environment as Lean's export |
| `install-elan` | install elan from its pinned release archive (CI) |
| `kernel-cases` | generate the kernel test cases of `tests/kernel` |
| `kc ...` | the kernel-computation benchmarks (`bench/kernel-compute`): `fetch-zenodo`, `fetch-lrat`, `fetch-mathlib-decide`, `build-checkers`, `measure`, `summarize`, `run-limited`, `lrat-trim`, `select-decide` |
| `matcert ...` | the matrix certificates (`bench/certificates`): `gen`, `exports`, `measure`, `table` |
| `mathlib ...` | the benchmark on all of Mathlib: `fetch` (its v4.36.0 export, checked by SHA-256), `run` (a checker's wall time, CPU time and peak memory at several thread counts) |
| `famous-sat ...` | cubes of famous cube-and-conquer SAT proofs (`bench/famous-sat`): `fetch`, `parallel`, `coverage`, `scaling`, `survey`, `cube-cnf`, `lrat-core`, `renumber` |
| `arena ...` | the Lean Kernel Arena benchmark (`bench/arena`): `fetch`, `run`, `report`, `pin`, `collect`, `verify` |
| `oracle ...` | the per-declaration oracle against Lean's checker (`bench/oracle`): `build`, `run`, `reduce`, `all` |
| `pgo EXPORT... [--repo] [--rustflags FLAGS] [--bolt]`, `pgo --use PROFDATA` | a profile-guided `target/release/nitrolean`: an instrumented build checks each export on one thread, `llvm-profdata` (`rustup component add llvm-tools`) merges the profiles into `target/pgo/nitrolean.profdata`, and the release build uses it; `--repo` trains on the exports in the repository (`tests/kernel` and the `Init` prefix in `bench/arena/pgo`); `--use` builds with a profile made before; `--bolt` then lays out the binary's code with LLVM's BOLT on a profile of the same exports (`--bolt-profile perf|instrument`, `--bolt-dir DIR` for `llvm-bolt` and `merge-fdata`), and fails unless the result's output matches the binary before BOLT on every training export at `-j 1` and `-j 4` |
| `perf-lines --raw DIR --name NAME [--bin BIN] [--period N] [--dir DIR] -- CMD...` | the Mathlib benchmark's profile by source line (`bench/mathlib-ci/profile.sh`): tries `mem_load_retired.l2_miss` and `br_misp_retired.all_branches` alone at `:upp`, `:up`, then `:u` (marked approximate), records CMD with those perf takes (each alone if not together), and writes the reports, the binary, perf's errors (`record-notes.txt`) and a Markdown table (`lines-NAME.md`) into DIR |
| `perf-lines-test` | `perf-lines` on a fake `perf`: precise, fallback to `:u`, one event refused, events refused together |

The commands drive git, curl, elan, lake and the checkers directly. Lean
sources stay Lean; the upstream tools some benchmarks use (the Arena's
`lka.py`, LRAT-Catcher's `gen_php.py`) are run as they are.
