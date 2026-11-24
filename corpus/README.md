# Correctness corpus

leanqk has to give the same verdict as Lean's kernel on every test here, except
for the deliberate divergences listed in `divergences.md`.

    scripts/fetch-corpus.sh        # fetch and export the tests into corpus/exports
    cargo build --release
    scripts/run-corpus.py          # run target/release/leanqk on all of them

| file | what |
|---|---|
| `SOURCES.md` | where the tests come from, their licenses and authors |
| `exports.sha256` | SHA-256 of every export; `fetch-corpus.sh` checks them |
| `expected-lean-v4.36.0.tsv` | per test: id, source, the verdict its source declares, Lean v4.36.0's verdict, note |
| `expected-leanqk.tsv` | leanqk's intended verdict per test (generated) |
| `divergences.md` | the tests where leanqk's intended verdict differs from Lean's, and why |
| `lean/` | tests written as Lean files, exported with the Lean Kernel Arena's tutorial machinery |

`fetch-corpus.sh` needs git, curl, elan and uv (`MISE_ENV=corpus mise install`
gives uv). It takes about 3 minutes on two cores and makes the same files byte
for byte on every run. `--full` also builds the Arena's large real-world exports
(Mathlib and others), which takes hours and is not part of the checked corpus.

`scripts/lean-verdicts.sh` reruns Lean's `leanchecker --from-export` on every
export and rewrites both TSV files; run it after changing the corpus or
`divergences.md`. `scripts/selfcheck.sh` checks that the files agree with each
other and tests the runner on a fake checker.

`run-corpus.py` runs `leanqk check FILE` (exit 0 accepted, 1 rejected, malformed
input included, 2 declined) with each test's timeout and prints one row per
test with its time and peak memory, then the counts. It exits 1 on any
unexpected verdict, crash, timeout or missing export. A test leanqk declines
(exit 2, or a "not implemented" message) is pending: listed and counted, but not
a failure unless `--strict`. `--parse-only` checks instead that every export
expected to be accepted parses (`leanqk check --parse-only`). See
`run-corpus.py --help` for filtering, parallel runs and TSV output.
