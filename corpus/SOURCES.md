# Sources of the test corpus

`cargo xtask fetch-corpus` fetches each source below at the commit given here,
checks the SHA-256 of the files it uses, and exports the tests with the
`leanexport` of Lean v4.36.0 (`leanprover/lean4:v4.36.0`, commit
611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9). The exports are not in git; their
SHA-256s are in `exports.sha256`. Each section names the source as it appears in
the second column of `expected-lean-v4.36.0.tsv`.

The tests belong to their authors, under the licenses below; this repository
only records their ids, their expected verdicts and the commands that build
them. Thanks to everyone who wrote them.

## Lean Kernel Arena (`arena`)

- https://github.com/leanprover/lean-kernel-arena, commit
  8a7d0dceea76dfe6fd7bd7f3a6ea216f6347c6aa
- License: Apache-2.0
- Used: `tests/` (bugs, corner cases, perf and other tests, `Init.Prelude`)
  and `tutorial/` (the tutorial tests), built with the Arena's own
  `lka.py build-test --skip-ci`. With `--full`, also the real-world exports it
  marks `skip-on-ci` (Init, Std, Mathlib, cslib, Cedar, and others), which are not
  in the checksummed corpus.
- Each test declares its expected outcome (`accept`, `reject` or `either`);
  that is the `expected` column.
- Authors of the tests and of the tutorial: Joachim Breitner, who started the
  Arena and wrote most of them, and Szymon Teżewski, Robert J. Simmons, Jeremy
  Chen, Julian Berman, phiferd, Tristan Stérin, Sebastian Graf, Reuben Bowlby,
  Markus Himmel, Mario Carneiro, Giorgio Dell'Immagine, Eric Anderson and Aron
  Adler. The test descriptions credit the people who found the bugs they
  reproduce.

## Lean's leanchecker tests (`leanchecker`)

- https://github.com/leanprover/lean4, tag v4.36.0 (commit
  611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9), `tests/pkg/leanchecker`
- License: Apache-2.0
- Used: the test modules that have an `.export` file, built with `lake build`
  and exported with `leanexport MODULE -- DECLS` as the package's `run_test.sh`
  does. The expected verdict is the one in its `.export.out.expected`.
- Authors: the Lean developers (leanchecker grew out of lean4checker by Kim
  Morrison); the test package's history credits Sebastian Ullrich, Garmelon,
  Joachim Breitner, Thomas Zhu, Marc Huisinga and Henrik Böving.

## nanoda_lib's test exports (`nanoda`)

- https://github.com/ammkrn/nanoda_lib, commit
  0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929
- License: Apache-2.0
- Used: `test_resources/Empty/export` (an export with no declarations; accepted)
  and `test_resources/ProjFromProp/export` (a projection out of a proof, which
  nanoda's test expects to be rejected), as they are.
- Author: Chris Bailey (ammkrn).

## lean4lean's regression tests (`lean4lean`)

- https://github.com/digama0/lean4lean, commit
  23fd0341e823a332ce5df21a1897c8afcbf34471, `Lean4Lean/Tests/KernelHardening.lean`
- License: Apache-2.0
- lean4lean's tests build kernel declarations in Lean and pass them to its own
  `addDecl`, so there are no export files to fetch. `corpus/lean/Lean4LeanTests.lean`
  copies those declarations and exports each one as a test case with the Arena's
  tutorial machinery; its header lists the cases that cannot be exported. The
  expected verdict is lean4lean's.
- Authors: Mario Carneiro and the lean4lean contributors (the tests' history
  credits Mario Carneiro, Kim Morrison, Joachim Breitner and Muneeb Sheikh).

## Historical Lean kernel bugs (`historical`)

- `corpus/lean/HistoricalBugs.lean`, in this repository (Apache-2.0), exported
  with the Arena's tutorial machinery.
- Reproducers of soundness bugs of Lean 4's kernel that the Arena does not
  already cover: leanprover/lean4#1781, #2125, #1433, #8060, #12746 and #13602,
  #16279, #15908 and #16730. Each test's description names the issue, the
  people who reported and fixed it, and the release that has the fix. The
  reproducers follow the issues and the tests of the pull requests that fixed
  them.
