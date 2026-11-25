# Kernel test cases

Each case is one export in the lean4export format (3.1), built to test one kernel rule.
A case is either something a correct kernel must reject, or a tricky
export it must accept. `cases.tsv` lists them:

| column     | meaning |
|------------|---------|
| `id`       | file name: `exports/<id>.ndjson` or `out/cases/<id>.ndjson` |
| `rule`     | the kernel rule under test |
| `expected` | `accept`, `reject`, or `either` (true claims that need more than Lean's Nat size limit; accepting and rejecting cleanly are both fine, crashing or hanging is not) |
| `lean`     | what `leanchecker --from-export` from Lean v4.36.0 says |
| `why`      | what the case does |

## Generating

Lean is pinned in `lean-toolchain` (elan).

    cargo xtask kernel-cases            # all cases into out/cases/ (about 23 MB, not committed)
    cargo xtask kernel-cases --lean     # also run leanchecker on each case
    cargo xtask kernel-cases --update   # rewrite cases.tsv and exports/
    cargo xtask kernel-cases --check    # fail if cases.tsv or exports/ are stale
    cargo xtask kernel-cases --only ID,ID   # only these cases

`cargo test` checks the committed exports; after generating,
`cargo test --release --test kernel_cases -- --ignored` checks every case in
`out/cases/` too. The `eval-*` cases test the closed-term evaluator
(`src/check/eval/`); each claim is proved by `Eq.refl`, so only reduction
decides it, and each has a false twin.

The `eval434-*` cases come from `lean/KCases434.lean`, built with Lean
v4.34.0 and exported with the lean4export commit for it (pinned in
`xtask/src/kernel_cases/mod.rs`; the first run fetches it from GitHub and
builds it into `out/`). They test the evaluator's fast paths that are only for Lean versions before v4.36.0.
Their `lean` column is still the verdict of v4.36.0's `leanchecker`, which
checks any export.

`lean/KCases.lean` holds the valid source declarations.
`cargo xtask kernel-cases` compiles it, runs `leanexport` on the closure of a
few constants, and applies the mutation defined in
`xtask/src/kernel_cases/cases.rs`. Some cases (universe levels) are built from
scratch (`export.rs` there). The output is deterministic. Lean names the module
after its path from `tests/kernel`, where the generator runs it, and `sorry`
records its source line, so moving lines in the Lean files (even comment lines)
changes the exports. Exports up to 16 KB are committed under `exports/`. The rest (mostly the Nat and String cases, whose closures
pull in much of the prelude) are only generated.

Cases that Lean itself rejects as Lean source are built in two ways:
- by editing a valid export;
- by declaring the type `unsafe` (so Lean emits its recursors) and then
  clearing the `isUnsafe` flags (positivity).

Statements proved by `sorry` in the source get their proof replaced by `Eq.refl`.

## Cases marked `either`

- `univ-imax-assoc`: `imax u (imax v w)` and `imax (max u v) w` are equal for
  every assignment, which a syntactic level normaliser need not prove.
- `nat-pow-2-24-plus1`, `nat-pow-exp-u32`, `nat-shl-limit`, `nat-shl-zero-u32`:
  true claims at or beyond Lean's Nat limits. These are an exponent or shift
  that does not fit in 32 bits, and a result over `LEAN_NAT_MAX_SIZE`, which
  defaults to 128 MB and is checked as `size(base) > max / exponent` for
  `Nat.pow`.

## Open cases

`open.tsv` lists the cases nitrolean gets wrong today (found by the
differential fuzzer of `tests/fuzz/`, with their class and a note). `cargo
test` expects each of them to still give the wrong verdict, so a fix has to
take its case off the list. The `fuzz-*` cases are the fuzzer's minimised
disagreements; where `expected` and `lean` differ, `why` says which side is
right.

`checker-results.tsv` records the verdicts of other independent checkers on
these cases.
