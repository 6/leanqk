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

Lean is pinned in `lean-toolchain` (elan), Python in `mise.toml`.

    cd tests/kernel
    mise exec -- python -I gen.py            # all cases into out/cases/ (about 23 MB, not committed)
    mise exec -- python -I gen.py --lean     # also run leanchecker on each case
    mise exec -- python -I gen.py --update   # rewrite cases.tsv and exports/
    mise exec -- python -I gen.py --check    # fail if cases.tsv or exports/ are stale

`lean/KCases.lean` holds the valid source declarations. `gen.py` compiles it,
runs `leanexport` on the closure of a few constants, and applies the mutation
defined in `cases.py`. Some cases (universe levels) are built from scratch with
`exportlib.py`. The output is deterministic. Exports up to 16 KB are committed
under `exports/`. The rest (mostly the Nat and String cases, whose closures
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

`checker-results.tsv` records the verdicts of other independent checkers on
these cases.
