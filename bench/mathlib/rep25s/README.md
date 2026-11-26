# rep25s: a slice of Mathlib v4.36.0

`rep25s` is a dependency-closed slice of Mathlib v4.36.0 for benchmarks that
cannot check all of Mathlib: 43,484 declarations in 40,295 work blocks
(a work block is one top-level `axiom`, `def`, `thm`, `opaque`, `quot` or
`inductive` record of the export; an inductive family is one block).

| | |
|---|---|
| lines | 6,881,298 |
| bytes | 367,621,205 |
| SHA-256 | `e8aff3c872ae2b052b49646047f1e6ce331f29e14c394eb4f845a3b01e47b768` |

For comparison, the full export (`cargo xtask mathlib fetch`) has
112,081,718 lines and 6,326,141,213 bytes.

## How it was chosen

371 work blocks were sampled from the full export, and the selection was
closed under dependencies: every block that a selected block refers to is
selected too. `rep25s.roots.jsonl.zst` lists, for each of the 40,295
selected blocks in the full export's order, the Lean name of its first
declaration (one JSON array of name components per line). The list is
frozen, so building the slice needs neither the full export nor a seed.

## Building it

    cargo xtask install-elan --toolchain leanprover/lean4:v4.36.0
    bench/mathlib/rep25s/build.sh MATHLIB_CHECKOUT OUT.ndjson

`build.sh` clones Mathlib at v4.36.0
(`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`) unless the checkout is there,
fetches its prebuilt `.olean` files with `lake exe cache get`, and runs
`OrderedExport.lean`, which imports Mathlib and exports the listed
declarations with everything they depend on, through the LeanExport library
of the toolchain `leanprover/lean4:v4.36.0` (`LeanExport.dumpEnv` with the
names as roots). It then checks the line count, size and SHA-256 above.
Needs git, elan and zstd; about three minutes once Mathlib's cache is
downloaded, and under 7 GiB of memory.

The workflow `.github/workflows/mathlib-bench.yml` builds it this way
(`slice: rep25s`).
