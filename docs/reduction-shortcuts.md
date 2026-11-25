# Shortcuts in reduction and universe levels

Small techniques in the checkers' reduction and in universe levels. Each
leaves every weak head normal form and every verdict as it was. Each is
behind a constant, so that it can be switched off to compare.

| constant | where | what |
|---|---|---|
| `CASES_DIRECT` | `src/check/nbe/cases.rs` | `casesOn`s and matchers go straight to the chosen branch |
| `SMALL_NAT` | `src/check/ext.rs` | `Nat` operations on literals below 2^64 without big integers |
| `NORM_MEMO` | `src/check/univ.rs` | normal forms of levels remembered |
| `OWN_LEVELS` | `src/check/univ.rs` | a constant at its own universe parameters is not substituted |
| `LSUB_DIRECT` | `src/check/nbe/lsub.rs` | a direct-mapped table in front of the level substitution caches |
| `PARAM_CLASSES` | `src/check/nbe/lsub.rs` | one substitution per sequence of parameter names |

## `casesOn`s and matchers

The evaluating checker (`src/check/nbe/`) recognises a definition of the
shape of a `casesOn`, or a matcher of nested `casesOn`s, once per constant,
with the detectors of the closed-term evaluator (`src/check/shape.rs`,
described under "Matches" in `docs/kernel-compute.md`). Its `whnf` reduces
an application of one whose major premises reduce to constructors straight
to the chosen minor premise applied to the fields and the remaining
arguments. Unfolding the definition, then the `casesOn`s, then reducing
the recursor gives the same application, after building the motive and
every minor premise. Any other application (a major premise that is not a
constructor, a projection in the spine) unfolds as before. Definitional
equality still unfolds such definitions one step at a time.

Constants of none of the shapes are recorded in a bit set by name, so the
test on every unfolding is one bit. A first version kept every constant in
a map and cost more on Mathlib than it saved.

## `Nat` literals below 2^64

Both checkers' `Nat` reductions (the binary operations of `Nat`,
`Nat.succ`, and a literal turned into `Nat.succ` of its predecessor)
compute on 64-bit integers when the operands are below 2^64 and so is the
result (`NatOp::small`). Otherwise, and for the kernel's limits on the
size of literals (which no result below 2^64 reaches), the big-integer
path decides as before. A unit test compares the two on edge values.

## Universe levels

- `univ::normalize` remembers its results per store. Levels are
  hash-consed, so a level's normal form is computed once.
- A constant used at its own universe parameters (`c.{u, v}` in a
  declaration whose parameters are `u, v`, where `c`'s are `u, v` too) is
  taken as it is. Substituting parameters by themselves changes nothing:
  `instantiate_lparams` returns the term, and the evaluating checker uses
  the identity substitution, whose terms evaluate as written and share
  the caches of terms without parameters.
- The evaluating checker's caches of substituted levels and level lists
  have a direct-mapped table of 4096 entries in front of their maps. Most
  lookups are for the few levels of the declaration at hand.
- A substitution depends only on the names it replaces and what replaces
  them. The evaluating checker keys it by one parameter list per sequence
  of names, so `c.{u}` and `d.{u}` at the same levels are one substitution,
  and the levels and values cached under it are shared.

## Measurements

All of Mathlib v4.36.0 from its `.olean` files, one loading and one checking
thread (`check --olean --stats -j 1 --threads 1 --module Mathlib`), counted
by Cachegrind (`--cache-sim=no`) on aarch64 Linux. Every run accepted all
808 087 declarations. Loading (the `.olean` decoder and string pool,
about 207 G instructions) varies by about ±1.5 G between runs of the same
build, so the effects are given on the rest, the checking.

| build | instructions | checking | checking against main |
|---|---:|---:|---:|
| main at 1784a3e | 1 744.2 G | 1 535.5 G | |
| all of the above but `PARAM_CLASSES` | 1 709.6 G | 1 502.2 G | −33.4 G (−2.2%) |
| all of the above | 1 685.1 G | 1 477.6 G | −57.9 G (−3.8%) |

Each constant switched off in turn, against all but `PARAM_CLASSES` on:

| switched off | checking | its saving |
|---|---:|---:|
| `CASES_DIRECT` | 1 502.2 G | 0.0 G |
| `SMALL_NAT` | 1 502.2 G | 0.0 G |
| `NORM_MEMO` | 1 503.2 G | 1.0 G (0.07%) |
| `OWN_LEVELS` | 1 526.6 G | 24.5 G (1.6%) |
| `LSUB_DIRECT` | 1 508.7 G | 6.5 G (0.4%) |

`PARAM_CLASSES`, added on top, saves another 24.5 G (1.6%). Direct
`casesOn`s and small `Nat` literals save nothing measurable on Mathlib,
where `whnf` seldom meets a matcher on a constructor or arithmetic on
literals. Direct `casesOn`s take the corpus (`cargo xtask corpus`) from
34.1 to 21.9 s.
