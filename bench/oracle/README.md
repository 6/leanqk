# Corpus oracle

Checks that nitrolean gives the same verdict as Lean's own checker, declaration by
declaration, on real public Lean projects. Each project in `projects.tsv` is pinned to a
commit and a toolchain. It is built, its declarations are exported, and the export is
checked by `leanchecker --from-export` and by nitrolean. The verdicts are then compared
for each declaration. This is run by hand, not in CI.

| File | What it does |
| --- | --- |
| `projects.tsv` | the pinned projects, one per line, with their tier |
| `exports.sha256` | SHA-256 of every export `cargo xtask oracle build` made |
| `RESULTS.md` | the last results (tier 1: about 3 minutes once built) |

The tooling is `cargo xtask oracle` (in `xtask/src/oracle/`):

| command | what it does |
| --- | --- |
| `build` | fetches, builds and exports the projects of a tier; checks the exports' SHA-256 against `exports.sha256` |
| `run` | runs both checkers and the variants, compares the verdicts, writes `RESULTS.md` |
| `reduce` | shrinks a declaration the checkers disagree on to a small export for `tests/kernel` |
| `all` | `cargo build --release`, then `build`, then `run` |

Needs `git elan cargo` and GNU `time`. A typical run:

```sh
cargo xtask oracle all                 # tier 1: a few minutes once the projects are built
cargo xtask oracle all --tier 2        # opt-in: larger projects
cargo xtask oracle all --only aesop    # one project
```

Sources and build trees go under `cache/`, and exports and logs under `out/`. Both are
git-ignored; `ORACLE_CACHE` and `ORACLE_OUT` override them. A project that is already built
is not built again, so a second run only reruns the checkers. Every command has `--help`.

## Tiers

Tier 1 runs routinely and must stay quick, since it serves as a regression check. Tiers 2
and 3 are opt-in with `--tier`. Adding a project means adding one line to `projects.tsv`:
the repository, the commit, its `lean-toolchain`, the Lake subdirectory, the root modules,
the prefixes of its own modules, and whether to use the Mathlib cache.

## What is exported

The export of a project is the closure of the non-internal constants declared in its own
modules (`../kernel-compute/lean/ListOwn.lean`). That is, the project's own declarations
and everything they use from their dependencies. The export is written by the exporter of
the project's toolchain: the `leanexport` that ships with Lean from v4.35.0 on, and before
that `github.com/leanprover/lean4export` at the commit that bumps it to that toolchain
(pinned in `xtask/src/oracle/mod.rs`). Supported toolchains are the stable releases from v4.28.0 to
v4.36.0, whose exporters write format 3.1.

## Lean's verdict

Lean's verdict comes from `leanchecker --from-export` of the project's toolchain. For
toolchains before v4.35.0, it comes from that of v4.36.0, the version nitrolean targets,
because `--from-export` came with v4.35.0.

## Per-declaration verdicts

Both checkers stop at the first declaration they reject. `oracle run` therefore repeats a run
that rejects a declaration D on the export without D:

- if D is a theorem, it is replaced by an axiom of the same type, so the declarations that
  use it are still checked;
- otherwise, D's record (a whole mutual block for an inductive) is dropped, together with
  every record that depends on it. Those records count as `skipped`.

This repeats until the checker accepts what is left, or after `--max-rounds` runs. Each
constant then has a verdict for each checker: `accept`, `reject:<kind>` or `skipped`. The
error kind is taken from the message (`KINDS` in `xtask/src/oracle/mod.rs`). Lean names the declaration in
`while replaying declaration 'D'`, and nitrolean in `declaration 'D'`. The constants are
compared one by one:

- **agree**: both accept; both reject (if the kinds differ, it is listed as a mismatch);
  or both skip.
- **nitrolean-only reject**: Lean accepts and nitrolean rejects.
- **nitrolean-only accept**: nitrolean accepts and Lean rejects. This would be a
  soundness bug in nitrolean, and `oracle run` prints it as `SOUNDNESS`.

A constant that one checker skips and the other does not cannot be compared. It is counted
in the notes. When both checkers reject an export but blame different declarations, both
declarations show up as mismatches. This happens, for example, when nitrolean rejects an
inductive record whose flags it does not derive itself, and Lean only fails later on a
declaration that uses it. Error kinds are coarse classes of the two checkers' messages, so a
kind difference is worth a look but is not necessarily wrong.

On the committed exports of `tests/kernel`, the two checkers give the same per-declaration
verdicts and kinds on 97 of the 99. On the other 2, `eta-recursive-isrec-lie` and
`mutual-all`, both reject the export but blame different declarations.

## Variants

Every project is checked four ways by nitrolean:

- from the NDJSON export, with all cores and with `--threads 1`;
- from the project's `.olean` files (`check --olean DIR --module ROOT`), with all cores
  and with `--threads 1`.

The two export runs must give identical verdicts for every constant. The `.olean` runs
cannot be filtered, so each gives one verdict. It must be accept if the export runs
rejected nothing; otherwise, it must reject one of the declarations they rejected, with
the same kind. The `.olean` runs also load everything the roots import, so they check more
than the export. nitrolean's `.olean` reader supports Lean v4.36.0 only, so projects on
other toolchains have no `.olean` runs (`n/a`).

## Reducing a mismatch

```sh
cargo xtask oracle reduce bench/oracle/out/<id>/export.ndjson <declaration>
```

This starts from the declaration's closure in the export. It turns as many of the closure's
definitions and theorems into axioms as it can while the two checkers still disagree in the
same way, then drops whatever is no longer used. The result goes to
`reduced/<declaration>.ndjson`, and a `tests/kernel/cases.tsv` line is printed for it.

## Later candidates

These projects have been looked up but not yet run. Each commit's `lean-toolchain` was read
at that commit. They are for tiers 2 and 3. "Mathlib" means the project uses Mathlib's
cache.

| project | repository | commit | toolchain | notes |
| --- | --- | --- | --- | --- |
| proofwidgets | leanprover-community/ProofWidgets4 | `2f0f3520daeac2d9310ff25b7a877a0e5cdaa203` | v4.36.0 | UI library |
| qq | leanprover-community/quote4 | `ff055a2fcc835935e0ae607339b455a5f5896b4b` | v4.36.0 | metaprogramming |
| import-graph | leanprover-community/import-graph | `8370c640afcd1cc3fb1cb9bf1560cc66eafee5e0` | v4.36.0 | tooling |
| lean4-cli | leanprover/lean4-cli | `50810f72af7618bee62fe9800dc26e806c188703` | v4.36.0 | programming |
| doc-gen4 | leanprover/doc-gen4 | `b3ed25bf7905565f793c47f2a13737d742d96f14` | v4.36.0 | programming |
| verso | leanprover/verso | `6674cf83c82a2c260bf5827d44e58f26568f7cbe` | v4.36.0 | several libraries |
| cedar-spec | cedar-policy/cedar-spec | `0e8c45ca4e920ebe78b6bc705263a0b56467bb66` | v4.36.0 | verification; subdirectory `cedar-lean` |
| iris-lean | leanprover-community/iris-lean | `40e6418437a794dcd0429bfbe4d6b60fdafb2ecd` | v4.36.0 | program logic; subdirectory `Iris` |
| lean-auto | leanprover-community/lean-auto | `1b07c5c089785e5811165f2c67d11ec3ffb3e58c` | v4.36.0 | automation |
| duper | leanprover-community/duper | `0958200fe25740c5a171bb2bf67559d631165d59` | v4.36.0 | superposition prover |
| mathlib | leanprover-community/mathlib4 | `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` | v4.36.0 | tier 3 |
| cslib | leanprover/cslib | `22b39634cb3dc80d829683ad1f65c5680b722309` | v4.36.0 | Mathlib |
| lean-cam-combi | YaelDillies/LeanCamCombi | `4c74f9c9dcb372349b2106c684fade092cd0ac78` | v4.36.0 | Mathlib |
| pfr | teorth/pfr | `54dc86a9c2eb28daf5b9f7593205cdc12345f27c` | v4.36.0 | Mathlib |
| pnt-plus | AlexKontorovich/PrimeNumberTheoremAnd | `b47896b36cc6e36559189281330930ecf25fae7a` | v4.36.0 | Mathlib |
| flt-regular | leanprover-community/flt-regular | `0b18be7264c97208d7529c69da24c0bc2e27da8e` | v4.36.0 | Mathlib |
| con-nf | leanprover-community/con-nf | `4f2d84a7e6716c91c6619776afcfc2cb9f4e86e6` | v4.36.0 | Mathlib |
| analysis | teorth/analysis | `b019951163e7d6c5ff10795b7a12fd36af579969` | v4.36.0 | Mathlib |
| compfiles | dwrensha/compfiles | `e77a62609fb89d80ec12a27fb251b4f4f3600c89` | v4.36.0 | Mathlib; heavy `decide` and `norm_num` |
| arklib | Verified-zkEVM/ArkLib | `608f550b89b881cc1c9c6c32825fcc61b53c96ab` | v4.36.0 | Mathlib; cryptography |
| aeneas | AeneasVerif/aeneas | `fb44cb400eb6bfe7dce97422ebe8fa748b7e4f9b` | v4.36.0 | Mathlib; Rust verification; subdirectory `backends/lean` |
| flt | ImperialCollegeLondon/FLT | `a3210204ad8876e851e32f73dd97d882bf1ccd0a` | v4.35.0 | Mathlib; tier 3 |
| sphere-eversion | leanprover-community/sphere-eversion | `33ab3d626854a0f0f04ed5772e3102d652e96475` | v4.35.0 | Mathlib |
| lnsym | leanprover/LNSym | `49f8a1d9e46f8dcfc345f4bc15d35b0ba845ff5c` | v4.35.0 | Arm verification, `bv_decide` |
| lean-hammer | JOSHCLUNE/LeanHammer | `93734d62412e5af695439eab116efcece30e80a9` | v4.34.0 | automation |
| carleson | fpvandoorn/carleson | `c82b9f685d43c9c35ceddcc89fdb97eee0482ff3` | v4.32.0 | Mathlib; tier 3 |
| clean | Verified-zkEVM/clean | `1e563b9c27991b3795eb440c1ee0757edb4ce8b1` | v4.30.0 | Mathlib; zk circuits |
| sampcert | leanprover/SampCert | `4c0ed99d1431628cd0bebf8de3bae02bc9f828b6` | v4.28.0 | Mathlib; differential privacy |

Projects on patch releases (such as equational_theories on v4.29.1) would need an exporter
built for that release. The Lean core library (`Init`, `Std`, `Lean`) and the Lean test
suite would each need their own build step.
