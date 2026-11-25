# Famous SAT results: cube-and-conquer proofs, one cube at a time

Four well-known theorems were proved by SAT solvers with cube and conquer: the formula is split
into many *cubes* (partial assignments that together cover every case), and each cube's
subproblem, the formula with the cube's literals added as unit clauses, is refuted on its own.
The whole proofs are far too large to check in full here (petabytes for Schur number five), but
every cube is an independent kernel theorem, so a sample of cubes shows how fast each proof
would be checked, and the cubes are a natural unit for checking on many threads.

| result | statement | public files used | cubes |
| --- | --- | --- | ---: |
| Schur number five (Heule 2018) | S(5) = 160: every 5-colouring of 1..161 has a monochromatic a + b = c | `Schur_161_5_SBP.cnf`; cube file `10330615-shuf-aa` | 10 330 615 |
| Keller's conjecture, dimension 7 (Brakensiek, Heule, Mackey, Narváez 2020) | no clique of size 128 in the Keller graph G(7,3) | `output/s3.cnf`, `output/s3.dnf`, `logs/table-s3.txt` of `Keller-encode` | 21 557 |
| Boolean Pythagorean triples (Heule, Kullmann, Marek 2016) | 1..7825 cannot be 2-coloured without a monochromatic a² + b² = c² | `transformed.cnf`, `million.cubes`, `full-results7824.data` | 1 000 000 |
| Empty hexagon number (Heule, Scheucher 2024) | every 30 points in general position contain an empty hexagon | the formula of the Lean-verified encoding, `final-30-ours-flat.cnf`, and `marijn-cubes.icnf` | 312 418 |

`data/sources.tsv` has the URL and SHA-256 of each file. The Schur files were on a server that
no longer serves them; the cube file and its log are fetched from the Internet Archive's copies,
which hold the first 5 MiB of each (49 517 complete cubes of the first of five cube files), so the
Schur cubes are drawn from those. The Keller and empty-hexagon files are fetched from their
repositories at a pinned commit, the others from the authors' pages.

The tooling is `cargo xtask famous-sat` (`xtask/src/famous_sat/`); it drives git, curl, elan,
Lake and CaDiCaL, and uses the Lean helpers of `../kernel-compute` and the checkers and
measurement of `cargo xtask kc`:

| Command | What it does |
| --- | --- |
| `famous-sat fetch` | builds the exports of `data/cubes.tsv` into `out/famous-sat/` (shares the pins and cache of `cargo xtask kc`) |
| `famous-sat parallel` | checks one export with `nitrolean check --jobs N`, N = 1, 2, 4, 8, 12 |
| `famous-sat coverage`, `famous-sat scaling` | the tables below, from the TSVs |
| `famous-sat survey` | solves sample cubes with a time limit (how the cubes were chosen) |
| `famous-sat cube-cnf`, `lrat-core`, `renumber` | the conversions `fetch` makes: a cube's subproblem; restricting formula and proof to the clauses the proof uses; renaming variables to 1, 2, ... (trimming is `cargo xtask kc lrat-trim`) |
| `kc build-checkers`, `kc measure` | build the four checkers; run them under a time and memory limit |

`data/` has `sources.tsv`, `cubes.tsv` (the cubes and the SHA-256 of each formula and proof as
stated) and `survey.tsv` (the surveyed cubes; the random ones were drawn with another generator
than `survey`'s, so their indices are listed rather than reproducible from a seed). Needs `git
curl make c++`, `elan` and cargo. Typical run (`out` and `cache` are `bench/kernel-compute/`'s):

```sh
cargo xtask kc build-checkers
cargo xtask famous-sat fetch
cargo xtask kc measure --out out/famous-60.tsv out/famous-sat/*.ndjson
cargo xtask famous-sat parallel out/famous-sat/keller7-bundle48-renumbered.ndjson
cargo xtask famous-sat scaling out/famous-sat/parallel.tsv out/famous-sat/parallel.decl-times.tsv
cargo xtask famous-sat coverage out/famous-sat/manifest.tsv bench/famous-sat/data/survey.tsv \
  cache/famous-sat/src out/famous-60.tsv
```

## The exports

For each cube of `data/cubes.tsv`, `fetch` writes the subproblem, solves it with CaDiCaL 2.2.1
(`--lrat --no-binary`, as `cargo xtask kc fetch-lrat`), trims the proof to the lemmas the
empty clause depends on (`cargo xtask kc lrat-trim`), and restricts the formula
to the clauses the proof uses. The export holds
the theorem `(core).Unsat`, stated and exported as `kc fetch-lrat` does: `kernel_lrat`, the
`+kernel` mode of LRAT-Catcher, `debug.skipKernelTC`, and the `lean4export` of Lean v4.30.0. A
refutation of the core refutes the whole subproblem, since the core is a subset of its clauses.
The restricted formula and proof are pinned by SHA-256: `fetch` stops if CaDiCaL gives a
different proof (`--update-pins` reports instead). A second machine reproduced every pin.

The sample, `set` `sample` in `data/cubes.tsv`: per result 6 to 9 cubes whose proofs grow from
under 1 KB to about 9 MB of LRAT. They were chosen from `data/survey.tsv`: random cubes (and,
for the Pythagorean triples, cubes spread over the published proof sizes; for Schur, cubes of 44
or more literals, which are the easy ones) solved with a time limit of 4 to 60 s. They are
therefore the easy end of each proof: in the surveys 2 of 27 Pythagorean, 9 of 243 Keller, 128
of 163 Schur and 107 of 123 empty-hexagon cubes did not finish within the limit, and every
cube used did.

Other sets:

* `keller7-full`: Keller cube 4403 with the whole formula (200 545 clauses, 3.9 MB) instead of
  its 75-clause core; its proof is 2.2 KB.
* `*-renumbered`: the core with its variables renamed to 1, 2, ... (`renumber`). That
  is a different theorem (the same formula up to variable names); it is there to show what the
  variable numbering costs (Keller uses variables up to 39 424, the empty hexagon up to 75 109).
* `keller7-bundle48`: 48 Keller cubes with proofs of 23 to 68 KB, one theorem each, in one export;
  `keller7-bundle48-renumbered` is the same with renumbered variables. These are for `parallel`.
* `base`: the theorem for LRAT-Catcher's 4-clause example, the part every export shares (about
  40 MB of library closure).

`out/famous-sat/manifest.tsv` has per export the CNF bytes, LRAT bytes (as stated), raw LRAT
bytes (as CaDiCaL wrote it), export bytes and solving time.

## Results (one machine, one run each)

12-core aarch64 Linux (one thread per core), 95 GB, nitrolean at this commit (`check` on all
cores, its default), `leanchecker` of Lean v4.36.0, gruszka and nano-lean at the commits of `cargo
xtask kc build-checkers`. `kc measure` with its defaults, 60 s and 4 GiB resident; then nitrolean
again for 600 s where it ran out of time and with 30 GB where it ran out of memory. Wall time in
seconds and peak resident memory in MiB. The nitrolean measured is that of main before the
evaluation-based checking core (pull request 27); a spot check of four exports on 2 cores with the current
main gives the same picture (Keller cube 3002: 3.8 s and 3.4 GB as published, 1.5 s and 240 MB
renamed).

| export | LRAT bytes | nitrolean | leanchecker | gruszka | nano-lean |
| --- | ---: | --- | --- | --- | --- |
| base | 36 | 0.16 s, 79 | 2.71 s, 167 | 0.04 s, 159 | 0.31 s, 166 |
| schur5-cube10449 | 146 124 | 2.69 s, 327 | oom | oom | oom |
| schur5-cube4500 | 361 158 | 7.33 s, 814 | oom | oom | oom |
| schur5-cube33713 | 1 007 107 | 19.9 s, 2 337 | oom | oom | oom |
| schur5-cube33162 | 1 449 860 | 35.4 s, 3 449 | oom | timeout | oom |
| schur5-cube11163 | 3 254 332 | oom; 78.3 s, 8 856 with 30 GB | oom | timeout | oom |
| schur5-cube44260 | 9 242 223 | oom; 293.9 s, 29 146 with 30 GB | oom | timeout | oom |
| keller7-cube16452 | 1 500 | 0.20 s, 89 | oom | 16.8 s, 2 873 | 4.50 s, 3 832 |
| keller7-full | 2 241 | timeout; oom after 235 s at 600 s | timeout | timeout | oom |
| keller7-cube4480 | 6 430 | 0.40 s, 253 | oom | oom | oom |
| keller7-cube8244 | 23 286 | 1.50 s, 1 044 | oom | oom | oom |
| keller7-cube3002-renumbered | 60 923 | 1.78 s, 220 | oom | oom | oom |
| keller7-cube3002 | 67 207 | 4.40 s, 3 385 | oom | oom | oom |
| keller7-cube17228 | 169 449 | oom; 10.6 s, 8 343 with 30 GB | oom | oom | oom |
| keller7-cube1178-renumbered | 351 689 | 11.1 s, 2 564 | oom | timeout | oom |
| keller7-cube1178 | 369 031 | oom; 25.8 s, 19 676 with 30 GB | oom | timeout | oom |
| keller7-cube17832 | 646 537 | oom; oom with 30 GB after 33 s | oom | timeout | oom |
| keller7-cube1854 | 1 902 420 | oom; oom with 30 GB after 30 s | oom | timeout | oom |
| keller7-cube5541 | 9 146 307 | oom; oom with 30 GB after 338 s | oom | timeout | oom |
| ptn-cube126397 | 452 | 0.18 s, 83 | oom | 3.11 s, 1 308 | 1.05 s, 1 076 |
| ptn-cube596811 | 6 409 | 0.29 s, 123 | oom | oom | oom |
| ptn-cube117888 | 20 454 | 0.72 s, 322 | oom | oom | oom |
| ptn-cube659550 | 47 550 | 1.38 s, 617 | oom | oom | oom |
| ptn-cube824009 | 101 922 | 2.86 s, 1 286 | oom | oom | oom |
| ptn-cube650038 | 290 585 | 9.42 s, 3 842 | oom | oom | oom |
| ptn-cube754743 | 670 215 | oom; 24.8 s, 8 612 with 30 GB | oom | oom | oom |
| ptn-cube740347 | 1 254 137 | oom; 46.7 s, 16 362 with 30 GB | oom | oom | oom |
| ptn-cube211974 | 9 020 096 | oom; oom with 30 GB after 87 s | oom | timeout | oom |
| hexagon30-cube195611 | 416 | 0.29 s, 161 | oom | oom | oom |
| hexagon30-cube4416 | 1 328 | 0.35 s, 216 | oom | oom | oom |
| hexagon30-cube241910 | 1 510 | 0.37 s, 233 | oom | oom | oom |
| hexagon30-cube14390-renumbered | 1 466 752 | oom; oom with 30 GB after 94 s | oom | timeout | oom |
| hexagon30-cube14390 | 1 493 253 | oom; oom with 30 GB after 56 s | oom | timeout | oom |
| hexagon30-cube161553 | 3 094 851 | oom; oom with 30 GB after 128 s | oom | timeout | oom |
| hexagon30-cube25643 | 8 505 190 | oom; oom with 30 GB after 238 s | oom | timeout | oom |

nitrolean checks every sample cube up to 1.4 MB of LRAT for Schur, 290 KB for the Pythagorean
triples, 67 KB for Keller and the small empty-hexagon cubes within 60 s and 4 GiB; the other
checkers only the smallest one or two of a result, or none. With 30 GB it gets to 9.2 MB (Schur)
and 1.25 MB (Pythagorean triples), 369 KB (Keller); no empty-hexagon cube above 1.5 KB fits in
30 GB.

What limits it is memory, and memory grows with the formula's variable numbers rather than with
the proof:

* Cost per step follows the largest variable index. Keller's variables go up to 39 424, the
  empty hexagon's to 75 109, the Pythagorean triples' to 7 825, Schur's to 805, and per KB of
  proof Schur is the cheapest and the empty hexagon the dearest. The renamed copies show it
  directly: Keller cube 3002 (1 070 clauses, 816 distinct variables, the largest 38 460) takes
  3 385 MiB and 4.4 s as published and 220 MiB and 1.8 s renamed; cube 1178 needs 19.7 GB as
  published and 2.6 GB renamed. The likely cause is that LRAT-Catcher's checker keeps an
  assignment array indexed by variable and the kernel evaluator does not update it in place, so
  each step pays for the whole array; that is a matter for the evaluator (`src/check/eval/`),
  not measured further here. The empty-hexagon cube 14390 runs out of 30 GB either way: its core
  has 12 423 distinct variables, so even renamed its array is large.
* The whole formula is worse still: `keller7-full`, a 2.2 KB proof stated against all 200 545
  clauses of the formula, runs out of 4 GiB after 235 s. That is why every export states the cube
  against the clauses its proof uses. A checked cube-and-conquer proof needs the theorem about
  the whole formula, so this part of the work is still ahead.

Both are costs of evaluating this checker in the kernel, not of the proofs, so they are the
first thing to fix for checking these results at all.

### How much of each proof, and how long the whole would take

`cargo xtask famous-sat coverage`; the factors and the rate are explained below the table:

| result | cubes | sampled | sample LRAT | whole proof (published) | whole proof as LRAT here (factor) | sample share | nitrolean rate | whole proof at that rate |
| --- | ---: | ---: | ---: | --- | --- | ---: | ---: | ---: |
| Schur number five | 10330615 | 6 (5.8e-7 of the cubes) | 15.5 MB | 2 PB of DRAT (paper) | 1.28 PB (0.64) | 1.2e-8 | 35.4 KB/s | 1147 years |
| Keller, dimension 7 | 21557 | 9 (4.2e-4 of the cubes) | 12.3 MB | 103 GB of proof (logs) | 98.2 GB (0.95) | 1.3e-4 | 15.1 KB/s | 75.2 days |
| Pythagorean triples | 1000000 | 9 (9.0e-6 of the cubes) | 11.4 MB | 193 TB of DRAT (logs) | 631 TB (3.27) | 1.8e-8 | 28.1 KB/s | 711 years |
| Empty hexagon | 312418 | 6 (1.9e-5 of the cubes) | 13.1 MB | 180 TB of LRAT (paper) | 36.1 TB (0.20) | 3.6e-7 | none above 10 KB accepted | - |

"Whole proof as LRAT here" is the published size times the factor between the trimmed,
core-restricted LRAT that the exports state and the published form, measured on cubes above 1 MB
(Keller and the Pythagorean triples against their per-cube logs; Schur and the empty hexagon
against the untrimmed LRAT CaDiCaL wrote for the sample cubes). The rate is nitrolean's, LRAT
bytes per second of wall time above that of `base`, over the sample cubes above 10 KB it accepts
(including the 30 GB runs). The sample is the easy end of each proof, and cost grows faster than
size, so the times are lower bounds; they are for one process using all 12 cores on one cube at
a time. The cubes are independent, so checking them side by side divides the time by at most
the number of cores (see below): at the 7 to 9.6 times measured on 12 cores, Keller's 75 days
become 8 to 11 days on this machine, the
others stay centuries until the memory use above is fixed.

### Checking cubes in parallel

Cube-and-conquer proofs are independent per cube, and `nitrolean check --jobs N` hands the
declarations of an export to N threads (in export order, each with its own type checker). The
test is `keller7-bundle48`: 48 Keller cube theorems, proofs of 23 to 68 KB, one export
(`cargo xtask famous-sat parallel`, median of 3 runs; `bound` is the time if every declaration
took its one-thread time and they were handed out the same way, from `scaling`).

With the variables renamed (`keller7-bundle48-renumbered`, 244 MiB on one thread):

| memory budget | jobs | wall s | check s | speedup | efficiency | bound s | bound speedup | peak MiB |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| default | 1 | 46.1 | 46.0 | 1.00 | 100% | 48.4 | 0.95 | 244 |
| default | 2 | 24.1 | 23.9 | 1.92 | 96% | 24.3 | 1.90 | 357 |
| default | 4 | 12.8 | 12.7 | 3.60 | 90% | 12.2 | 3.76 | 569 |
| default | 8 | 7.7 | 7.6 | 5.96 | 74% | 6.5 | 7.05 | 878 |
| default | 12 | 6.1 | 5.9 | 7.61 | 63% | 4.5 | 10.22 | 1197 |

As published (3.1 GB on one thread), with nitrolean's memory budget (1 GiB by default) and with
it lifted (`--mem-budget-mib 1000000`):

| memory budget | jobs | wall s | check s | speedup | efficiency | bound s | bound speedup | peak MiB |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| default | 1 | 114.3 | 114.1 | 1.00 | 100% | 114.3 | 1.00 | 3120 |
| default | 2 | 59.1 | 58.9 | 1.93 | 97% | 57.9 | 1.97 | 4967 |
| default | 4 | 37.8 | 37.6 | 3.02 | 76% | 29.8 | 3.84 | 7836 |
| default | 8 | 22.8 | 22.6 | 5.00 | 63% | 16.6 | 6.87 | 14858 |
| default | 12 | 16.3 | 16.1 | 7.00 | 58% | 11.5 | 9.90 | 16846 |

| memory budget | jobs | wall s | check s | speedup | efficiency | bound s | bound speedup | peak MiB |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1000000 | 1 | 114.7 | 114.5 | 1.00 | 100% | 114.7 | 1.00 | 3119 |
| 1000000 | 2 | 58.8 | 58.6 | 1.95 | 98% | 57.8 | 1.99 | 4959 |
| 1000000 | 4 | 30.1 | 29.9 | 3.81 | 95% | 29.2 | 3.92 | 7323 |
| 1000000 | 8 | 16.7 | 16.5 | 6.87 | 86% | 15.9 | 7.20 | 12198 |
| 1000000 | 12 | 12.0 | 11.8 | 9.57 | 80% | 11.0 | 10.47 | 17900 |

The scaling is not linear: 7.6 times on 12 cores renamed, 7.0 as published. The schedule is not
the reason. The 48 cube theorems take 98% of the one-thread time, the largest 3.5% of it, so
handing them out in order would allow about 10 times on 12 threads (`bound`). Two things take
the rest:

1. **Each declaration gets slower when others run beside it.** On the renamed bundle, the sum of
   the declaration times is 46.2 s on one thread, 49.9 s on 4 (1.08 times), 57.7 s on 8 (1.24)
   and 65.7 s on 12 (1.43). The slowdown is about the same for every cube theorem (1.24 to 1.52
   times at 12 threads, median 1.41). That points at a resource the threads share, not at
   slower cores: the cores all report the same type, and slower cores would split the cubes into
   two groups. Bound times 1.43 is 6.4 s, close to the 6.2 s measured. The evaluator allocates
   heavily for these terms (the memory growth above), so memory traffic is the likely shared
   resource. Allocator locking is unlikely: nitrolean uses mimalloc, which has per-thread heaps.
2. **The memory budget serializes large declarations.** Once the process held more than 1 GiB
   (since pull request 27, 1 GiB more than when checking started),
   a thread starts a new declaration only when no other is checking one. Each published-numbering
   cube takes 1 to 3.5 GB, so beyond 2 threads the budget keeps cores idle: 7.0 times on 12
   threads with it, 9.6 times without it. Without it, peak memory was 17.9 GB against 16.8 GB
   with it, on a 95 GB machine.

Proposed fixes, none made here. The first two are in the evaluator, which another change owns.

* Reduce the evaluator's allocation per LRAT step: update the assignment array in place when it
  is uniquely referenced, rather than rebuilding it. This removes most of the memory (above) and
  most of the shared memory traffic that slows the threads, so it improves single-thread speed
  and scaling together.
* Size the memory budget to the machine. Make the default a fraction of physical memory, or of
  the cgroup limit when there is one, rather than a fixed 1 GiB. Or compare the budget against
  the memory the running declarations are expected to add, not the whole process. On this
  machine a budget of a few GB per thread would have cost nothing and given back the 27% that
  the budget costs at 12 threads.
* For split proofs with very uneven cubes, hand out the largest theorems first, ordered by proof
  size, which the export knows. With 48 even cubes this changes little, but with the Schur or
  Pythagorean distributions, where the largest cubes are orders of magnitude above the median,
  the last large cube otherwise runs alone at the end.
