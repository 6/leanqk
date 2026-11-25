# Corpus oracle results

Written by `cargo xtask oracle run` (2026-11-25;
nitrolean 0.1.0-alpha.1, 12 cores). How the verdicts are
obtained is in `README.md`. Times are wall-clock seconds and memory is peak resident MiB,
of the first run on the whole export (`check --threads 0` for nitrolean,
`leanchecker --from-export` for Lean).

| project | Lean | declarations | agree | nitrolean-only reject | nitrolean-only accept | nitrolean | leanchecker | notes |
| --- | --- | ---: | ---: | ---: | ---: | --- | --- | --- |
| batteries | v4.36.0 | 30 168 | 30 168 | 0 | 0 | 5.37 s, 139 | 14.8 s, 334 |  |
| aesop | v4.36.0 | 22 621 | 22 621 | 0 | 0 | 2.65 s, 87 | 7.29 s, 227 |  |
| plausible | v4.36.0 | 12 460 | 12 460 | 0 | 0 | 2.33 s, 82 | 5.88 s, 201 |  |

## Variants

nitrolean's verdicts on each project from the NDJSON export and from the project's .olean
files, with all cores and with one thread. The .olean runs load the roots and everything
they import, the Lean core library included, so they check more than the export.

| project | NDJSON, all cores | NDJSON, 1 thread | .olean, all cores | .olean, 1 thread | identical |
| --- | --- | --- | --- | --- | --- |
| batteries | 5.37 s, 139 | 5.41 s, 139 | 21.2 s, 860; accepts | 22.1 s, 717; accepts | yes |
| aesop | 2.65 s, 87 | 2.66 s, 87 | 19.3 s, 820; accepts | 20.1 s, 694; accepts | yes |
| plausible | 2.33 s, 82 | 2.32 s, 80 | 18.1 s, 740; accepts | 19.1 s, 600; accepts | yes |

## Mismatches

None.
