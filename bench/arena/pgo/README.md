# Training data for profile-guided builds

`init-prefix.ndjson.xz` is the first 154,000 lines (7,990,926 bytes,
SHA-256 `ddd97ce1585f2ddfdd8bedd91c50fd82e01a4ab5b41b8dcb7a58329dc7587169`
unpacked) of the export of Lean's `Init` module, made by `leanexport Init`
from Lean v4.36.0 (commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`), and
packed with `xz -9e`. An export lists every term before the lines that use
it, so its first lines are an export too (2,285 declarations, all accepted).
Lean and its library are under the Apache License 2.0.

`cargo xtask pgo --repo` trains on it and on the exports of `tests/kernel`.
The arena's build uses this, since it has no other exports at hand (see
`../nitrolean.yaml`). To remake the file:

    leanexport Init | head -n 154000 | xz -9e > init-prefix.ndjson.xz
