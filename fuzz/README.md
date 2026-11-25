# Coverage-guided fuzzing (cargo-fuzz)

Three libFuzzer targets for nitrolean's input paths. The goal: on any
malformed input, a clean error or verdict, never a panic, a hang,
unbounded memory or a crash. The differential fuzzer against Lean's kernel
is in `tests/fuzz/`.

| target | what it runs |
|---|---|
| `read_ndjson` | `reader::read` on arbitrary bytes |
| `check_export` | `reader::read`, then `check::check_env` on every input up to 64 KB that decodes |
| `read_olean` | `olean::load` on arbitrary bytes, written as a module with no toolchain and no imports available |

Setup (nightly Rust, as cargo-fuzz needs it):

    rustup toolchain install nightly --profile minimal
    cargo +nightly install cargo-fuzz
    cargo xtask fetch-corpus         # the exports the corpora are seeded from
    cargo xtask difffuzz seed-corpus # fuzz/corpus/<target>/

Running:

    cd fuzz
    cargo +nightly fuzz run read_ndjson corpus/read_ndjson -- -dict=dict/ndjson.dict -timeout=10 -rss_limit_mb=4096 -max_total_time=600
    cargo +nightly fuzz run check_export corpus/check_export -- -dict=dict/ndjson.dict -timeout=10 -rss_limit_mb=4096 -max_total_time=600
    cargo +nightly fuzz run read_olean corpus/read_olean -- -timeout=10 -rss_limit_mb=4096 -max_total_time=600
    cargo +nightly fuzz tmin check_export artifacts/check_export/crash-...   # minimise a finding

`dict/ndjson.dict` holds the keys and values of the export format.
`seeds/FuzzTiny.lean` is a module with no imports (`prelude`), so its
`.olean` loads on its own and the `read_olean` target gets past the import
closure and into decoding.

Some valid inputs are slow or large by design (the corpus's `arena/perf`
tests, a literal `2^(2^30)`). The seed script leaves `arena/perf` out of the
`check_export` corpus, but a timeout or an out-of-memory report must still be
checked against Lean (`leanchecker --from-export`) before it counts as a bug.
