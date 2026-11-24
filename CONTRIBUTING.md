# Contributing

This repository is public. Before committing, run

    scripts/public-check.sh

It checks the tree and the messages of the commits on top of `origin/main`
(pass a range such as `main..HEAD` to check others, or `--tree-only`). It
checks that `README.md` is the one expected line, and refuses home directory
paths, IPv4 addresses outside the documentation ranges, build artifacts,
binaries and files over 1 MB, and co-author trailers in commit messages. A
binary or large file that belongs in the repository goes in
`scripts/public-check.allow`. CI runs the check on every pull request and
push to `main`, together with its test, `scripts/public-check-test.sh`.
`scripts/selfcheck.sh` runs it too.
