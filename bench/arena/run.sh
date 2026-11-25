#!/usr/bin/env bash
# Run checkers on the arena test set: bench/arena/run.sh [run.py run options].
# See bench/arena/run.py --help and bench/arena/README.md.
set -euo pipefail
exec python3 -I "$(dirname "${BASH_SOURCE[0]}")/run.py" run "$@"
