#!/bin/sh
# Every listing in cdclkit-sat-tutorial.tex is pulled from code/ with \lstinputlisting, so
# the document cannot drift from what runs. This re-runs all of it.
#
#   cd tex/tutorial && ./run_examples.sh
#
# Uses an installed cdclkit if there is one -- which is what a reader of the
# tutorial has -- and otherwise falls back to the checkout two levels up.
set -e
cd "$(dirname "$0")"
REPO=$(cd ../.. && pwd)
PY=${PYTHON:-python3}

if ! "$PY" -c "import cdclkit" 2>/dev/null; then
    if "$PY" -c "import sys; sys.path.insert(0,'$REPO'); import cdclkit" 2>/dev/null; then
        echo "c using the checkout at $REPO"
        export PYTHONPATH="$REPO${PYTHONPATH:+:$PYTHONPATH}"
    else
        echo "cdclkit is not importable. Either:" >&2
        echo "    pip install cdclkit" >&2
        echo "  or run with PYTHON=/path/to/an/interpreter/that/has/it" >&2
        exit 1
    fi
fi

for f in code/ex*.py; do
    echo "=== $f"
    "$PY" "$f"
done
# ex6_pipeline.py writes build/timetable2.{cnf,drat}; the second Rust binary
# reads them back, so the order here matters.
echo "=== code/rust-demo (checker API)"
(cd code/rust-demo && cargo run --quiet --bin rust-demo)
echo "=== code/rust-demo (reading the files Python wrote)"
(cd code/rust-demo && cargo run --quiet --bin check_files)
