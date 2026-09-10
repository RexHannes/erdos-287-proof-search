#!/bin/sh
# Build a self-contained source archive of this project for independent replay.
#
#   sh scripts/make_archive.sh          # -> ../erdos287-U2.tar.gz
#
# The archive contains the Lean sources, the lakefile, the toolchain pin and the Mathlib
# manifest, the certificate data and the audit scripts -- everything needed to run
#
#   lake exe cache get && lake build
#   python3 scripts/audit.py && python3 scripts/audit_u2.py
#
# It deliberately excludes .lake/ (build artefacts and the Mathlib checkout) and .git/.
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd)
NAME=erdos287-U2
OUT=${1:-"$ROOT/../$NAME.tar.gz"}
cd "$ROOT/.."
tar --exclude=".lake" --exclude=".git" --exclude="*.tar.gz" \
    -czf "$OUT" "$(basename "$ROOT")"
echo "wrote $OUT"
