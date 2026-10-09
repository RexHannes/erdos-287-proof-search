#!/usr/bin/env bash
# Native-environment audit of the external SW/BV theorems of openai/math and of the
# transcription in RequestProject/Erdos287/SourceChain/OAIImport/Defs.lean.
# Usage: bash external/oai_primegaps_crosscheck/run.sh [WORKDIR]   (needs network + elan)
set -eu
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
W="${1:-/tmp/oaipg}"
COMMIT=adc7f1241b42e322a6451854ab7e4b4c146bf78a
mkdir -p "$W"
if [ ! -d "$W/src" ]; then
  git clone --filter=blob:none https://github.com/openai/math "$W/src"
fi
git -C "$W/src" checkout -q "$COMMIT"
mkdir -p "$W/OAI/NumberTheory"
rm -rf "$W/OAI/NumberTheory/PrimeGaps"
cp -r "$W/src/lean/OAI/NumberTheory/PrimeGaps" "$W/OAI/NumberTheory/"
cp "$W/src/lean/lean-toolchain" "$W/lean-toolchain"     # leanprover/lean4:v4.34.1
cp "$HERE/lakefile.toml" "$W/lakefile.toml"
# verbatim copy of the transcription, followed by the cross-check
{ echo "import OAI.NumberTheory.PrimeGaps.Main"; grep -v '^import Mathlib$' \
    "$ROOT/RequestProject/Erdos287/SourceChain/OAIImport/Defs.lean"; \
  cat "$HERE/CrossCheckTail.lean"; } > "$W/CrossCheck.lean"
cd "$W"
grep -rnE '^\s*axiom |sorry|native_decide|implemented_by|\bunsafe\b' OAI/NumberTheory/PrimeGaps \
  && { echo "FAIL: forbidden token in external sources"; exit 1; } || echo "no forbidden tokens"
lake exe cache get
lake build OAI.NumberTheory.PrimeGaps.Main
lake env lean CrossCheck.lean
