#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export PATH="$HOME/.elan/bin:$PATH"
export ELAN_TOOLCHAIN="$(cat lean-toolchain)"
pin_record="$(mktemp)"
trap 'rm -f "$pin_record"' EXIT
python3 - "$pin_record" <<'PIN'
import hashlib,json,sys
from pathlib import Path
names=['lean-toolchain','lakefile.toml','lake-manifest.json']
Path(sys.argv[1]).write_text(json.dumps({n:hashlib.sha256(Path(n).read_bytes()).hexdigest() for n in names}))
PIN
if ! command -v elan >/dev/null 2>&1; then
  installer="$(mktemp)"
  curl --fail --silent --show-error --location https://elan.lean-lang.org/elan-init.sh -o "$installer"
  sh "$installer" -y --default-toolchain none
  rm -f "$installer"
fi
lean --version
lake exe cache get
python3 - "$pin_record" <<'PIN'
import hashlib,json,sys
from pathlib import Path
for name,digest in json.loads(Path(sys.argv[1]).read_text()).items():
    assert hashlib.sha256(Path(name).read_bytes()).hexdigest()==digest, f'Pin changed: {name}'
print('All original toolchain and dependency pins preserved.')
PIN
