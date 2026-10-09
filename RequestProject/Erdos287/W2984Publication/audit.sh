#!/usr/bin/env bash
# Erdős #287 — W2.984 publication subtree: source / firewall / build / negative-control audit.
# Run from anywhere:  bash RequestProject/Erdos287/W2984Publication/audit.sh
# Every check fails loudly (non-zero exit).  ERDŐS #287 REMAINS OPEN.
set -u
cd "$(dirname "$0")/../../.."
SUB=RequestProject/Erdos287/W2984Publication
W3=RequestProject/Erdos287/W3Publication
FILES="$SUB/*.lean RequestProject/Erdos287/W2984Publication.lean $W3/*.lean RequestProject/Erdos287/W3Publication.lean"
fail=0
bad() { echo "FAIL: $*"; fail=1; }
strip() { perl -0pe 's{/-.*?-/}{}gs; s{--[^\n]*}{}g' "$1"; }

echo "== 1. forbidden tokens in code (comments/docstrings stripped)"
probe=$(printf 'theorem t : True := by\n  sorry\n' | perl -0pe 's{/-.*?-/}{}gs; s{--[^\n]*}{}g')
echo "$probe" | grep -Pq '\bsorry\b' || bad "scanner self-test failed"
for f in $FILES; do
  code=$(strip "$f")
  for pat in '\bsorry\b' '\badmit\b' '^\s*axiom\b' '\bunsafe\b' '\bnative_decide\b' \
             '\bbv_decide\b' 'implemented_by' '\bopaque\b' '\bextern\b' 'ofReduceBool' \
             '\bInhabited\b' 'False\.elim'; do
    if echo "$code" | grep -Pq "$pat"; then bad "$f matches $pat"; fi
  done
done

echo "== 2. no provider is constructed (result type = provider) except the derived PairBoundProvider"
for f in $FILES; do
  code=$(strip "$f")
  for p in W3FrameworkProvider AffineChenS1Provider AffineChenS2Provider AffineChenS3Provider \
           AffineChenSquareTailProvider FrameworkFamily FrameworkWindowData; do
    re="^\\s*(noncomputable\\s+)?(def|instance|example|abbrev|theorem)\\b[^\\n]*:\\s*$p\\b[^():\\n]*(:=|where)"
    hits=$(echo "$code" | grep -P "$re" || true)
    if [ -n "$hits" ]; then echo "$hits"; bad "$f constructs $p"; fi
  done
done

echo "== 3. scope firewall: no SR-287 / HLS / Zheng / Lichtman / R11 / PNP imports"
for f in $FILES; do
  if grep -P '^import' "$f" | grep -Piq 'SR287|HLS|Zheng|Lichtman|R11|PNP'; then
    bad "$f imports an out-of-scope module"
  fi
done

echo "== 4. historical files unchanged (only new subtrees and new reports added)"
BASE=$(git rev-list --max-parents=0 HEAD | tail -1)
if ! git diff --quiet "$BASE" -- RequestProject/Erdos287/PostV87V90R RequestProject/Erdos287/PostV87V90R.lean \
     RequestProject/Erdos287/PostV71V87 RequestProject/Erdos287/PostV64V71 ARISTOTLE_SUMMARY.md; then
  bad "historical files modified"
fi

echo "== 5. narrow build (runs #assert_std_axioms_v90, #audit_providers_w2984, firewall asserts)"
if ! lake build RequestProject.Erdos287.W2984Publication > /tmp/w2984_build.log 2>&1; then
  tail -30 /tmp/w2984_build.log; bad "narrow build failed"
fi
if grep -q "declaration uses 'sorry'" /tmp/w2984_build.log; then bad "build reports sorry"; fi

echo "== 6. negative controls (each must FAIL to elaborate)"
mk() { cat > "/tmp/w2984_neg$1.lean"; }
mk 1 <<'X'
import RequestProject.Erdos287.W2984Publication
theorem bad_sorry : 1 = 2 := by sorry
#assert_std_axioms_v90 bad_sorry
X
mk 2 <<'X'
import RequestProject.Erdos287.W2984Publication
theorem bad_native : 10 < 20 := by native_decide
#assert_std_axioms_v90 bad_native
X
mk 3 <<'X'
import RequestProject.Erdos287.W2984Publication
namespace Erdos287.W2984Publication
def fakeS1 (P : W3FrameworkProvider) (h : False) : AffineChenS1Provider P := h.elim
end Erdos287.W2984Publication
#audit_providers_w2984
X
mk 4 <<'X'
import RequestProject.Erdos287.W2984Publication
-- endpoint s = 2.984 is not derivable from the strict-inequality theorem by `lt_irrefl`
example : (2.984 : ℝ) < 2.984 := by norm_num
X
mk 5 <<'X'
import RequestProject.Erdos287.W2984Publication
-- the uncorrected Chen inequality must not be provable
example : ∀ n : ℕ, Erdos287.W2984Publication.ind (Erdos287.W2984Publication.rough
    Erdos287.W2984Publication.primesTo20 20 n) ≤
    Erdos287.W2984Publication.chenRHSLiteral Erdos287.W2984Publication.primesTo20 4 20 n := by
  intro n; exact absurd trivial (by simp)
X
for i in 1 2 3 4 5; do
  if lake env lean "/tmp/w2984_neg$i.lean" > "/tmp/w2984_neg$i.log" 2>&1; then
    bad "negative control $i elaborated (should fail)"
  else
    echo "  control $i rejected as expected"
  fi
done

if [ $fail -eq 0 ]; then echo "W2.984 AUDIT PASSED"; else echo "W2.984 AUDIT FAILED"; exit 1; fi
