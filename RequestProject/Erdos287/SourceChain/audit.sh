#!/usr/bin/env bash
# Erdős #287 — SourceChain subtree: token / firewall / build / checker / negative-control audit.
# Run from anywhere:  bash RequestProject/Erdos287/SourceChain/audit.sh
# Every check fails loudly (non-zero exit).  ERDŐS #287 REMAINS OPEN.  TAIL-287 NOT BANKED.
set -u
cd "$(dirname "$0")/../../.."
SUB=RequestProject/Erdos287/SourceChain
FILES="$SUB/*.lean RequestProject/Erdos287/SourceChain.lean"
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
             'False\.elim' '^\s*instance\b' '\bexact\?' ; do
    if echo "$code" | grep -Pq "$pat"; then bad "$f matches $pat"; fi
  done
done

echo "== 2. no unconditional tail theorem and no alias of the conditional ones"
for f in $FILES; do
  code=$(strip "$f")
  if echo "$code" | grep -Pq '^\s*(theorem|def|abbrev|lemma)\s+\S*Unconditional'; then
    bad "$f declares an 'Unconditional' tail object"
  fi
  if echo "$code" | grep -Pq ':=\s*(Tail287_of_AnalyticProviders|Tail287_of_MinimalAnalyticProviders|Tail287_of_NarrowProviders)\s*$'; then
    bad "$f aliases a conditional tail theorem"
  fi
done

echo "== 3. CurrentTail / W3 / W2.984 / historical subtrees and ARISTOTLE_SUMMARY.md unchanged"
BASE=$(git rev-list --max-parents=0 HEAD | tail -1)
if ! git diff --quiet "$BASE" -- RequestProject/Erdos287/CurrentTail RequestProject/Erdos287/CurrentTail.lean \
     RequestProject/Erdos287/W3Publication RequestProject/Erdos287/W3Publication.lean \
     RequestProject/Erdos287/W2984Publication RequestProject/Erdos287/W2984Publication.lean \
     RequestProject/Erdos287/PostV87V90R RequestProject/Erdos287/PostV87V90R.lean \
     RequestProject/Erdos287/PostV71V87 ARISTOTLE_SUMMARY.md; then
  bad "protected files modified"
fi

echo "== 4. narrow build (runs #sc_assert_all_std_axioms, provider firewalls, DAG decides)"
if ! lake build RequestProject.Erdos287.SourceChain > /tmp/sc_build.log 2>&1; then
  tail -30 /tmp/sc_build.log; bad "narrow build failed"
fi
if grep -q "declaration uses 'sorry'" /tmp/sc_build.log; then bad "build reports sorry"; fi

echo "== 5. fresh kernel re-check with the installed checker"
CHK=""
for c in leanchecker lean4checker; do
  if lake env which "$c" > /dev/null 2>&1; then CHK=$c; break; fi
done
if [ -z "$CHK" ]; then bad "no kernel checker found"; else
  echo "checker: $CHK"
  if ! lake env "$CHK" --fresh RequestProject.Erdos287.SourceChain > /tmp/sc_check.log 2>&1; then
    tail -20 /tmp/sc_check.log; bad "$CHK --fresh failed"
  fi
fi

echo "== 6. negative controls (each must FAIL to elaborate)"
mk() { cat > "/tmp/sc_neg$1.lean"; }
mk 1 <<'X'
import RequestProject.Erdos287.SourceChain
namespace Erdos287.SourceChain
theorem bad_sorry : 1 = 2 := by sorry
end Erdos287.SourceChain
#sc_assert_all_std_axioms
X
mk 2 <<'X'
import RequestProject.Erdos287.SourceChain
namespace Erdos287.SourceChain
theorem bad_native : 10 < 20 := by native_decide
end Erdos287.SourceChain
#sc_assert_all_std_axioms
X
mk 3 <<'X'
import RequestProject.Erdos287.SourceChain
-- the retired Ordering A must not reach the tail
example : Erdos287.SourceChain.scReachable .orderingA .conditionalTail = true := by decide
X
mk 4 <<'X'
import RequestProject.Erdos287.SourceChain
-- metadata must not feed a mathematical node
example : (Erdos287.SourceChain.SCNode.refereePending,
    Erdos287.SourceChain.SCNode.conditionalTail) ∈ Erdos287.SourceChain.scEdges := by decide
X
mk 5 <<'X'
import RequestProject.Erdos287.SourceChain
-- the conditional tail does not feed global #287 directly
example : (Erdos287.SourceChain.SCNode.conditionalTail,
    Erdos287.SourceChain.SCNode.globalErdos287) ∈ Erdos287.SourceChain.scEdges := by decide
X
mk 6 <<'X'
import RequestProject.Erdos287.SourceChain
-- the 391/256 ledger is not satisfied for sigma = 1/3
example : (391 / 256 : ℚ) * (1 / 3) < 1 / 4 := by norm_num
X
for i in 1 2 3 4 5 6; do
  if lake env lean "/tmp/sc_neg$i.lean" > "/tmp/sc_neg$i.log" 2>&1; then
    bad "negative control $i unexpectedly elaborated"
  else
    echo "negative control $i rejected (as expected)"
  fi
done

if [ $fail -eq 0 ]; then echo "AUDIT PASSED"; else echo "AUDIT FAILED"; exit 1; fi
