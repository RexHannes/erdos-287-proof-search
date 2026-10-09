#!/usr/bin/env bash
# Erdős #287 — CurrentTail subtree: token / firewall / build / checker / negative-control audit.
# Run from anywhere:  bash RequestProject/Erdos287/CurrentTail/audit.sh
# Every check fails loudly (non-zero exit).  ERDŐS #287 REMAINS OPEN.  TAIL-287 NOT BANKED.
set -u
cd "$(dirname "$0")/../../.."
SUB=RequestProject/Erdos287/CurrentTail
FILES="$SUB/*.lean RequestProject/Erdos287/CurrentTail.lean"
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
             'False\.elim' '^\s*instance\b'; do
    if echo "$code" | grep -Pq "$pat"; then bad "$f matches $pat"; fi
  done
done

echo "== 2. no unconditional tail theorem and no alias of the conditional one"
for f in $FILES; do
  code=$(strip "$f")
  if echo "$code" | grep -Pq '^\s*(theorem|def|abbrev|lemma)\s+\S*Unconditional'; then
    bad "$f declares an 'Unconditional' tail object"
  fi
  if echo "$code" | grep -Pq ':=\s*Tail287_of_AnalyticProviders\s*$'; then
    bad "$f aliases the conditional tail theorem"
  fi
done

echo "== 3. W3 / W2.984 / historical subtrees and ARISTOTLE_SUMMARY.md unchanged"
BASE=$(git rev-list --max-parents=0 HEAD | tail -1)
if ! git diff --quiet "$BASE" -- RequestProject/Erdos287/W3Publication RequestProject/Erdos287/W3Publication.lean \
     RequestProject/Erdos287/W2984Publication RequestProject/Erdos287/W2984Publication.lean \
     RequestProject/Erdos287/PostV87V90R RequestProject/Erdos287/PostV87V90R.lean \
     RequestProject/Erdos287/PostV71V87 ARISTOTLE_SUMMARY.md; then
  bad "protected files modified"
fi

echo "== 4. narrow build (runs #ct_audit_providers, firewall asserts, axiom asserts)"
if ! lake build RequestProject.Erdos287.CurrentTail > /tmp/ct_build.log 2>&1; then
  tail -30 /tmp/ct_build.log; bad "narrow build failed"
fi
if grep -q "declaration uses 'sorry'" /tmp/ct_build.log; then bad "build reports sorry"; fi

echo "== 5. fresh kernel re-check with the installed checker"
CHK=""
for c in leanchecker lean4checker; do
  if lake env which "$c" > /dev/null 2>&1; then CHK=$c; break; fi
done
if [ -z "$CHK" ]; then bad "no kernel checker found"; else
  echo "checker: $CHK"
  if ! lake env "$CHK" --fresh RequestProject.Erdos287.CurrentTail > /tmp/ct_check.log 2>&1; then
    tail -20 /tmp/ct_check.log; bad "$CHK --fresh failed"
  fi
fi

echo "== 6. negative controls (each must FAIL to elaborate)"
mk() { cat > "/tmp/ct_neg$1.lean"; }
mk 1 <<'X'
import RequestProject.Erdos287.CurrentTail
theorem bad_sorry : 1 = 2 := by sorry
#ct_assert_std_axioms bad_sorry
X
mk 2 <<'X'
import RequestProject.Erdos287.CurrentTail
theorem bad_native : 10 < 20 := by native_decide
#ct_assert_std_axioms bad_native
X
mk 3 <<'X'
import RequestProject.Erdos287.CurrentTail
namespace Erdos287.CurrentTail
theorem fakeE1 (h : False) : MaynardE1Estimate 0 0 0 0 0 0 0 := h.elim
end Erdos287.CurrentTail
#ct_audit_providers
X
mk 4 <<'X'
import RequestProject.Erdos287.CurrentTail
namespace Erdos287.CurrentTail
theorem fakeTail : Tail287Statement := by exact?
end Erdos287.CurrentTail
X
mk 5 <<'X'
import RequestProject.Erdos287.CurrentTail
-- the retired Ordering A must not feed anything
example : (Erdos287.CurrentTail.Node.orderingA, Erdos287.CurrentTail.Node.asymptoticTail) ∈
    Erdos287.CurrentTail.edges := by decide
X
mk 6 <<'X'
import RequestProject.Erdos287.CurrentTail
-- the tail does not feed global #287 directly
example : (Erdos287.CurrentTail.Node.asymptoticTail, Erdos287.CurrentTail.Node.globalErdos287) ∈
    Erdos287.CurrentTail.edges := by decide
X
for i in 1 2 3 4 5 6; do
  if lake env lean "/tmp/ct_neg$i.lean" > "/tmp/ct_neg$i.log" 2>&1; then
    bad "negative control $i unexpectedly elaborated"
  else
    echo "negative control $i rejected (as expected)"
  fi
done

if [ $fail -eq 0 ]; then echo "AUDIT PASSED"; else echo "AUDIT FAILED"; exit 1; fi
