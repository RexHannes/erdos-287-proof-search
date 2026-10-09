#!/usr/bin/env bash
# Erdős #287 post-V71 → V87 bank: source / build / provider audit.
# Run from the project root:  bash RequestProject/Erdos287/PostV71V87/audit.sh
# Every check fails loudly (non-zero exit) — no reliance on Python `assert`.
set -u
cd "$(dirname "$0")/../../.."
SUB=RequestProject/Erdos287/PostV71V87
FILES="$SUB/*.lean RequestProject/Erdos287/PostV71V87.lean"
fail=0
bad() { echo "FAIL: $*"; fail=1; }

echo "== 1. forbidden tokens in code (comments/docstrings stripped)"
# self-test of the scanner: a planted `sorry` in code must be detected, one in a comment not
probe_code=$(printf 'theorem t : True := by\n  sorry\n' | perl -0pe 's{/-.*?-/}{}gs; s{--[^\n]*}{}g')
probe_cmt=$(printf '/- sorry -/\ntheorem t : True := trivial -- sorry\n' | perl -0pe 's{/-.*?-/}{}gs; s{--[^\n]*}{}g')
echo "$probe_code" | grep -Pq '\bsorry\b' || bad "scanner self-test: planted sorry not detected"
echo "$probe_cmt" | grep -Pq '\bsorry\b' && bad "scanner self-test: comment not stripped"
for f in $FILES; do
  # strip block comments /- ... -/ and line comments -- ...
  code=$(perl -0pe 's{/-.*?-/}{}gs; s{--[^\n]*}{}g' "$f")
  for pat in '\bsorry\b' '\badmit\b' '^\s*axiom\b' '\bunsafe\b' '\bnative_decide\b' \
             'implemented_by' '\bopaque\b' '\bextern\b' 'ofReduceBool' 'Inhabited' \
             'Nonempty\s*\(\s*(Proximity287|CrossScaleSynchronization287)'; do
    if echo "$code" | grep -Pq "$pat"; then bad "$f matches $pat"; fi
  done
done

echo "== 2. historical subtree unchanged"
BASE=$(git rev-list --max-parents=0 HEAD | tail -1)
if ! git diff --quiet "$BASE" -- RequestProject/Erdos287/PostV64V71 RequestProject/Erdos287/PostV64V71.lean ARISTOTLE_SUMMARY.md; then
  bad "historical files modified"
fi
changed=$(git diff --name-only "$BASE" -- . | grep -v "^$SUB/" \
  | grep -v "^RequestProject/Erdos287/PostV71V87.lean$" \
  | grep -v "^ERDOS287_POSTV71_V87_REPORT.md$" || true)
if [ -n "$changed" ]; then bad "files changed outside the new subtree: $changed"; fi

echo "== 3. narrow build (includes #assert_std_axioms and #audit_providers)"
if ! lake build RequestProject.Erdos287.PostV71V87 > /tmp/pv87_build.log 2>&1; then
  tail -20 /tmp/pv87_build.log; bad "narrow build failed"
fi

echo "== 4. negative controls (each must FAIL to elaborate)"
cat > /tmp/pv87_neg1.lean <<'EOF'
import RequestProject.Erdos287.PostV71V87.AxiomAudit
theorem bad_sorry : 1 = 2 := by sorry
#assert_std_axioms bad_sorry
EOF
cat > /tmp/pv87_neg2.lean <<'EOF'
import RequestProject.Erdos287.PostV71V87.AxiomAudit
theorem bad_native : 10 < 20 := by native_decide
#assert_std_axioms bad_native
EOF
cat > /tmp/pv87_neg3.lean <<'EOF'
import RequestProject.Erdos287.PostV71V87.AxiomAudit
namespace Erdos287.PostV71V87
theorem fake_provider : FiniteExclusionBelow 0 := fun _ _ hlt => absurd hlt (Nat.not_lt_zero _)
end Erdos287.PostV71V87
#audit_providers
EOF
for n in 1 2 3; do
  if lake env lean /tmp/pv87_neg$n.lean > /tmp/pv87_neg$n.log 2>&1; then
    bad "negative control $n unexpectedly elaborated"
  else
    echo "  negative control $n rejected: $(grep -m1 error /tmp/pv87_neg$n.log)"
  fi
done

if [ $fail -ne 0 ]; then echo "AUDIT FAILED"; exit 1; fi
echo "AUDIT PASSED"
