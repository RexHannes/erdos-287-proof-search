#!/usr/bin/env bash
# Erdős #287 post-V87 → V90R subtree: source / build / provider / axiom audit.
# Run from anywhere:  bash RequestProject/Erdos287/PostV87V90R/audit.sh
# Every check fails loudly (non-zero exit).
set -u
cd "$(dirname "$0")/../../.."
SUB=RequestProject/Erdos287/PostV87V90R
FILES="$SUB/*.lean RequestProject/Erdos287/PostV87V90R.lean"
fail=0
bad() { echo "FAIL: $*"; fail=1; }
strip() { perl -0pe 's{/-.*?-/}{}gs; s{--[^\n]*}{}g' "$1"; }

echo "== 1. forbidden tokens in code (comments/docstrings stripped)"
probe_code=$(printf 'theorem t : True := by\n  sorry\n' | perl -0pe 's{/-.*?-/}{}gs; s{--[^\n]*}{}g')
probe_cmt=$(printf '/- sorry -/\ntheorem t : True := trivial -- sorry\n' | perl -0pe 's{/-.*?-/}{}gs; s{--[^\n]*}{}g')
echo "$probe_code" | grep -Pq '\bsorry\b' || bad "scanner self-test: planted sorry not detected"
echo "$probe_cmt" | grep -Pq '\bsorry\b' && bad "scanner self-test: comment not stripped"
for f in $FILES; do
  code=$(strip "$f")
  for pat in '\bsorry\b' '\badmit\b' '^\s*axiom\b' '\bunsafe\b' '\bnative_decide\b' \
             '\bbv_decide\b' 'implemented_by' '\bopaque\b' '\bextern\b' 'ofReduceBool' \
             'Inhabited' 'False\.elim' '\bIsEmpty\b' 'Nonempty\s*\(\s*(WidthThreeMomentProvider|E287_11_4_Provider|NarrowWidthClosureProvider)'; do
    case "$f:$pat" in *AxiomAudit.lean:*IsEmpty*|*AxiomAudit.lean:*False*) continue;; esac
    if echo "$code" | grep -Pq "$pat"; then bad "$f matches $pat"; fi
  done
done

echo "== 2. obsolete 11/6 constant absent from all code except the regression fixture"
for f in $FILES; do
  case "$f" in *RegressionSuite.lean) continue;; esac
  if strip "$f" | grep -Pq '11\s*/\s*6'; then bad "$f uses the obsolete constant 11/6"; fi
done

echo "== 3. no provider is constructed in code (no anonymous-constructor / where-instance of a provider)"
for f in $FILES; do
  code=$(strip "$f")
  for p in WidthThreeMomentProvider E287_11_4_Provider NarrowWidthClosureProvider WindowMomentData AffineContactCompiler; do
    # a construction has the provider as its *result type*: `def x ... : <Provider> args :=`/`where`
    # (binder occurrences such as `(P : <Provider> s)` are excluded because `[^():\n]*` stops at `)`)
    re="^\\s*(noncomputable\\s+)?(def|instance|example|abbrev|theorem)\\b[^\\n]*:\\s*$p\\b[^():\\n]*(:=|where)"
    hits=$(echo "$code" | grep -P "$re" | grep -v "def E287_11_4 {s : ℝ} (P : E287_11_4_Provider s) : NarrowWidthClosureProvider s" || true)
    if [ -n "$hits" ]; then echo "$hits"; bad "$f constructs $p"; fi
  done
done

echo "== 4. historical files unchanged"
BASE=$(git rev-list --max-parents=0 HEAD | tail -1)
if ! git diff --quiet "$BASE" -- RequestProject/Erdos287/PostV64V71 RequestProject/Erdos287/PostV64V71.lean \
     RequestProject/Erdos287/PostV71V87 RequestProject/Erdos287/PostV71V87.lean ARISTOTLE_SUMMARY.md; then
  bad "historical files modified"
fi
changed=$(git diff --name-only "$BASE" -- . | grep -v "^$SUB/" \
  | grep -v "^RequestProject/Erdos287/PostV87V90R.lean$" \
  | grep -v "^ERDOS287_POSTV87_V90R_REPORT.md$" || true)
if [ -n "$changed" ]; then bad "files changed outside the new subtree: $changed"; fi

echo "== 5. narrow build (runs #assert_std_axioms_v90, #assert_(un)conditional, #audit_providers_v90)"
if ! lake build RequestProject.Erdos287.PostV87V90R > /tmp/pv90_build.log 2>&1; then
  tail -30 /tmp/pv90_build.log; bad "narrow build failed"
fi
grep -q "provider audit passed" /tmp/pv90_build.log || \
  grep -q "Replayed RequestProject.Erdos287.PostV87V90R.AxiomAudit" /tmp/pv90_build.log || \
  grep -q "Built RequestProject.Erdos287.PostV87V90R" /tmp/pv90_build.log || bad "audit module not built"

echo "== 6. negative controls (each must FAIL to elaborate)"
mk() { cat > "/tmp/pv90_neg$1.lean"; }
mk 1 <<'X'
import RequestProject.Erdos287.PostV87V90R.AxiomAudit
theorem bad_sorry : 1 = 2 := by sorry
#assert_std_axioms_v90 bad_sorry
X
mk 2 <<'X'
import RequestProject.Erdos287.PostV87V90R.AxiomAudit
theorem bad_native : 10 < 20 := by native_decide
#assert_std_axioms_v90 bad_native
X
mk 3 <<'X'
import RequestProject.Erdos287.PostV87V90R.AxiomAudit
namespace Erdos287.PostV87V90R
def fakeNarrow (h : False) : NarrowWidthClosureProvider 4 := h.elim
end Erdos287.PostV87V90R
#audit_providers_v90
X
mk 4 <<'X'
import RequestProject.Erdos287.PostV87V90R.AxiomAudit
namespace Erdos287.PostV87V90R
def fakeNarrow2 [IsEmpty Erdos287.PostV71V87.ExactWord] : NarrowWidthClosureProvider 4 :=
  ⟨by norm_num, 0, fun W _ => IsEmpty.false W⟩
end Erdos287.PostV87V90R
#audit_providers_v90
X
mk 5 <<'X'
import RequestProject.Erdos287.PostV87V90R.AxiomAudit
namespace Erdos287.PostV87V90R
def emptyCompiler : AffineContactCompiler 11 3 0 where
  slope := fun _ i => i.elim0
  slope_pos := fun _ i => i.elim0
  edge_ne := fun _ _ i => i.elim0
  edge_gcd := fun _ _ i => i.elim0
  ratio := 0
  scale_ratio := fun _ i => i.elim0
end Erdos287.PostV87V90R
#audit_providers_v90
X
mk 6 <<'X'
import RequestProject.Erdos287.PostV87V90R.AxiomAudit
namespace Erdos287.PostV87V90R
theorem overstated (W : Erdos287.PostV71V87.ExactWord) (P : WidthThreeMomentProvider 4) :
    1 < W.a → P.onset ≤ W.M → (4 : ℝ) * W.a ≤ W.M → False := W3_of_provider P W
end Erdos287.PostV87V90R
#assert_unconditional Erdos287.PostV87V90R.overstated
X
mk 7 <<'X'
import RequestProject.Erdos287.PostV87V90R.AxiomAudit
namespace Erdos287.PostV87V90R
theorem bad_trivial_provider : Nonempty (WidthThreeMomentProvider 4) := by
  exact ⟨by trivial⟩
end Erdos287.PostV87V90R
X
# expected rejection reason for each control (so a control cannot "pass" by an unrelated error)
expect=( "" "non-standard axiom sorryAx" "non-standard axiom Lean.ofReduceBool" \
  "provider constructed" "provider constructed" "provider constructed" \
  "labelled unconditional" "error" )
for n in 1 2 3 4 5 6 7; do
  if lake env lean /tmp/pv90_neg$n.lean > /tmp/pv90_neg$n.log 2>&1; then
    bad "negative control $n unexpectedly elaborated"
  elif ! grep -q "${expect[$n]}" /tmp/pv90_neg$n.log; then
    cat /tmp/pv90_neg$n.log | head -5; bad "negative control $n rejected for an unexpected reason"
  else
    echo "  negative control $n rejected: $(grep -m1 -E 'error' /tmp/pv90_neg$n.log | cut -c1-160)"
  fi
done

if [ $fail -ne 0 ]; then echo "AUDIT FAILED"; exit 1; fi
echo "AUDIT PASSED"
