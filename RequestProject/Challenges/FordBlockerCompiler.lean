import Mathlib
import RequestProject.TrustedBank.Erdos287.TopLayerConsequences

/-!
# Challenge D — the Ford / prime-lower-bound compiler  (**specification only**)

**No Lean proof of a Ford–Maynard-type theorem is attempted or postulated here**, and
no axiom is introduced.  What this file contains is:

1. a *dependency specification* — the exact data an external prime-lower-bound theorem
   would have to deliver, written as a Lean predicate;
2. a *proved compiler theorem* — that this data, once delivered, refutes a gap-`≤2`
   Erdős #287 counterexample, using only the certified blocker bank.

The symmetric-Sophie sequence the specification refers to is

`a_m = W(m/X) · (Λ(2m-1) + Λ(2m+1)) / log X`,

with

* TYPE-I INPUT: equidistribution of `a_m` in arithmetic progressions to a positive level;
* TYPE-II INPUT: a bilinear (convolution) estimate at level `1/2 + 1/104`
  (see `Challenges.Gate1B`);
* MAIN TERM: the expected count `∑_m a_m` on the dyadic block;
* LOCAL DENSITY: the singular series of the pair, whose *local* factors are banked in
  `TrustedBank.SingularFactors` and whose optimality proxy is banked in
  `TrustedBank.CofactorIntensity`;
* SPARSE / FIXED-CERTIFICATE INPUT: for the fixed cofactor `j`, a prime power `q = r^e`
  with `r > C(2j)`;
* CONCLUSION REQUIRED FOR #287: a positive lower bound giving, in every sufficiently
  large dyadic interval, a prime `p ∈ (M/2, M]` with `p ∓ 1 = j·q`.

Since the published Ford-type theorem is not formalized in Lean, item (1) remains an
**external theorem dependency**, not a bank item.
-/

open scoped BigOperators

namespace Challenges
namespace FordCompiler

open Erdos287 TrustedBank.Erdos287Blockers

/-- **The blocker supply predicate** — exactly what an external prime-lower-bound
theorem has to deliver at scale `M` for the fixed cofactor `j`:

a prime `p` in the top interval `(M/2, M]`, and a prime power `q = r^e` with `r` above
the certified subset-numerator threshold `C(2j)`, such that `p = j·q + 1`
(or `p + 1 = j·q` in the companion form). -/
def BlockerSupplySub (M j : ℕ) : Prop :=
  ∃ p q r e : ℕ, p.Prime ∧ r.Prime ∧ 1 ≤ e ∧ 1 ≤ j ∧ q = r ^ e ∧ p = j * q + 1 ∧
    p ≤ M ∧ M < 2 * p ∧ M < q ^ 2 ∧ C (2 * j) < (r : ℤ)

/-- Companion form on the `p + 1` side. -/
def BlockerSupplyAdd (M j : ℕ) : Prop :=
  ∃ p q r e : ℕ, p.Prime ∧ r.Prime ∧ 1 ≤ e ∧ 1 ≤ j ∧ q = r ^ e ∧ p + 1 = j * q ∧
    p + 1 ≤ M ∧ M < 2 * p ∧ M < q ^ 2 ∧ C (2 * j) < (r : ℤ)

/-- **Proved compiler theorem (`p - 1` side).**  A supplied blocker at the scale `M` of
a gap-`≤2` counterexample refutes it, provided the supplied prime lies above the
smallest denominator `N` (a placement requirement that the external prime theorem must
also meet). -/
theorem no_Gap2CE_of_blockerSupplySub (ce : Gap2CE) {j : ℕ}
    (h : BlockerSupplySub ce.M j)
    (hplace : ∀ p : ℕ, p.Prime → p ≤ ce.M → ce.M < 2 * p → ce.N < p) : False := by
  obtain ⟨p, q, r, e, hp, hr, he, hj, hq, heq, hpM, hM2, hqsq, hthr⟩ := h
  exact Gap2CE.fixedCofactor_blocker_sub ce hp hr he hj hq heq
    (by have := hplace p hp hpM hM2; omega) hpM hM2 hqsq hthr

/-- **Proved compiler theorem (`p + 1` side).** -/
theorem no_Gap2CE_of_blockerSupplyAdd (ce : Gap2CE) {j : ℕ}
    (h : BlockerSupplyAdd ce.M j)
    (hplace : ∀ p : ℕ, p.Prime → p + 1 ≤ ce.M → ce.M < 2 * p → ce.N ≤ p) : False := by
  obtain ⟨p, q, r, e, hp, hr, he, hj, hq, heq, hpM, hM2, hqsq, hthr⟩ := h
  exact Gap2CE.fixedCofactor_blocker_add ce hp hr he hj hq heq
    (hplace p hp hpM hM2) hpM hM2 hqsq hthr

/-- **The external dependency, recorded as a statement (NOT proved).**  A Ford-type
theorem would assert that the blocker supply is available in every sufficiently large
dyadic block. -/
def FordSupply (j : ℕ) : Prop := ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → BlockerSupplySub M j

/-- **Proved.**  Granting the external supply *and* the placement requirement, every
sufficiently large gap-`≤2` counterexample is refuted.  This is the compiler, not a
proof of the supply. -/
theorem no_large_Gap2CE_of_FordSupply {j : ℕ} (h : FordSupply j)
    (hplace : ∀ ce : Gap2CE, ∀ p : ℕ, p.Prime → p ≤ ce.M → ce.M < 2 * p → ce.N < p) :
    ∃ M₀ : ℕ, ∀ ce : Gap2CE, M₀ ≤ ce.M → False := by
  obtain ⟨M₀, hM₀⟩ := h
  exact ⟨M₀, fun ce hce => no_Gap2CE_of_blockerSupplySub ce (hM₀ ce.M hce) (hplace ce)⟩

end FordCompiler
end Challenges
