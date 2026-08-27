import Mathlib
import RequestProject.Challenges.Delta6Interfaces
import RequestProject.TrustedBank.Erdos287.GoodPrime
import RequestProject.Erdos287.V2SophieFinite

/-!
# Erdős #287 — the *placed* log-cofactor supply predicate (append-only repair)

## Why this file exists

The historical abstract supply predicate `Challenges.Delta6.LCBeta M J`
(`RequestProject/Challenges/Delta6Interfaces.lean`) records the upper placement
`x + 1 ≤ M` of the adjacent pair `x, x+1`, but it records **no lower placement**: nothing
in it implies `N ≤ x` for the minimum denominator `N` of a hypothetical gap-`≤2`
counterexample.  Since the banked finite blocker
`TrustedBank.Erdos287Good.Gap2CE.logCofactor_finite_blocker` *requires* `ce.N ≤ x`
(it is the hypothesis `hxN`), `LCBeta` alone cannot be compiled into the blocker.

A second, independent gap: `LCBeta` also omits the numerator threshold
`C (2J) < qᵢ`, which the finite blocker likewise requires.

**Nothing historical is mutated.**  `LCBeta` is left exactly as it was; this file adds a
strictly stronger predicate `PlacedLCBeta` (equivalently `UpperHalfLCBeta`) together with

* `Erdos287.Gap2CE.N_le_of_M_le_two_mul` — the placement lemma
  `ce.M ≤ 2 * x → ce.N ≤ x`, derived from the banked half-range theorem
  `Erdos287.Gap2CE.halfRange_min_le` (`N ≤ ⌊M/2⌋`);
* `Erdos287.Gap2CE.no_of_placedLCBeta` — the append-only compiler from the repaired
  predicate to the existing finite blocker;
* `Erdos287.placedLCBeta_imp_LCBeta` — the repaired predicate is genuinely stronger:
  it implies the historical one.

Erdős #287 remains **OPEN**: `PlacedLCBeta M J` is *not* proved for any `M`; it is an
arithmetic supply statement, exactly as `LCBeta` was.
-/

open scoped BigOperators

namespace Erdos287

/-- **Placed log-cofactor supply (repaired, append-only).**

Same shape as `Challenges.Delta6.LCBeta M J`, with the two missing fields restored:

* the *lower placement* `M ≤ 2 * x` (so `x` lies in the upper half of the window, which
  by `halfRange_min_le` forces `N ≤ x`);
* the *numerator threshold* `C (2J) < qᵢ` required by the banked finite blocker. -/
def PlacedLCBeta (M J : ℕ) : Prop :=
  ∃ x : ℕ, ∃ q₀ q₁ : ℕ, q₀.Prime ∧ q₁.Prime ∧
    M ≤ 2 * J * q₀ ∧ M ≤ 2 * J * q₁ ∧ M < q₀ ^ 2 ∧ M < q₁ ^ 2 ∧
    C (2 * J) < (q₀ : ℤ) ∧ C (2 * J) < (q₁ : ℤ) ∧
    q₀ ∣ x ∧ q₁ ∣ (x + 1) ∧ M ≤ 2 * x ∧ x + 1 ≤ M

/-- Alias with the alternative name suggested for the repair. -/
def UpperHalfLCBeta (M J : ℕ) : Prop := PlacedLCBeta M J

theorem upperHalfLCBeta_iff (M J : ℕ) : UpperHalfLCBeta M J ↔ PlacedLCBeta M J := Iff.rfl

/-- The repaired predicate implies the historical one: no statement is weakened. -/
theorem placedLCBeta_imp_LCBeta {M J : ℕ} (h : PlacedLCBeta M J) :
    Challenges.Delta6.LCBeta M J := by
  obtain ⟨x, q₀, q₁, hq0, hq1, hl0, hl1, hs0, hs1, _, _, hd0, hd1, _, hxM⟩ := h
  exact ⟨x, q₀, q₁, hq0, hq1, hl0, hl1, hs0, hs1, hd0, hd1, hxM⟩

/-- The lower placement is *not* recoverable from the historical predicate: `LCBeta`
is satisfiable with `x` strictly below `M/2`, as witnessed here at `M = 30`, `J = 3`,
`x = 13` (`2x = 26 < 30 = M`).  Hence `LCBeta` cannot imply `N ≤ x`. -/
theorem lcBeta_witness_below_half : Challenges.Delta6.LCBeta 30 3 :=
  ⟨13, 13, 7, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, ⟨1, rfl⟩, ⟨2, rfl⟩, by norm_num⟩

namespace Gap2CE

variable (ce : Gap2CE)

/-- **Placement lemma.**  For a gap-`≤2` counterexample, any `x` with `M ≤ 2x` satisfies
`N ≤ x`.  Proof: the banked `halfRange_min_le` gives `N ≤ ⌊M/2⌋`, and `M ≤ 2x` gives
`⌊M/2⌋ ≤ x`.

The hypothesis `2 ≤ ce.M` is the one carried by the banked half-range theorem (it is
necessary there: `A = {1}` inhabits `Gap2CE` with `N = 1 > 0 = ⌊M/2⌋`). -/
theorem N_le_of_M_le_two_mul {x : ℕ} (hM : 2 ≤ ce.M) (h : ce.M ≤ 2 * x) : ce.N ≤ x := by
  have h1 : ce.N ≤ ce.M / 2 := ce.halfRange_min_le hM
  have h2 : ce.M / 2 ≤ (2 * x) / 2 := Nat.div_le_div_right h
  rw [Nat.mul_div_cancel_left x (by norm_num : 0 < 2)] at h2
  omega

/-- **Append-only compiler.**  The repaired supply predicate at the scale `M` of a
gap-`≤2` counterexample refutes it, via the banked finite blocker
`logCofactor_finite_blocker`.

No extra hypothesis on `ce.M` is needed: the predicate itself forces `2 ≤ M`
(`x + 1 ≤ M` and `M ≤ 2x` give `x ≥ 1`). -/
theorem no_of_placedLCBeta {J : ℕ} (h : PlacedLCBeta ce.M J) : False := by
  obtain ⟨x, q₀, q₁, hq0, hq1, hl0, hl1, hs0, hs1, hC0, hC1, hd0, hd1, hhalf, hxM⟩ := h
  have hx1 : 1 ≤ x := by omega
  have hM2 : 2 ≤ ce.M := by omega
  exact TrustedBank.Erdos287Good.Gap2CE.logCofactor_finite_blocker ce
    (ce.N_le_of_M_le_two_mul hM2 hhalf) hxM hq0 hq1 hl0 hl1 hs0 hs1 hC0 hC1 hd0 hd1

/-- The same compiler in contrapositive form. -/
theorem not_placedLCBeta_of_counterexample {J : ℕ} : ¬ PlacedLCBeta ce.M J :=
  fun h => ce.no_of_placedLCBeta h

end Gap2CE

end Erdos287
