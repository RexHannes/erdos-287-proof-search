import Mathlib

/-!
# Erdős #287 — Research Bank V27 §8: exact `1/d` and the global conductor sum

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

**LEAN BANK.**
* `denominator_split` / `exact_one_over_d` — the actual denominator `q d u₁ v₁ u₂ v₂` equals
  `d · (q u₁ v₁ u₂ v₂)`, so the decorated sum carries the exact outside factor `1/d`;
* `fixed_lifted_scale_factor` — at FIXED lifted scale `Q = D Q₀` the common `1/Q` factors out;
* `global_aggregation` — (root-mass contract) + (per-state bound `√D · B`) + (divisor-sum bound)
  give `Σ_D Σ_b |Γ(D,b)| |P(D,b)| ≤ x^{3σ/2+ε} B`;
* `clean_energy_saving` — `η − 3σ/2 = 347/418000 > 0` for `η = 1/1100`, `σ = 1/19000`;
* `clean_discrepancy_saving` — after the final Cauchy: `(η − 3σ/2)/2 = 347/836000 > 0`.

**FINITE REGRESSION.**
* `fixing_Q0_alone_invalid` — with `Q₀` fixed but `D` varying, the lifted scales differ and no
  single denominator `D·Q₀` factors out of the sum.

**EXTERNAL PROVIDER** (never constructed):
* `DivisorSumProvider` — `Σ_{D ≤ x^σ} τ(D)^C √D ≤ x^{3σ/2 + ε}`.
-/

namespace Erdos287
namespace ResearchBankV27
namespace GlobalConductorSum

open Finset

/-- **Denominator split** (LEAN BANK). -/
theorem denominator_split (q d u1 v1 u2 v2 : ℚ) :
    q * d * u1 * v1 * u2 * v2 = d * (q * u1 * v1 * u2 * v2) := by ring

/-- **Exact outside factor `1/d`** (LEAN BANK). -/
theorem exact_one_over_d (X q d u1 v1 u2 v2 : ℚ) :
    X / (q * d * u1 * v1 * u2 * v2) = (1 / d) * (X / (q * u1 * v1 * u2 * v2)) := by
  rw [denominator_split, div_mul_div_comm, one_mul]

/-- **Fixed lifted scale** (LEAN BANK): with `Q = D Q₀` fixed, `1/Q` factors out. -/
theorem fixed_lifted_scale_factor {β : Type*} (s : Finset β) (X : β → ℚ) (D Q0 : ℚ) :
    ∑ b ∈ s, X b / (D * Q0) = (1 / (D * Q0)) * ∑ b ∈ s, X b := by
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring

/-- **Regression** (FINITE REGRESSION): fixing `Q₀ = 1` while `D ∈ {1, 2}` varies, the sum
`Σ_D 1/(D Q₀) = 3/2` is not `2/(D Q₀)` for any single lifted scale `D Q₀`. -/
theorem fixing_Q0_alone_invalid :
    ¬ ∃ D ∈ ({1, 2} : Finset ℚ), ∑ D' ∈ ({1, 2} : Finset ℚ), 1 / (D' * 1) = 2 / (D * 1) := by
  rintro ⟨D, hD, h⟩
  rw [Finset.sum_pair (by norm_num)] at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hD
  rcases hD with rfl | rfl <;> norm_num at h

/-- **Divisor-sum provider** (EXTERNAL PROVIDER; never constructed). -/
structure DivisorSumProvider (Ds : Finset ℕ) (C : ℕ) (x σ ε : ℝ) : Prop where
  bound : ∑ D ∈ Ds, ((Nat.divisors D).card : ℝ) ^ C * Real.sqrt D ≤ x ^ (3 * σ / 2 + ε)

/-- **Global aggregation** (LEAN CONDITIONAL on `DivisorSumProvider`; the root-mass contract and
the per-state bound are explicit hypotheses). -/
theorem global_aggregation {β : Type*} (Ds : Finset ℕ) (bs : ℕ → Finset β) (Γ P : ℕ → β → ℂ)
    (C : ℕ) {x σ ε B : ℝ} (hB : 0 ≤ B)
    (hroot : ∀ D ∈ Ds, ∑ b ∈ bs D, ‖Γ D b‖ ≤ ((Nat.divisors D).card : ℝ) ^ C)
    (hstate : ∀ D ∈ Ds, ∀ b ∈ bs D, ‖P D b‖ ≤ Real.sqrt D * B)
    (hdiv : DivisorSumProvider Ds C x σ ε) :
    ∑ D ∈ Ds, ∑ b ∈ bs D, ‖Γ D b‖ * ‖P D b‖ ≤ x ^ (3 * σ / 2 + ε) * B := by
  calc ∑ D ∈ Ds, ∑ b ∈ bs D, ‖Γ D b‖ * ‖P D b‖
      ≤ ∑ D ∈ Ds, (∑ b ∈ bs D, ‖Γ D b‖) * (Real.sqrt D * B) := by
        refine Finset.sum_le_sum fun D hD => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun b hb =>
          mul_le_mul_of_nonneg_left (hstate D hD b hb) (norm_nonneg _)
    _ ≤ ∑ D ∈ Ds, ((Nat.divisors D).card : ℝ) ^ C * (Real.sqrt D * B) :=
        Finset.sum_le_sum fun D hD =>
          mul_le_mul_of_nonneg_right (hroot D hD) (mul_nonneg (Real.sqrt_nonneg _) hB)
    _ = (∑ D ∈ Ds, ((Nat.divisors D).card : ℝ) ^ C * Real.sqrt D) * B := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun D _ => by ring
    _ ≤ x ^ (3 * σ / 2 + ε) * B := mul_le_mul_of_nonneg_right hdiv.bound hB

/-- The fixed exponents. -/
def eta : ℚ := 1 / 1100
def sigma : ℚ := 1 / 19000

/-- **Clean energy saving** (LEAN BANK). -/
theorem clean_energy_saving : eta - 3 * sigma / 2 = 347 / 418000 ∧ (0 : ℚ) < 347 / 418000 := by
  unfold eta sigma; norm_num

/-- **Clean discrepancy saving** (LEAN BANK). -/
theorem clean_discrepancy_saving :
    (eta - 3 * sigma / 2) / 2 = 347 / 836000 ∧ (0 : ℚ) < 347 / 836000 := by
  unfold eta sigma; norm_num

/-- Real-valued form of the global saving (LEAN BANK): with `B = N_q x^{−η}` and `ε` small,
`x^{3σ/2+ε} · x^{−η} = x^{−(347/418000) + ε}`. -/
theorem global_saving_rpow {x ε : ℝ} (hx : 0 < x) :
    x ^ (3 * ((1 : ℝ) / 19000) / 2 + ε) * x ^ (-((1 : ℝ) / 1100)) = x ^ (-(347 / 418000) + ε) := by
  rw [← Real.rpow_add hx]; congr 1; ring

end GlobalConductorSum
end ResearchBankV27
end Erdos287
