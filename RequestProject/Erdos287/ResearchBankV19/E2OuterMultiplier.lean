import Mathlib

/-!
# Erdős #287 — Research Bank V19 §6: E2 outer-multiplier scope theorem

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Abstract Cauchy stage: outer variables `o = (f, n₁, n₂, r₁, r₂, s₂)` (any finite type), inner
variables `i = (s₁, h)` (any finite type).

Kernel-proved (LEAN BANK, scope theorems):
* **`cauchy_outer_absorb`** — a one-bounded outer coefficient `U(o)`, independent of the inner
  variables, is absorbed without changing the inner estimate:
  `∑_o ‖∑_i U(o) c(o,i)‖² ≤ ∑_o ‖∑_i c(o,i)‖²`;
* **`h_multiplier_absorb`** — an independent one-bounded `h`-multiplier is absorbed by any inner
  estimate that is stable under one-bounded `h`-coefficients (grouped coefficient argument).

FINITE REGRESSION / scope limits (arbitrary joint `q/h` dependence is NOT covered):
* `joint_dependence_not_covered` — a multiplier depending on the inner summation variable can
  turn a vanishing sum into a sum of size `2`;
* `inner_dependent_outer_fails` — an "outer" multiplier that secretly depends on the inner
  variable violates the Cauchy-stage inequality.
-/

namespace Erdos287
namespace ResearchBankV19
namespace E2OuterMultiplier

/-- **Absorbing a one-bounded outer coefficient at the Cauchy stage.** -/
theorem cauchy_outer_absorb {O ι : Type*} [Fintype O] [Fintype ι] (U : O → ℂ)
    (hU : ∀ o, ‖U o‖ ≤ 1) (c : O → ι → ℂ) :
    ∑ o, ‖∑ i, U o * c o i‖ ^ 2 ≤ ∑ o, ‖∑ i, c o i‖ ^ 2 := by
  refine Finset.sum_le_sum fun o _ => ?_
  rw [← Finset.mul_sum, norm_mul, mul_pow]
  have h1 : ‖U o‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hU o)
  have h2 : 0 ≤ ‖∑ i, c o i‖ ^ 2 := by positivity
  nlinarith

/-- Equality when the outer coefficient is unimodular. -/
theorem cauchy_outer_unimodular {O ι : Type*} [Fintype O] [Fintype ι] (U : O → ℂ)
    (hU : ∀ o, ‖U o‖ = 1) (c : O → ι → ℂ) :
    ∑ o, ‖∑ i, U o * c o i‖ ^ 2 = ∑ o, ‖∑ i, c o i‖ ^ 2 := by
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [← Finset.mul_sum, norm_mul, hU, one_mul]

/-- **Absorbing an independent one-bounded `h`-multiplier.** -/
theorem h_multiplier_absorb {H : Type*} [Fintype H] (X : H → ℂ) {B : ℝ}
    (hstable : ∀ β : H → ℂ, (∀ h, ‖β h‖ ≤ 1) → ‖∑ h, β h * X h‖ ≤ B)
    (γ β : H → ℂ) (hγ : ∀ h, ‖γ h‖ ≤ 1) (hβ : ∀ h, ‖β h‖ ≤ 1) :
    ‖∑ h, γ h * β h * X h‖ ≤ B :=
  hstable (fun h => γ h * β h) fun h => by
    rw [norm_mul]; exact mul_le_one₀ (hγ h) (norm_nonneg _) (hβ h)

/-- **Joint dependence is not covered.** -/
theorem joint_dependence_not_covered :
    ∃ (X U : Fin 2 → ℂ), (∀ h, ‖U h‖ ≤ 1) ∧ ‖∑ h, X h‖ = 0 ∧ ‖∑ h, U h * X h‖ = 2 := by
  refine ⟨![1, -1], ![1, -1], fun h => ?_, ?_, ?_⟩
  · fin_cases h <;> simp
  · simp [Fin.sum_univ_two]
  · simp [Fin.sum_univ_two]; norm_num

/-- **An inner-dependent "outer" multiplier breaks the Cauchy-stage inequality.** -/
theorem inner_dependent_outer_fails :
    ∃ (U c : Unit → Fin 2 → ℂ), (∀ o i, ‖U o i‖ ≤ 1) ∧
      ¬ (∑ o, ‖∑ i, U o i * c o i‖ ^ 2 ≤ ∑ o, ‖∑ i, c o i‖ ^ 2) := by
  refine ⟨fun _ => ![1, -1], fun _ => ![1, -1], fun o i => ?_, ?_⟩
  · fin_cases i <;> simp
  · simp [Fin.sum_univ_two]

end E2OuterMultiplier
end ResearchBankV19
end Erdos287
