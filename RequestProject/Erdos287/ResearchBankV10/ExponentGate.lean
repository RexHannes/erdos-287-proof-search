import RequestProject.Erdos287.ResearchBankV9.Gates

/-!
# Erdős #287 — Research Bank V10 §O (arithmetic): the exact exponent gate `> 78/145`

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Exact rational arithmetic (no floating point), with

  `θ₀ = 1/25000 + 1/625000000`,  `ε₀ = 1/100000`,  `ϑ = 7/13 − 3θ₀ − ε₀`.

* `theta0_lt` — `θ₀ < 1/1000`;
* `loss_lt` — `3θ₀ + ε₀ < 1/1885`;
* `vartheta_eq` — `ϑ = 4373943711 / 8125000000`;
* `vartheta_gt_gate` — `ϑ > 78/145` (the V9 gate `7/13 − 78/145 = 1/1885` is reused);
* `pair_coefficient_gap` — `145/39 − 2/ϑ = 52426455 / 18953756081 > 0`;
* `gate_pass_real` — the same pass transported to `ℝ` through the frozen V9 equivalence
  `Gates.gate_iff` (`2/θ < 145/39 ⟺ θ > 78/145`).

This is exponent arithmetic only; it certifies no analytic estimate.
-/

namespace Erdos287
namespace ResearchBankV10
namespace ExponentGate

/-- `θ₀ = 1/25000 + 1/625000000`. -/
def theta0 : ℚ := 1 / 25000 + 1 / 625000000

/-- `ε₀ = 1/100000`. -/
def eps0 : ℚ := 1 / 100000

/-- `ϑ = 7/13 − 3θ₀ − ε₀`. -/
def vartheta : ℚ := 7 / 13 - 3 * theta0 - eps0

theorem theta0_eq : theta0 = 25001 / 625000000 := by norm_num [theta0]

theorem theta0_pos : 0 < theta0 := by norm_num [theta0]

/-- `θ₀ < 1/1000`. -/
theorem theta0_lt : theta0 < 1 / 1000 := by norm_num [theta0]

theorem eps0_pos : 0 < eps0 := by norm_num [eps0]

theorem eps0_le : eps0 ≤ 1 / 1000 := by norm_num [eps0]

/-- `3θ₀ + ε₀ < 1/1885`. -/
theorem loss_lt : 3 * theta0 + eps0 < 1 / 1885 := by norm_num [theta0, eps0]

/-- `ϑ = 4373943711 / 8125000000`. -/
theorem vartheta_eq : vartheta = 4373943711 / 8125000000 := by
  norm_num [vartheta, theta0, eps0]

/-- **`ϑ > 78/145`**, via the frozen V9 margin `7/13 − 78/145 = 1/1885`. -/
theorem vartheta_gt_gate : 78 / 145 < vartheta := by
  have h := ResearchBankV9.Gates.gate_margin.1
  have := loss_lt
  unfold vartheta
  linarith

/-- **The exact pair-coefficient gap** `145/39 − 2/ϑ = 52426455 / 18953756081 > 0`. -/
theorem pair_coefficient_gap :
    145 / 39 - 2 / vartheta = 52426455 / 18953756081 ∧ (0 : ℚ) < 52426455 / 18953756081 := by
  rw [vartheta_eq]; constructor <;> norm_num

/-- The gate pass in `ℝ`, through the frozen V9 equivalence `gate_iff`. -/
theorem gate_pass_real : 2 / (vartheta : ℝ) < 145 / 39 := by
  have hpos : (0 : ℝ) < vartheta := by
    have := vartheta_gt_gate; exact_mod_cast (by linarith : (0 : ℚ) < vartheta)
  rw [ResearchBankV9.Gates.gate_iff hpos]
  have h : ((78 / 145 : ℚ) : ℝ) < (vartheta : ℝ) := by exact_mod_cast vartheta_gt_gate
  simpa using h

end ExponentGate
end ResearchBankV10
end Erdos287
