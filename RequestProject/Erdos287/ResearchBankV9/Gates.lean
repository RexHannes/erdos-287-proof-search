import RequestProject.Erdos287.ResearchBankV9.CircularGraph
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Erdős #287 — Research Bank V9 §3E: the exact gates

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Machine-checked exact arithmetic:

* `gate_13_3` — `G(13, 3)`: `α = 4` and `χ_f = 13/4` (certificate form);
* `gate_145_38` — `G(145, 38)`: `α = 39` and `χ_f = 145/39`;
* `gate_ineq` — `26/7 < 145/39`;
* `gate_margin` — `7/13 − 78/145 = 1/1885 > 0`;
* `gate_iff` — for `θ > 0`: `2/θ < 145/39 ⟺ θ > 78/145`;
* `localization_constant` — the rational localization constant `c = 39/106` satisfies
  `c > 1/e`, via Mathlib's proved bound `e > 2.7182818283` (no new axiom); equivalently
  `ρ = 106/39 < e`, and `145/39 = ρ + 1`.
-/

namespace Erdos287
namespace ResearchBankV9
namespace Gates

open CircularGraph

/-- `α(G(n, r)) = r + 1` in certificate form (for `n > 3r`). -/
def AlphaEq (n r : ℤ) : Prop :=
  (∃ S : Finset ℤ, Indep n r S ∧ (S.card : ℤ) = r + 1) ∧
    ∀ S : Finset ℤ, Indep n r S → (S.card : ℤ) ≤ r + 1

/-- `χ_f(G(n, r)) = v` in certificate form. -/
def ChiFEq (n r : ℤ) (v : ℚ) : Prop :=
  (∃ c : FracColouring n r, c.value = v) ∧ ∀ c : FracColouring n r, v ≤ c.value

theorem alphaEq_of {n r : ℤ} (hr : 0 ≤ r) (hn : 3 * r < n) : AlphaEq n r :=
  ⟨⟨arc0 r, (arc_indep hr (by linarith)).1, (arc_indep hr (by linarith)).2⟩,
   fun _ hS => indep_card_le hr hn hS⟩

/-- **`G(13, 3)`: `α = 4`, `χ_f = 13/4`.** -/
theorem gate_13_3 : AlphaEq 13 3 ∧ ChiFEq 13 3 (13 / 4) := by
  refine ⟨alphaEq_of (by norm_num) (by norm_num), ?_⟩
  have := fractional_chromatic_eq (n := 13) (r := 3) (by norm_num) (by norm_num)
  norm_num at this
  exact this

/-- **`G(145, 38)`: `α = 39`, `χ_f = 145/39`.** -/
theorem gate_145_38 : AlphaEq 145 38 ∧ ChiFEq 145 38 (145 / 39) := by
  refine ⟨alphaEq_of (by norm_num) (by norm_num), ?_⟩
  have := fractional_chromatic_eq (n := 145) (r := 38) (by norm_num) (by norm_num)
  norm_num at this
  exact this

/-- `26/7 < 145/39`. -/
theorem gate_ineq : (26 : ℚ) / 7 < 145 / 39 := by norm_num

/-- `7/13 − 78/145 = 1/1885 > 0`. -/
theorem gate_margin : (7 : ℚ) / 13 - 78 / 145 = 1 / 1885 ∧ (0 : ℚ) < 1 / 1885 := by
  constructor <;> norm_num

/-- **The gate equivalence**: for `θ > 0`, `2/θ < 145/39 ⟺ θ > 78/145`. -/
theorem gate_iff {θ : ℝ} (hθ : 0 < θ) : 2 / θ < 145 / 39 ↔ 78 / 145 < θ := by
  rw [div_lt_iff₀ hθ]
  constructor <;> intro h <;> linarith

/-- The architecture parameter `ρ = 106/39` and the gate `145/39 = ρ + 1`. -/
theorem gate_eq_rho_add_one : (145 : ℚ) / 39 = 106 / 39 + 1 := by norm_num

/-- **The rational localization constant `c = 39/106` exceeds `1/e`** (equivalently
`106/39 < e`), using only Mathlib's proved decimal bound on `e`. -/
theorem localization_constant :
    (106 : ℝ) / 39 < Real.exp 1 ∧ 1 / Real.exp 1 < 39 / 106 := by
  have he := Real.exp_one_gt_d9
  have hpos := Real.exp_pos 1
  constructor
  · linarith [show (106 : ℝ) / 39 < 2.7182818283 by norm_num]
  · rw [div_lt_div_iff₀ hpos (by norm_num)]
    linarith [show (106 : ℝ) / 39 < 2.7182818283 by norm_num]

/-- Arithmetic metadata: the chosen gate sits just below the architecture limit `e + 1`:
`0 < (e + 1) − 145/39 < 1/2000`.  (Metadata only; not a closure theorem.) -/
theorem gate_near_architecture_limit :
    0 < Real.exp 1 + 1 - 145 / 39 ∧ Real.exp 1 + 1 - 145 / 39 < 1 / 2000 := by
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.exp_one_lt_d9
  constructor
  · linarith [show (145 : ℝ) / 39 < 3.7182818283 by norm_num]
  · linarith [show (3.7182818286 : ℝ) - 145 / 39 < 1 / 2000 by norm_num]

end Gates
end ResearchBankV9
end Erdos287
