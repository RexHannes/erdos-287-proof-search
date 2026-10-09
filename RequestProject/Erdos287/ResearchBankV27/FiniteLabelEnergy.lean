import RequestProject.Erdos287.ResearchBankV27.CommonCauchy

/-!
# Erdős #287 — Research Bank V27 §6.1–6.2: finite-label energy grouping

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Inner coefficients may carry a label `κ(o) ∈ J` depending on the OUTER variable only:
`X_κ(o) = Σ_i Ψ_{κ(o)}(i) K(o; i)`.  Each `Ψ_j` is an arbitrary inner coefficient (it is a
function of the inner variable only, hence cannot see the final Kloosterman variables).

**LEAN BANK.**
* `label_energy_le` — `Σ_o |X_{κ(o)}(o)|² ≤ Σ_j Σ_o |X_j(o)|²` (positivity / range enlargement;
  NO orthogonality is assumed — the `Ψ_j` are completely arbitrary);
* `labelled_cauchy` — `|W_κ|² ≤ mass · Σ_j V(Ψ_j)`;
* `labelled_sqrt_cost` — if every single label satisfies `mass · V(Ψ_j) ≤ B²`, then
  `|W_κ| ≤ √L · B`: the labels cost `√L` on the linear sum (`L` at energy level only).

**FINITE REGRESSION.**
* `label_energy_not_le_max` — the labelled energy can exceed `max_j V(Ψ_j)`: the factor `L` at
  energy level is genuinely needed (so the linear cost is `√L`, not `1`).
-/

namespace Erdos287
namespace ResearchBankV27
namespace FiniteLabelEnergy

open Finset CommonCauchy

variable {O I J : Type*} [Fintype O] [Fintype I] [Fintype J]

/-- The labelled inner sum `X_{κ(o)}(o)`. -/
noncomputable def labelInner (K : O → I → ℂ) (Ψ : J → I → ℂ) (κ : O → J) (o : O) : ℂ :=
  innerSum K (Ψ (κ o)) o

/-- The labelled energy `Σ_o |X_{κ(o)}(o)|²`. -/
noncomputable def labelEnergy (K : O → I → ℂ) (Ψ : J → I → ℂ) (κ : O → J) : ℝ :=
  ∑ o, ‖labelInner K Ψ κ o‖ ^ 2

/-- The labelled decorated sum `W_κ = Σ_o A(o) X_{κ(o)}(o)`. -/
noncomputable def labelSum (A : O → ℂ) (K : O → I → ℂ) (Ψ : J → I → ℂ) (κ : O → J) : ℂ :=
  ∑ o, A o * labelInner K Ψ κ o

/-- **Energy label grouping** (LEAN BANK; positivity only, no orthogonality). -/
theorem label_energy_le (K : O → I → ℂ) (Ψ : J → I → ℂ) (κ : O → J) :
    labelEnergy K Ψ κ ≤ ∑ j, energy K (Ψ j) := by
  unfold labelEnergy energy
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun o _ => ?_
  exact Finset.single_le_sum (f := fun j => ‖innerSum K (Ψ j) o‖ ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ (κ o))

/-- **Labelled Cauchy** (LEAN BANK): `|W_κ|² ≤ mass · Σ_j V(Ψ_j)`. -/
theorem labelled_cauchy (A : O → ℂ) (w : O → ℝ) (hA : ∀ o, ‖A o‖ ^ 2 ≤ w o) (K : O → I → ℂ)
    (Ψ : J → I → ℂ) (κ : O → J) :
    ‖labelSum A K Ψ κ‖ ^ 2 ≤ (∑ o, w o) * ∑ j, energy K (Ψ j) := by
  have h := common_cauchy univ A (labelInner K Ψ κ) w fun o _ => hA o
  have hw : 0 ≤ ∑ o, w o := Finset.sum_nonneg fun o _ => (sq_nonneg _).trans (hA o)
  exact h.trans (mul_le_mul_of_nonneg_left (label_energy_le K Ψ κ) hw)

/-- **`√L` label cost** (LEAN BANK): single-label decorated estimates `mass · V(Ψ_j) ≤ B²`
give `|W_κ| ≤ √L · B` with `L = #J`. -/
theorem labelled_sqrt_cost (A : O → ℂ) (w : O → ℝ) (hA : ∀ o, ‖A o‖ ^ 2 ≤ w o)
    (K : O → I → ℂ) (Ψ : J → I → ℂ) (κ : O → J) {B : ℝ} (hB : 0 ≤ B)
    (hsingle : ∀ j, (∑ o, w o) * energy K (Ψ j) ≤ B ^ 2) :
    ‖labelSum A K Ψ κ‖ ≤ Real.sqrt (Fintype.card J) * B := by
  have h := labelled_cauchy A w hA K Ψ κ
  have hsum : (∑ o, w o) * ∑ j, energy K (Ψ j) ≤ (Fintype.card J : ℝ) * B ^ 2 := by
    rw [Finset.mul_sum]
    calc ∑ j, (∑ o, w o) * energy K (Ψ j) ≤ ∑ _j : J, B ^ 2 := Finset.sum_le_sum fun j _ => hsingle j
      _ = _ := by simp
  have hpos : 0 ≤ Real.sqrt (Fintype.card J) * B := mul_nonneg (Real.sqrt_nonneg _) hB
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) hpos (by norm_num : (2 : ℕ) ≠ 0)).1 ?_
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact h.trans hsum

/-- **Regression** (FINITE REGRESSION): labelled energy may exceed every single-label energy,
so the energy-level factor `L` cannot be dropped. -/
theorem label_energy_not_le_max :
    ∃ (K : Fin 2 → Fin 2 → ℂ) (Ψ : Fin 2 → Fin 2 → ℂ) (κ : Fin 2 → Fin 2),
      (∀ j i, ‖Ψ j i‖ ≤ 1) ∧ (∀ j, energy K (Ψ j) = 1) ∧ labelEnergy K Ψ κ = 2 := by
  refine ⟨fun o i => if o = i then 1 else 0, fun j i => if j = i then 1 else 0, id,
    fun j i => by dsimp only; split_ifs <;> simp, fun j => ?_, ?_⟩
  · fin_cases j <;> simp [energy, innerSum, Fin.sum_univ_two]
  · simp [labelEnergy, labelInner, innerSum]

end FiniteLabelEnergy
end ResearchBankV27
end Erdos287
