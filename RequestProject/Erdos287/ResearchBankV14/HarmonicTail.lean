import RequestProject.Erdos287.ResearchBankV13.HarmonicTwoHole

/-!
# Erdős #287 — Research Bank V14 §A9: the harmonic two-hole contradiction with `c = 37/100`

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* `selected_set_above` — two consecutive omissions `z, z+1` with `z ≤ M`, plus the banked
  successive-gap condition, force the selected set into `[z+2, M]`;
* `harmonic_tail_lt_log` — `∑_{n=z+2}^{M} 1/n < log(M/z)`;
* `log_ratio_le` — `z ≥ (37/100) M` gives `log(M/z) ≤ log(100/37)`;
* `log_100_37_lt_one` — `log(100/37) < 1` (from Mathlib's proved bound `e > 2.7182818283`;
  no numerical axiom, no provider needed);
* `two_hole_contradiction_c` — the full contradiction.  Only licensed inequalities are used:
  the discrete tail bound `harmonic_tail_le_log` (from `log x ≤ x − 1`) and the rational bound
  on `e`.
-/

namespace Erdos287
namespace ResearchBankV14
namespace HarmonicTail

open ResearchBankV13.HarmonicTwoHole ResearchBankV13.FiniteRepresentationModel

/-- `c = 37/100`. -/
def c : ℚ := 37 / 100

/-- `log(100/37) < 1`. -/
theorem log_100_37_lt_one : Real.log (100 / 37) < 1 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have := Real.exp_one_gt_d9
  linarith

/-- `c > 1/e`. -/
theorem c_gt_inv_e : 1 / Real.exp 1 < ((c : ℚ) : ℝ) := by
  have he := Real.exp_one_gt_d9
  have hpos := Real.exp_pos 1
  unfold c; push_cast
  rw [div_lt_iff₀ hpos]; linarith

/-- **The selected set lies in `[z+2, M]`.** -/
theorem selected_set_above {A : Finset ℕ} (hA : Erdos287Counterexample A) {z : ℕ}
    (hz : z ∉ A) (hz1 : z + 1 ∉ A) (hzM : z ≤ A.max' hA.nonempty) :
    ∀ a ∈ A, z + 2 ≤ a ∧ a ≤ A.max' hA.nonempty := by
  have hMA : A.max' hA.nonempty ∈ A := Finset.max'_mem _ _
  have hM2 : z + 2 ≤ A.max' hA.nonempty := by
    have h1 : A.max' hA.nonempty ≠ z := fun e => hz (e ▸ hMA)
    have h2 : A.max' hA.nonempty ≠ z + 1 := fun e => hz1 (e ▸ hMA)
    omega
  intro a ha
  refine ⟨?_, Finset.le_max' _ _ ha⟩
  by_contra hlt
  push_neg at hlt
  have ha1 : a ≠ z := fun e => hz (e ▸ ha)
  have ha2 : a ≠ z + 1 := fun e => hz1 (e ▸ ha)
  have hN : A.min' hA.nonempty ≤ z := le_trans (Finset.min'_le _ _ ha) (by omega)
  exact cannot_cross_two_holes hA hz hz1 hN (by omega)

/-- **`∑_{n=z+2}^{M} 1/n < log(M/z)`.** -/
theorem harmonic_tail_lt_log {z M : ℕ} (hz : 1 ≤ z) (hzM : z + 1 ≤ M) :
    ∑ n ∈ Finset.Ioc (z + 1) M, (1 : ℝ) / n < Real.log ((M : ℝ) / z) := by
  have h := harmonic_tail_le_log (H := z + 1) (by omega) M hzM
  have hz0 : (0 : ℝ) < z := by exact_mod_cast hz
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  rw [Real.log_div hM0.ne' hz0.ne']
  have : Real.log (z : ℝ) < Real.log ((z + 1 : ℕ) : ℝ) :=
    Real.log_lt_log hz0 (by push_cast; linarith)
  linarith

/-- **`z ≥ (37/100) M ⟹ log(M/z) ≤ log(100/37)`.** -/
theorem log_ratio_le {z M : ℕ} (hz : 1 ≤ z) (hc : ((c : ℚ) : ℝ) * M ≤ z) :
    Real.log ((M : ℝ) / z) ≤ Real.log (100 / 37) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp; exact (Real.log_pos (by norm_num)).le
  have hz0 : (0 : ℝ) < z := by exact_mod_cast hz
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  apply Real.log_le_log (by positivity)
  rw [div_le_iff₀ hz0]
  unfold c at hc; push_cast at hc
  linarith

/-- **The harmonic two-hole contradiction** with `c = 37/100`. -/
theorem two_hole_contradiction_c {A : Finset ℕ} (hA : Erdos287Counterexample A) {z : ℕ}
    (hz : z ∉ A) (hz1 : z + 1 ∉ A) (hzM : z ≤ A.max' hA.nonempty)
    (hc : ((c : ℚ) : ℝ) * A.max' hA.nonempty ≤ z) : False := by
  set M := A.max' hA.nonempty
  have hsub := selected_set_above hA hz hz1 hzM
  have hz1' : 1 ≤ z := by
    by_contra h0; push_neg at h0
    have hz0 : z = 0 := by omega
    have hM4 := hA.four_le_max
    rw [hz0] at hc
    have : (4 : ℝ) ≤ M := by exact_mod_cast hM4
    unfold c at hc; push_cast at hc; linarith
  have hM2 : z + 2 ≤ M := by
    have := hsub M (Finset.max'_mem _ _); omega
  have hS : A ⊆ Finset.Ioc (z + 1) M := fun a ha =>
    Finset.mem_Ioc.2 ⟨by have := (hsub a ha).1; omega, (hsub a ha).2⟩
  have hsumR : ∑ a ∈ A, (1 : ℝ) / a = 1 := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hA.sum_one
    simpa using this
  have hle : ∑ a ∈ A, (1 : ℝ) / a ≤ ∑ n ∈ Finset.Ioc (z + 1) M, (1 : ℝ) / n :=
    Finset.sum_le_sum_of_subset_of_nonneg hS fun _ _ _ => by positivity
  have h1 := harmonic_tail_lt_log hz1' (by omega : z + 1 ≤ M)
  have h2 := log_ratio_le hz1' hc
  have h3 := log_100_37_lt_one
  linarith

/-- The `c = 37/100` window fits the V13 `η = 685/252` window: `37 M ≤ 100 z ⟹ M ≤ ⌊η (z+1)⌋`. -/
theorem c_window_in_eta {z M : ℕ} (h : 37 * M ≤ 100 * z) : M ≤ etaFloor (z + 1) := by
  unfold etaFloor
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  omega

end HarmonicTail
end ResearchBankV14
end Erdos287
