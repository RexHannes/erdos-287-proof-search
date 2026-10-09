import RequestProject.Erdos287.ResearchBankV14.HarmonicTail
import RequestProject.Erdos287.ResearchBankV16.RouteCParameters

/-!
# Erdős #287 — Research Bank V16 §4: Route-C contact localization, `c_C = 46/125`

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Macro-group `r ∈ {0,…,25}` receives the box `(r + 1 − ξ, r + 1 + ξ)`, `ξ = 1/1000`.  Adjacent
groups in `G(26,7)` satisfy `7 ≤ s − r ≤ 19`.  The Route-C contact ratio is

    R_C = ((19 + 2ξ)/(7 − 2ξ)) · ρ_C²,      ρ_C = 10001/10000,

where `ρ_C` is the translation buffer (`A ≥ 10000 · max b_v`).  **Caveat:** the audited numerical
value of `R_C` was not supplied to this run; the formula above is the reconstruction from the
26-group geometry, and every constant is a visible definition.

Kernel-proved (LEAN BANK):
* `cC_gt_inv_e` — `c_C = 46/125 > 1/e` (Mathlib's certified `e > 2.7182818283`);
* `log_125_46_lt_one` — `log(125/46) < 1`;
* `RC_lt` / `cC_mul_RC_lt_one` — `R_C < 125/46`, i.e. `c_C R_C < 1`;
* `cC_mul_RC_buffer_lt_one` — buffered `c_C R_C ρ_C² < 1` (used by the proportional window);
* `edge_difference_range_C`, `contact_coeff_ratio_C` — the audited contact-ratio inequality;
* `two_hole_contradiction_cC` — the harmonic two-hole contradiction at `c_C`, re-proved natively
  (`cC_lt_c_routeB`: `46/125 < 37/100`, so the V14 statement at `37/100` does not apply);
* negative controls (FINITE REGRESSION): `routeB_c_fails_with_RC` — the Route-B constant
  `c = 37/100` does NOT satisfy `c R_C < 1`; `routeB_buffer_fails` — the Route-B translation
  buffer `1001/1000` does NOT give `c_C R < 1`.  Route-B constants are therefore not imported.
-/

namespace Erdos287
namespace ResearchBankV16
namespace ContactLocalizationC

open RouteCParameters ResearchBankV13.FiniteRepresentationModel

/-- `c_C = 46/125`. -/
def cC : ℚ := 46 / 125

/-- Translation / window buffer `ρ_C = 10001/10000`. -/
def rhoC : ℚ := 10001 / 10000

/-- Edge-difference ratio `(19 + 2ξ)/(7 − 2ξ)`. -/
def diffRatio : ℚ := (19 + 2 * xi) / (7 - 2 * xi)

/-- **The Route-C contact ratio** `R_C = diffRatio · ρ_C²`. -/
def RC : ℚ := diffRatio * rhoC ^ 2

theorem diffRatio_eq : diffRatio = 9501 / 3499 := by unfold diffRatio xi; norm_num

theorem RC_eq : RC = 950290029501 / 349900000000 := by
  unfold RC diffRatio rhoC xi; norm_num

theorem RC_lt : RC < 125 / 46 := by rw [RC_eq]; norm_num

/-- `c_C R_C < 1`. -/
theorem cC_mul_RC_lt_one : cC * RC < 1 := by unfold cC; rw [RC_eq]; norm_num

/-- Buffered: `c_C R_C ρ_C² < 1`. -/
theorem cC_mul_RC_buffer_lt_one : cC * RC * rhoC ^ 2 < 1 := by
  unfold cC rhoC; rw [RC_eq]; norm_num

/-- **`c_C > 1/e`.** -/
theorem cC_gt_inv_e : 1 / Real.exp 1 < ((cC : ℚ) : ℝ) := by
  have he := Real.exp_one_gt_d9
  have hpos := Real.exp_pos 1
  unfold cC; push_cast
  rw [div_lt_iff₀ hpos]; linarith

/-- `log(125/46) < 1`. -/
theorem log_125_46_lt_one : Real.log (125 / 46) < 1 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have := Real.exp_one_gt_d9
  linarith

/-- **Negative control:** the Route-B constant `37/100` fails against `R_C`. -/
theorem routeB_c_fails_with_RC : 1 < (37 / 100 : ℚ) * RC := by rw [RC_eq]; norm_num

/-- **Negative control:** the Route-B translation buffer `1001/1000` fails against `c_C`. -/
theorem routeB_buffer_fails : 1 < cC * (diffRatio * (1001 / 1000) ^ 2) := by
  unfold cC; rw [diffRatio_eq]; norm_num

/-- `c_C = 46/125 < 37/100`: Route C uses a SHARPER contact constant than Route B, so the banked
V14 harmonic tail at `c = 37/100` does not apply and is re-proved below at `c_C`. -/
theorem cC_lt_c_routeB : cC < ResearchBankV14.HarmonicTail.c := by
  unfold ResearchBankV14.HarmonicTail.c cC; norm_num

/-- Box of macro-group `r`. -/
def boxLo (r : ℕ) : ℚ := r + 1 - xi
def boxHi (r : ℕ) : ℚ := r + 1 + xi

/-- **Edge-difference range** for adjacent groups `7 ≤ s − r ≤ 19`. -/
theorem edge_difference_range_C {r s : ℕ} (hrs : 7 ≤ (s : ℤ) - r) (hrs' : (s : ℤ) - r ≤ 19)
    {xu xv : ℚ} (hu : boxLo r < xu ∧ xu < boxHi r) (hv : boxLo s < xv ∧ xv < boxHi s) :
    7 - 2 * xi < xv - xu ∧ xv - xu < 19 + 2 * xi := by
  unfold boxLo boxHi at *
  have h1 : (7 : ℚ) ≤ (s : ℚ) - r := by exact_mod_cast hrs
  have h2 : (s : ℚ) - r ≤ 19 := by exact_mod_cast hrs'
  constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]

/-- **The audited contact-ratio inequality** (Route C).  If `a_u ≤ ρ_C a_{u'}`,
`a_v ≤ ρ_C a_{v'}` and `d' ≤ diffRatio · d`, then `(a_u/d) a_v ≤ R_C · (a_{u'}/d') a_{v'}`. -/
theorem contact_coeff_ratio_C {au av au' av' d d' : ℚ} (hau : 0 < au') (hav : 0 < av')
    (hd : 0 < d) (hd' : 0 < d') (h1 : au ≤ rhoC * au') (h2 : av ≤ rhoC * av')
    (h3 : d' ≤ diffRatio * d) (hav0 : 0 ≤ av) :
    au / d * av ≤ RC * (au' / d' * av') := by
  have hr : (0 : ℚ) < rhoC := by unfold rhoC; norm_num
  have hq : (0 : ℚ) < diffRatio := by rw [diffRatio_eq]; norm_num
  have e1 : au * av ≤ rhoC ^ 2 * (au' * av') := by
    calc au * av ≤ (rhoC * au') * (rhoC * av') := mul_le_mul h1 h2 hav0 (by positivity)
      _ = rhoC ^ 2 * (au' * av') := by ring
  have e2 : 1 / d ≤ diffRatio * (1 / d') := by
    rw [div_le_iff₀ hd]
    have : diffRatio * (1 / d') * d = (diffRatio * d) / d' := by field_simp
    rw [this, le_div_iff₀ hd']; linarith
  calc au / d * av = (au * av) * (1 / d) := by ring
    _ ≤ (rhoC ^ 2 * (au' * av')) * (diffRatio * (1 / d')) :=
        mul_le_mul e1 e2 (by positivity) (by positivity)
    _ = RC * (au' / d' * av') := by unfold RC; ring

/-- The two edge differences of two Route-C edges satisfy `d' ≤ diffRatio · d` (scaled by any
`T > 0`: `(7 − 2ξ)T < d` and `d' < (19 + 2ξ)T`). -/
theorem diff_ratio_of_ranges {T d d' : ℚ} (hT : 0 < T) (hd : (7 - 2 * xi) * T < d)
    (hd' : d' < (19 + 2 * xi) * T) : d' ≤ diffRatio * d := by
  unfold diffRatio xi at *
  have : (19 + 2 * (1 / 1000 : ℚ)) * T = (19 + 2 * (1 / 1000)) / (7 - 2 * (1 / 1000)) *
      ((7 - 2 * (1 / 1000)) * T) := by field_simp
  have hpos : (0 : ℚ) < (19 + 2 * (1 / 1000)) / (7 - 2 * (1 / 1000)) := by norm_num
  nlinarith

/-- `z ≥ c_C M ⟹ log(M/z) ≤ log(125/46)`. -/
theorem log_ratio_le_cC {z M : ℕ} (hz : 1 ≤ z) (hc : ((cC : ℚ) : ℝ) * M ≤ z) :
    Real.log ((M : ℝ) / z) ≤ Real.log (125 / 46) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp; exact (Real.log_pos (by norm_num)).le
  have hz0 : (0 : ℝ) < z := by exact_mod_cast hz
  apply Real.log_le_log (by positivity)
  rw [div_le_iff₀ hz0]
  unfold cC at hc; push_cast at hc
  linarith

/-- **The harmonic two-hole contradiction at `c_C = 46/125`** (proved natively from the banked
discrete tail bound and `log(125/46) < 1`). -/
theorem two_hole_contradiction_cC {A : Finset ℕ} (hA : Erdos287Counterexample A) {z : ℕ}
    (hz : z ∉ A) (hz1 : z + 1 ∉ A) (hzM : z ≤ A.max' hA.nonempty)
    (hc : ((cC : ℚ) : ℝ) * A.max' hA.nonempty ≤ z) : False := by
  set M := A.max' hA.nonempty
  have hsub := ResearchBankV14.HarmonicTail.selected_set_above hA hz hz1 hzM
  have hz1' : 1 ≤ z := by
    by_contra h0; push_neg at h0
    have hz0 : z = 0 := by omega
    have hM4 := hA.four_le_max
    rw [hz0] at hc
    have : (4 : ℝ) ≤ M := by exact_mod_cast hM4
    unfold cC at hc; push_cast at hc; linarith
  have hM2 : z + 2 ≤ M := by
    have := hsub M (Finset.max'_mem _ _); omega
  have hS : A ⊆ Finset.Ioc (z + 1) M := fun a ha =>
    Finset.mem_Ioc.2 ⟨by have := (hsub a ha).1; omega, (hsub a ha).2⟩
  have hsumR : ∑ a ∈ A, (1 : ℝ) / a = 1 := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hA.sum_one
    simpa using this
  have hle : ∑ a ∈ A, (1 : ℝ) / a ≤ ∑ n ∈ Finset.Ioc (z + 1) M, (1 : ℝ) / n :=
    Finset.sum_le_sum_of_subset_of_nonneg hS fun _ _ _ => by positivity
  have h1 := ResearchBankV14.HarmonicTail.harmonic_tail_lt_log hz1' (by omega : z + 1 ≤ M)
  have h2 := log_ratio_le_cC hz1' hc
  have h3 := log_125_46_lt_one
  linarith

end ContactLocalizationC
end ResearchBankV16
end Erdos287
