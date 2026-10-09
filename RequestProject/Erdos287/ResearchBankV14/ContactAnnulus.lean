import RequestProject.Erdos287.ResearchBankV14.HarmonicTail
import RequestProject.Erdos287.ResearchBankV14.MacroGraph11

/-!
# Erdős #287 — Research Bank V14 §A5: the contact annulus with explicit buffer

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Macro cell `r` receives the box `(r + 1 − ε, r + 1 + ε)`, `ε = 1/100`.

* `edge_difference_range` — oriented form: for adjacent cells `r < s` (so `3 ≤ s − r ≤ 8`) and
  positions `x_u ∈ (r+1−ε, r+1+ε)`, `x_v ∈ (s+1−ε, s+1+ε)`:  `149/50 < x_v − x_u < 401/50`;
  `scaled_edge_difference` — the same after scaling by `T`;
* `ratio_of_translation` — `A ≥ 1000 · max b_v` (all `b_v > 0`) gives
  `max a_v / min a_v ≤ 1001/1000` for `a_v = A + b_v`;
* `Rstar_eq` — `R* = (401/149)(1001/1000)^2 = 401802401/149000000`;
* `Rstar_chain` — `R* < 100/37 < 685/252 < e` (the last step is V13's `eta_lt_exp`, from
  Mathlib's proved rational lower bound on `e`);
* `c_gt_inv_e`, `c_mul_Rstar_lt_one`, `c_mul_Rstar_buffer_lt_one` — `c = 37/100 > 1/e`,
  `c R* < 1`, and even `c R* (1001/1000)^2 < 1` (buffer used by the proportional `t`-interval);
* `contact_coeff_ratio` — for two oriented edges the contact coefficients `(a_u/d) a_v` differ by
  at most the factor `R*`;
* `one_window` — **all useful contacts lie in one proportional window `[cM, M]`** once the scale
  `M` is chosen as the largest contact.
-/

namespace Erdos287
namespace ResearchBankV14
namespace ContactAnnulus

open ResearchBankV13.HarmonicTwoHole

/-- `ε = 1/100`. -/
def eps : ℚ := 1 / 100

/-- Box of macro cell `r`. -/
def boxLo (r : ℕ) : ℚ := r + 1 - eps
def boxHi (r : ℕ) : ℚ := r + 1 + eps

/-- `R* = (401/149)·(1001/1000)^2`. -/
def Rstar : ℚ := 401 / 149 * (1001 / 1000) ^ 2

/-- `ρ = 1001/1000`. -/
def rho : ℚ := 1001 / 1000

theorem Rstar_eq : Rstar = 401802401 / 149000000 := by unfold Rstar; norm_num

theorem Rstar_lt : Rstar < 100 / 37 := by unfold Rstar; norm_num

/-- **`R* < 100/37 < 685/252 < e`.** -/
theorem Rstar_chain :
    Rstar < 100 / 37 ∧ (100 / 37 : ℚ) < 685 / 252 ∧ ((685 / 252 : ℚ) : ℝ) < Real.exp 1 :=
  ⟨Rstar_lt, by norm_num, by have := eta_lt_exp; unfold eta at this; exact this⟩

theorem c_eq : HarmonicTail.c = 37 / 100 := rfl

/-- `c > 1/e`. -/
theorem c_gt_inv_e : 1 / Real.exp 1 < ((HarmonicTail.c : ℚ) : ℝ) := HarmonicTail.c_gt_inv_e

/-- `c R* < 1`. -/
theorem c_mul_Rstar_lt_one : HarmonicTail.c * Rstar < 1 := by
  unfold HarmonicTail.c Rstar; norm_num

/-- Buffered version: `c R* (1001/1000)^2 < 1`. -/
theorem c_mul_Rstar_buffer_lt_one : HarmonicTail.c * Rstar * rho ^ 2 < 1 := by
  unfold HarmonicTail.c Rstar rho; norm_num

/-- **Edge-difference range** (oriented, unscaled). -/
theorem edge_difference_range {r s : ℕ} (hrs : 3 ≤ (s : ℤ) - r) (hrs' : (s : ℤ) - r ≤ 8)
    {xu xv : ℚ} (hu : boxLo r < xu ∧ xu < boxHi r) (hv : boxLo s < xv ∧ xv < boxHi s) :
    149 / 50 < xv - xu ∧ xv - xu < 401 / 50 := by
  unfold boxLo boxHi eps at *
  have h1 : (3 : ℚ) ≤ (s : ℚ) - r := by exact_mod_cast hrs
  have h2 : (s : ℚ) - r ≤ 8 := by exact_mod_cast hrs'
  constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]

/-- **Edge-difference range**, scaled by `T > 0`. -/
theorem scaled_edge_difference {r s : ℕ} (hrs : 3 ≤ (s : ℤ) - r) (hrs' : (s : ℤ) - r ≤ 8)
    {T : ℚ} (hT : 0 < T) {bu bv : ℚ}
    (hu : boxLo r * T < bu ∧ bu < boxHi r * T) (hv : boxLo s * T < bv ∧ bv < boxHi s * T) :
    149 / 50 * T < bv - bu ∧ bv - bu < 401 / 50 * T := by
  have hu' : boxLo r < bu / T ∧ bu / T < boxHi r :=
    ⟨by rw [lt_div_iff₀ hT]; exact hu.1, by rw [div_lt_iff₀ hT]; exact hu.2⟩
  have hv' : boxLo s < bv / T ∧ bv / T < boxHi s :=
    ⟨by rw [lt_div_iff₀ hT]; exact hv.1, by rw [div_lt_iff₀ hT]; exact hv.2⟩
  obtain ⟨h1, h2⟩ := edge_difference_range hrs hrs' hu' hv'
  rw [← sub_div] at h1 h2
  exact ⟨by rwa [lt_div_iff₀ hT] at h1, by rwa [div_lt_iff₀ hT] at h2⟩

/-- Adjacent macro cells, oriented `r < s`, differ by `3 … 8`. -/
theorem adj_oriented {r s : Fin 11} (h : MacroGraph11.G11.Adj r s) (hlt : r.val < s.val) :
    3 ≤ (s.val : ℤ) - r.val ∧ (s.val : ℤ) - r.val ≤ 8 := by
  have h1 := MacroGraph11.adj_diff_range r s h
  have h2 := MacroGraph11.adj_diff_le r s h
  omega

/-- **Ratio after translation**: `A ≥ 1000 b` for all (positive) `b` gives `a_u ≤ ρ a_v`. -/
theorem ratio_of_translation {A bu bv : ℚ} (hbv : 0 < bv) (hAu : 1000 * bu ≤ A) :
    A + bu ≤ rho * (A + bv) := by
  unfold rho; nlinarith

/-- **Contact-coefficient ratio.**  If `a_u ≤ ρ a_{u'}`, `a_v ≤ ρ a_{v'}` and the two edge
differences satisfy `d' ≤ (401/149) d` (from `149/50 T < d`, `d' < 401/50 T`), then
`(a_u/d) a_v ≤ R* · (a_{u'}/d') a_{v'}`. -/
theorem contact_coeff_ratio {au av au' av' d d' : ℚ} (hau : 0 < au') (hav : 0 < av')
    (hd : 0 < d) (hd' : 0 < d') (h1 : au ≤ rho * au') (h2 : av ≤ rho * av')
    (h3 : d' ≤ 401 / 149 * d) (hav0 : 0 ≤ av) :
    au / d * av ≤ Rstar * (au' / d' * av') := by
  have hr : (0 : ℚ) < rho := by unfold rho; norm_num
  have e1 : au * av ≤ rho ^ 2 * (au' * av') := by
    calc au * av ≤ (rho * au') * (rho * av') := mul_le_mul h1 h2 hav0 (by positivity)
      _ = rho ^ 2 * (au' * av') := by ring
  have e2 : 1 / d ≤ 401 / 149 * (1 / d') := by
    rw [div_le_iff₀ hd]
    have : 401 / 149 * (1 / d') * d = (401 / 149 * d) / d' := by field_simp
    rw [this, le_div_iff₀ hd']; linarith
  have hRs : Rstar = 401 / 149 * rho ^ 2 := by unfold Rstar rho; ring
  calc au / d * av = (au * av) * (1 / d) := by ring
    _ ≤ (rho ^ 2 * (au' * av')) * (401 / 149 * (1 / d')) :=
        mul_le_mul e1 e2 (by positivity) (by positivity)
    _ = Rstar * (au' / d' * av') := by rw [hRs]; ring

/-- **One proportional window.**  If a finite nonempty family of contacts has all pairwise
ratios `≤ R`, all contacts are nonnegative and `c R ≤ 1`, then with `M = max` every contact lies in `[cM, M]`. -/
theorem one_window {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (z : ι → ℝ) {R cc : ℝ}
    (hc : 0 ≤ cc) (hcR : cc * R ≤ 1) (hpos : ∀ i ∈ s, 0 ≤ z i) (hratio : ∀ i ∈ s, ∀ j ∈ s, z i ≤ R * z j) :
    ∀ j ∈ s, cc * s.sup' hs z ≤ z j ∧ z j ≤ s.sup' hs z := by
  intro j hj
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' hs z
  refine ⟨?_, Finset.le_sup' z hj⟩
  rw [hmax]
  have h1 := hratio i hi j hj
  calc cc * z i ≤ cc * (R * z j) := mul_le_mul_of_nonneg_left h1 hc
    _ = (cc * R) * z j := by ring
    _ ≤ 1 * z j := mul_le_mul_of_nonneg_right hcR (hpos j hj)
    _ = z j := one_mul _

end ContactAnnulus
end ResearchBankV14
end Erdos287
