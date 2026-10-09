import Mathlib

/-!
# W2.984 — the one-dimensional sieve functions in the range used by Merikoski's `Ω₁, Ω₂, Ω₃`

**ERDŐS #287 REMAINS OPEN.  This file is real analysis about explicit functions only.**

Merikoski (arXiv:1811.03008v3, §3) uses the linear-sieve functions `F_lin`, `f_lin`
(delay-differential system with `sF(s) = 2e^γ` on `[1,3]`, `sf(s) = 0` on `s ≤ 2`) and the Buchstab
function `ω` (`sω(s) = 1` on `[1,2]`, `(sω(s))' = ω(s-1)` for `s > 2`).  At `α = 1/7`, `β = 3/14`
only the following ranges are evaluated:

* `F_lin` at `s = 7/2 ∈ [3,5]`;
* `f_lin` on `[2, 5/2] ⊂ [2,4]`;
* `ω` on `[5/3, 4]`.

We therefore *define* the three functions by their exact closed forms on those ranges
(`flin`, `Flin`, `buchstab`) and **prove** that these closed forms satisfy the defining
delay-differential systems there (`Flin_initial`, `Flin_dde`, `flin_at_two`, `flin_dde`,
`buchstab_initial`, `buchstab_dde_mid`, `buchstab_dde_tail`, continuity at the break points).
Outside those ranges the Lean functions are **not** the sieve functions and are never used.

Main analytic fact: `buchstab_le` — `ω(t) ≤ 3/5` for `t ∈ [5/3, 4]` (in fact the proof shows the
`[2,4]` part is `< 0.6` because `log(7/4) < 3/5` and `log 2 < 4/5`).
-/

namespace Erdos287.W2984Publication

open Real intervalIntegral MeasureTheory Set

noncomputable def eγ : ℝ := Real.exp Real.eulerMascheroniConstant

theorem eγ_pos : 0 < eγ := Real.exp_pos _

noncomputable def flin (s : ℝ) : ℝ := 2 * eγ * Real.log (s - 1) / s

noncomputable def Flin (s : ℝ) : ℝ :=
  if s ≤ 3 then 2 * eγ / s else (2 * eγ + ∫ u in (3:ℝ)..s, flin (u - 1)) / s


/-! ### Faithfulness of `flin`, `Flin` (Merikoski §3, Friedlander–Iwaniec Ch. 11–12) -/

theorem Flin_initial {s : ℝ} (h1 : 1 ≤ s) (h3 : s ≤ 3) : s * Flin s = 2 * eγ := by
  unfold Flin; rw [if_pos h3]; field_simp

theorem flin_at_two : 2 * flin 2 = 0 := by
  unfold flin; norm_num

/-- `(s f(s))' = F(s-1)` on `(2,4)`. -/
theorem flin_dde {s : ℝ} (h2 : 2 < s) (h4 : s < 4) :
    HasDerivAt (fun x => x * flin x) (Flin (s - 1)) s := by
  have hev : (fun x => 2 * eγ * Real.log (x - 1)) =ᶠ[nhds s] (fun x => x * flin x) := by
    filter_upwards [Ioi_mem_nhds (show (1:ℝ) < s by linarith)] with x hx
    unfold flin
    field_simp [show x ≠ 0 by linarith [show (1:ℝ) < x from hx]]
  have hd : HasDerivAt (fun x => 2 * eγ * Real.log (x - 1)) (2 * eγ * (1 / (s - 1))) s := by
    have := (((hasDerivAt_id s).sub_const 1).log (by simp; linarith)).const_mul (2 * eγ)
    convert this using 1
  have hval : Flin (s - 1) = 2 * eγ * (1 / (s - 1)) := by
    unfold Flin; rw [if_pos (by linarith)]; ring
  rw [hval]
  exact hd.congr_of_eventuallyEq hev.symm

/-- `(s F(s))' = f(s-1)` on `(3,5)`. -/
theorem Flin_dde {s : ℝ} (hs : s ∈ Ioo (3:ℝ) 5) :
    HasDerivAt (fun x => x * Flin x) (flin (s - 1)) s := by
  have h3 := hs.1
  have hev : (fun x => 2 * eγ + ∫ u in (3:ℝ)..x, flin (u - 1))
      =ᶠ[nhds s] (fun x => x * Flin x) := by
    filter_upwards [Ioi_mem_nhds h3] with x hx
    unfold Flin
    rw [if_neg (by linarith [show (3:ℝ) < x from hx])]
    field_simp [show x ≠ 0 by linarith [show (3:ℝ) < x from hx]]
  have hcontOn : ContinuousOn (fun u : ℝ => flin (u - 1)) (Ioi 2) := by
    intro u hu
    apply ContinuousAt.continuousWithinAt
    have hu' : (2:ℝ) < u := hu
    unfold flin
    have : u - 1 ≠ 0 := by linarith
    have : u - 1 - 1 ≠ 0 := by linarith
    fun_prop (disch := assumption)
  have hint : IntervalIntegrable (fun u : ℝ => flin (u - 1)) volume 3 s :=
    (hcontOn.mono (by
      intro u hu; rw [uIcc_of_le h3.le] at hu; exact show (2:ℝ) < u by linarith [hu.1])).intervalIntegrable
  have hd := (intervalIntegral.integral_hasDerivAt_right hint
    (hcontOn.stronglyMeasurableAtFilter isOpen_Ioi s (show (2:ℝ) < s by linarith))
    (hcontOn.continuousAt (Ioi_mem_nhds (show (2:ℝ) < s by linarith)))).const_add (2 * eγ)
  exact hd.congr_of_eventuallyEq hev.symm

/-- `Flin` is continuous at the break point `3`. -/
theorem Flin_at_three : (2 * eγ + ∫ u in (3:ℝ)..3, flin (u - 1)) / 3 = 2 * eγ / 3 := by simp

/-! ### The Buchstab function on `[1, 4]` -/

noncomputable def buchstab (t : ℝ) : ℝ :=
  if t ≤ 2 then 1 / t
  else if t ≤ 3 then (1 + Real.log (t - 1)) / t
  else (1 + Real.log 2 + ∫ u in (3:ℝ)..t, (1 + Real.log (u - 2)) / (u - 1)) / t

theorem log_seven_fourths_lt : Real.log (7/4) < 3/5 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 3/5)
  linarith

theorem buchstab_mid_le {t : ℝ} (h2 : 2 ≤ t) :
    (1 + Real.log (t - 1)) / t ≤ 3/5 := by
  have ht : 0 < t := by linarith
  rw [div_le_iff₀ ht]
  have hx : 0 < t - 1 := by linarith
  -- `log x ≤ log a + x/a - 1`
  have hl : Real.log (t - 1) ≤ Real.log (7/4) + (t - 1) / (7/4) - 1 := by
    have := Real.log_le_sub_one_of_pos (show 0 < (t - 1) / (7/4) by positivity)
    rw [Real.log_div (ne_of_gt hx) (by norm_num)] at this
    linarith
  have := log_seven_fourths_lt
  nlinarith

theorem buchstab_mid_nonneg {t : ℝ} (h2 : 2 ≤ t) : 0 ≤ (1 + Real.log (t - 1)) / t := by
  have : 0 ≤ Real.log (t - 1) := Real.log_nonneg (by linarith)
  positivity

theorem intInt_buchstab_tail {t : ℝ} (h3 : 3 ≤ t) :
    IntervalIntegrable (fun u : ℝ => (1 + Real.log (u - 2)) / (u - 1)) volume 3 t := by
  apply ContinuousOn.intervalIntegrable
  intro u hu
  rw [uIcc_of_le h3] at hu
  apply ContinuousAt.continuousWithinAt
  have : u - 1 ≠ 0 := by linarith [hu.1]
  have : u - 2 ≠ 0 := by linarith [hu.1]
  fun_prop (disch := assumption)

theorem buchstab_tail_integral_le {t : ℝ} (h3 : 3 ≤ t) :
    (∫ u in (3:ℝ)..t, (1 + Real.log (u - 2)) / (u - 1)) ≤ 3/5 * (t - 3) := by
  have : (∫ u in (3:ℝ)..t, (3/5 : ℝ)) = 3/5 * (t - 3) := by simp; ring
  rw [← this]
  apply intervalIntegral.integral_mono_on h3 (intInt_buchstab_tail h3) (by simp)
  intro u hu
  have := buchstab_mid_le (t := u - 1) (by linarith [hu.1])
  rwa [show u - 1 - 1 = u - 2 by ring] at this

theorem buchstab_tail_integral_nonneg {t : ℝ} (h3 : 3 ≤ t) :
    0 ≤ ∫ u in (3:ℝ)..t, (1 + Real.log (u - 2)) / (u - 1) := by
  apply intervalIntegral.integral_nonneg h3
  intro u hu
  have := buchstab_mid_nonneg (t := u - 1) (by linarith [hu.1])
  rwa [show u - 1 - 1 = u - 2 by ring] at this

/-- **Buchstab bound** `ω(t) ≤ 3/5` on `[5/3, 4]` (the range used in `Ω₃`). -/
theorem buchstab_le {t : ℝ} (ht : t ∈ Icc (5/3 : ℝ) 4) : buchstab t ≤ 3/5 := by
  have h1 := ht.1
  unfold buchstab
  split_ifs with ha hb
  · rw [div_le_iff₀ (by linarith)]; linarith
  · exact buchstab_mid_le (by linarith)
  · have ht : 0 < t := by linarith
    rw [div_le_iff₀ ht]
    have := buchstab_tail_integral_le (t := t) (by linarith)
    have := Real.log_two_lt_d9
    linarith

theorem buchstab_nonneg {t : ℝ} (h1 : 1 ≤ t) : 0 ≤ buchstab t := by
  unfold buchstab
  split_ifs with ha hb
  · have : 0 < t := by linarith
    positivity
  · exact buchstab_mid_nonneg (by linarith)
  · have := buchstab_tail_integral_nonneg (t := t) (by linarith)
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
    have : 0 < t := by linarith
    positivity

/-! Faithfulness of the explicit pieces: Buchstab's delay-differential system on `[1,4]`. -/

theorem buchstab_initial {t : ℝ} (h1 : 1 ≤ t) (h2 : t ≤ 2) : t * buchstab t = 1 := by
  unfold buchstab; rw [if_pos h2]; field_simp

theorem buchstab_at_two : buchstab 2 = (1 + Real.log (2 - 1)) / 2 := by
  unfold buchstab; norm_num

theorem buchstab_at_three : buchstab 3 = (1 + Real.log 2 + ∫ u in (3:ℝ)..3,
    (1 + Real.log (u - 2)) / (u - 1)) / 3 := by
  unfold buchstab; norm_num

theorem buchstab_dde_mid {t : ℝ} (h2 : 2 < t) (h3 : t < 3) :
    HasDerivAt (fun x => x * buchstab x) (buchstab (t - 1)) t := by
  have hev : (fun x => 1 + Real.log (x - 1)) =ᶠ[nhds t] (fun x => x * buchstab x) := by
    filter_upwards [Ioo_mem_nhds h2 h3] with x hx
    unfold buchstab
    rw [if_neg (by linarith [hx.1]), if_pos (by linarith [hx.2])]
    field_simp [show x ≠ 0 by linarith [hx.1]]
  have hd : HasDerivAt (fun x => 1 + Real.log (x - 1)) (1 / (t - 1)) t := by
    have := (((hasDerivAt_id t).sub_const 1).log (by simp; linarith)).const_add 1
    convert this using 1
  have hval : buchstab (t - 1) = 1 / (t - 1) := by
    unfold buchstab; rw [if_pos (by linarith)]
  rw [hval]
  exact hd.congr_of_eventuallyEq hev.symm

theorem buchstab_dde_tail {t : ℝ} (h3 : 3 < t) (h4 : t < 4) :
    HasDerivAt (fun x => x * buchstab x) (buchstab (t - 1)) t := by
  have hev : (fun x => 1 + Real.log 2 + ∫ u in (3:ℝ)..x, (1 + Real.log (u - 2)) / (u - 1))
      =ᶠ[nhds t] (fun x => x * buchstab x) := by
    filter_upwards [Ioo_mem_nhds h3 h4] with x hx
    unfold buchstab
    rw [if_neg (by linarith [hx.1]), if_neg (by linarith [hx.1])]
    field_simp [show x ≠ 0 by linarith [hx.1]]
  have hcont : ContinuousAt (fun u : ℝ => (1 + Real.log (u - 2)) / (u - 1)) t := by
    have : t - 1 ≠ 0 := by linarith
    have : t - 2 ≠ 0 := by linarith
    fun_prop (disch := assumption)
  have hcontOn : ContinuousOn (fun u : ℝ => (1 + Real.log (u - 2)) / (u - 1)) (Ioo 2 5) := by
    intro u hu
    apply ContinuousAt.continuousWithinAt
    have : u - 1 ≠ 0 := by linarith [hu.1]
    have : u - 2 ≠ 0 := by linarith [hu.1]
    fun_prop (disch := assumption)
  have hd := (intervalIntegral.integral_hasDerivAt_right (intInt_buchstab_tail h3.le)
    (hcontOn.stronglyMeasurableAtFilter isOpen_Ioo t ⟨by linarith, by linarith⟩) hcont).const_add
      (1 + Real.log 2)
  · have hval : buchstab (t - 1) = (1 + Real.log (t - 2)) / (t - 1) := by
      unfold buchstab
      rw [if_neg (by linarith), if_pos (by linarith), show t - 1 - 1 = t - 2 by ring]
    rw [hval]
    exact hd.congr_of_eventuallyEq hev.symm

end Erdos287.W2984Publication
