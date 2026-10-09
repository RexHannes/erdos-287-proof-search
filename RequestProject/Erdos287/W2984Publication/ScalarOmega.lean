import RequestProject.Erdos287.W2984Publication.ScalarFunctions

/-!
# W2.984 — Merikoski's constants `Ω₁, Ω₂, Ω₃` at `α = 1/7`, `β = 3/14`

**ERDŐS #287 REMAINS OPEN.  Exact real analysis.**

Definitions (Merikoski v3, proof of Proposition 12):

* `Ω₁ = F_lin(1/(2α)) / (α e^γ)`;
* `Ω₂ = (1/(2α e^γ)) ∫_α^β f_lin((1/2 - t)/α) dt/t`;
* `Ω₃ = 2 ∫_{α<u₁<u₂<u₃<β} ω((1-u₁-u₂-u₃)/u₂) du₁du₂du₃/(u₁u₂²u₃)` (iterated integral).

Proved:

* `Omega1_seventh` — Merikoski's display `Ω₁ = 4 + 4∫_3^{7/2} log(s-2)/(s-1) ds`, in the form
  `4 + 4∫_1^{3/2} log v/(v+1) dv`;
* `Omega2_seventh` — `Ω₂ = 2∫_1^{3/2} log v (1/(v+1) + 1/(5/2-v)) dv` (substitution `v = 5/2 - 7t`
  and partial fractions);
* **`Omega1_sub_Omega2`** — `Ω₁ - Ω₂ = 4 - 2∫_1^{3/2} log v (1/(5/2-v) - 1/(v+1)) dv`;
* **`Omega3_le`** — `Ω₃ ≤ 14 log(3/2) - 28/5`, from `buchstab_le` and the exact evaluation of
  `∫∫∫ du/(u₁u₂²u₃) = (35/3) log(3/2) - 14/3` over the simplex;
* **`J_lower`** — `∫_1^{3/2} log v (1/(5/2-v) - 1/(v+1)) dv ≥ 36653/55125 + (312/343) log(3/2)
  - (4552/1029) log(5/4)` (from `log v ≥ 2y + 2y³/3`, `y = (v-1)/(v+1)`, and an explicit
  antiderivative);
* `log_three_halves_le`, `log_five_fourths_le` — rational upper bounds from the Mercator series
  with explicit tail.
-/

namespace Erdos287.W2984Publication

open Real intervalIntegral MeasureTheory Set

noncomputable def Omega1 (α : ℝ) : ℝ := Flin (1 / (2 * α)) / (α * eγ)

noncomputable def Omega2 (α β : ℝ) : ℝ :=
  1 / (2 * α * eγ) * ∫ t in α..β, flin ((1 / 2 - t) / α) / t

theorem uIcc_one_three_halves {v : ℝ} (hv : v ∈ uIcc (1:ℝ) (3/2)) : 1 ≤ v ∧ v ≤ 3/2 := by
  rw [uIcc_of_le (by norm_num)] at hv; exact hv

theorem intInt_log_div_add_one :
    IntervalIntegrable (fun v : ℝ => Real.log v / (v + 1)) volume 1 (3/2) := by
  apply ContinuousOn.intervalIntegrable
  intro v hv
  obtain ⟨h1, h2⟩ := uIcc_one_three_halves hv
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div (Real.continuousAt_log (by linarith)) (by fun_prop) (by linarith)

theorem intInt_log_div_sub :
    IntervalIntegrable (fun v : ℝ => Real.log v / (5/2 - v)) volume 1 (3/2) := by
  apply ContinuousOn.intervalIntegrable
  intro v hv
  obtain ⟨h1, h2⟩ := uIcc_one_three_halves hv
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div (Real.continuousAt_log (by linarith)) (by fun_prop) (by linarith)

theorem Omega1_seventh :
    Omega1 (1/7) = 4 + 4 * ∫ v in (1:ℝ)..(3/2), Real.log v / (v + 1) := by
  have h72 : (1:ℝ) / (2 * (1/7)) = 7/2 := by norm_num
  unfold Omega1 Flin
  rw [h72, if_neg (by norm_num)]
  have hI : (∫ u in (3:ℝ)..(7/2), flin (u - 1)) =
      2 * eγ * ∫ v in (1:ℝ)..(3/2), Real.log v / (v + 1) := by
    rw [← intervalIntegral.integral_const_mul]
    have := intervalIntegral.integral_comp_sub_right
      (fun v : ℝ => 2 * eγ * (Real.log v / (v + 1))) (a := 3) (b := 7/2) 2
    rw [show (3:ℝ) - 2 = 1 by norm_num, show (7/2:ℝ) - 2 = 3/2 by norm_num] at this
    rw [← this]
    apply intervalIntegral.integral_congr
    intro u _
    simp only [flin]
    rw [show u - 1 - 1 = u - 2 by ring, show u - 2 + 1 = u - 1 by ring]
    ring
  rw [hI]
  have := eγ_pos
  field_simp
  ring

theorem Omega2_seventh :
    Omega2 (1/7) (3/14) =
      2 * ((∫ v in (1:ℝ)..(3/2), Real.log v / (v + 1)) +
        ∫ v in (1:ℝ)..(3/2), Real.log v / (5/2 - v)) := by
  unfold Omega2
  set g : ℝ → ℝ := fun v => 2 * eγ * Real.log v / ((v + 1) * ((5/2 - v) / 7)) with hg
  have h1 : (∫ t in (1/7:ℝ)..(3/14), flin ((1 / 2 - t) / (1/7)) / t) =
      ∫ t in (1/7:ℝ)..(3/14), g (5/2 - 7 * t) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [flin, hg]
    have e1 : (1 / 2 - t) / (1 / 7 : ℝ) - 1 = 5/2 - 7 * t := by ring
    have e2 : (1 / 2 - t) / (1 / 7 : ℝ) = 5/2 - 7 * t + 1 := by ring
    have e3 : (5 / 2 - (5 / 2 - 7 * t)) / 7 = t := by ring
    rw [e1, e2, e3, div_div]
  rw [h1, intervalIntegral.integral_comp_sub_mul g (by norm_num : (7:ℝ) ≠ 0)]
  norm_num
  have h2 : (∫ v in (1:ℝ)..(3/2), g v) =
      ∫ v in (1:ℝ)..(3/2), (7 * eγ) * (2 / 7 * 2) *
        (Real.log v / (v + 1) + Real.log v / (5/2 - v)) := by
    apply intervalIntegral.integral_congr
    intro v hv
    obtain ⟨hv1, hv2⟩ := uIcc_one_three_halves hv
    simp only [hg]
    have : v + 1 ≠ 0 := by linarith
    have : (5:ℝ)/2 - v ≠ 0 := by linarith
    have : (5:ℝ) - v * 2 ≠ 0 := by linarith
    have : (5:ℝ) - 2 * v ≠ 0 := by linarith
    field_simp
    ring
  rw [h2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add intInt_log_div_add_one intInt_log_div_sub]
  have := eγ_pos
  field_simp

/-- **Merikoski's `Ω₁ - Ω₂` at `α = 1/7`, `β = 3/14`, in the user's normal form.** -/
theorem Omega1_sub_Omega2 :
    Omega1 (1/7) - Omega2 (1/7) (3/14) =
      4 - 2 * ∫ v in (1:ℝ)..(3/2), Real.log v * (1 / (5/2 - v) - 1 / (v + 1)) := by
  rw [Omega1_seventh, Omega2_seventh]
  have : (∫ v in (1:ℝ)..(3/2), Real.log v * (1 / (5/2 - v) - 1 / (v + 1))) =
      (∫ v in (1:ℝ)..(3/2), Real.log v / (5/2 - v)) -
        ∫ v in (1:ℝ)..(3/2), Real.log v / (v + 1) := by
    rw [← intervalIntegral.integral_sub intInt_log_div_sub intInt_log_div_add_one]
    apply intervalIntegral.integral_congr
    intro v _
    simp only
    ring
  rw [this]
  ring

noncomputable def Omega3 (α β : ℝ) : ℝ :=
  2 * ∫ u₁ in α..β, ∫ u₂ in u₁..β, ∫ u₃ in u₂..β,
    buchstab ((1 - u₁ - u₂ - u₃) / u₂) / (u₁ * u₂ ^ 2 * u₃)

/-- Monotonicity of interval integrals without integrability of the smaller function. -/
theorem intervalIntegral_le_of_nonneg_of_le {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (h0 : ∀ x ∈ Icc a b, 0 ≤ f x)
    (h : ∀ x ∈ Icc a b, f x ≤ g x) : (∫ x in a..b, f x) ≤ ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  apply integral_mono_of_nonneg
  · exact (ae_restrict_iff' measurableSet_Ioc).2
      (Filter.Eventually.of_forall fun x hx => h0 x (Ioc_subset_Icc_self hx))
  · exact hg.1
  · exact (ae_restrict_iff' measurableSet_Ioc).2
      (Filter.Eventually.of_forall fun x hx => h x (Ioc_subset_Icc_self hx))

/-- The `Ω₃` argument stays in `[5/3, 4]` on the simplex `1/7 ≤ u₁ ≤ u₂ ≤ u₃ ≤ 3/14`. -/
theorem omega3_arg_mem {u₁ u₂ u₃ : ℝ} (h1 : 1/7 ≤ u₁) (h12 : u₁ ≤ u₂) (h23 : u₂ ≤ u₃)
    (h3 : u₃ ≤ 3/14) : (1 - u₁ - u₂ - u₃) / u₂ ∈ Icc (5/3 : ℝ) 4 := by
  have hu2 : 0 < u₂ := by linarith
  constructor
  · rw [le_div_iff₀ hu2]; linarith
  · rw [div_le_iff₀ hu2]; linarith

/-- Inner bound. -/
theorem omega3_inner_le {u₁ u₂ : ℝ} (h1 : 1/7 ≤ u₁) (h12 : u₁ ≤ u₂) (h2 : u₂ ≤ 3/14) :
    (∫ u₃ in u₂..(3/14), buchstab ((1 - u₁ - u₂ - u₃) / u₂) / (u₁ * u₂ ^ 2 * u₃)) ≤
      3 / (5 * u₁ * u₂ ^ 2) * (Real.log (3/14) - Real.log u₂) := by
  have hu1 : 0 < u₁ := by linarith
  have hu2 : 0 < u₂ := by linarith
  have key : (∫ u₃ in u₂..(3/14), 3 / (5 * u₁ * u₂ ^ 2) * u₃⁻¹) =
      3 / (5 * u₁ * u₂ ^ 2) * (Real.log (3/14) - Real.log u₂) := by
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hu2 (by norm_num),
      Real.log_div (by norm_num) (ne_of_gt hu2)]
  rw [← key]
  apply intervalIntegral_le_of_nonneg_of_le h2
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le h2] at hx
    apply ContinuousAt.continuousWithinAt
    have : x ≠ 0 := by linarith [hx.1]
    have : x ^ 2 ≠ 0 := by positivity
    have : 5 * x ≠ 0 := by positivity
    fun_prop (disch := assumption)
  · intro x hx
    have hm := omega3_arg_mem h1 h12 hx.1 hx.2
    have := buchstab_nonneg (le_trans (by norm_num) hm.1)
    have : 0 < x := by linarith [hx.1]
    positivity
  · intro x hx
    have hm := omega3_arg_mem h1 h12 hx.1 hx.2
    have hb := buchstab_le hm
    have hx0 : 0 < x := by linarith [hx.1]
    have hd : 0 < u₁ * u₂ ^ 2 * x := by positivity
    calc buchstab ((1 - u₁ - u₂ - x) / u₂) / (u₁ * u₂ ^ 2 * x)
        ≤ (3/5) / (u₁ * u₂ ^ 2 * x) := div_le_div_of_nonneg_right hb hd.le
      _ = 3 / (5 * u₁ * u₂ ^ 2) * x⁻¹ := by field_simp

theorem omega3_inner_nonneg {u₁ u₂ : ℝ} (h1 : 1/7 ≤ u₁) (h12 : u₁ ≤ u₂) (h2 : u₂ ≤ 3/14) :
    0 ≤ ∫ u₃ in u₂..(3/14), buchstab ((1 - u₁ - u₂ - u₃) / u₂) / (u₁ * u₂ ^ 2 * u₃) := by
  apply intervalIntegral.integral_nonneg h2
  intro x hx
  have hm := omega3_arg_mem h1 h12 hx.1 hx.2
  have := buchstab_nonneg (le_trans (by norm_num) hm.1)
  have : 0 < u₁ := by linarith
  have : 0 < u₂ := by linarith
  have : 0 < x := by linarith [hx.1]
  positivity

/-- Antiderivative used in the middle integral: `d/du [(1 - log β + log u)/u] = (log β - log u)/u²`. -/
theorem hasDerivAt_mid {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun u => (1 - Real.log (3/14) + Real.log u) / u)
      ((Real.log (3/14) - Real.log u) / u ^ 2) u := by
  have := (((hasDerivAt_log (ne_of_gt hu)).const_add (1 - Real.log (3/14)))).div
    (hasDerivAt_id u) (ne_of_gt hu)
  convert this using 1
  simp only [id]
  field_simp
  ring

theorem omega3_middle_le {u₁ : ℝ} (h1 : 1/7 ≤ u₁) (h2 : u₁ ≤ 3/14) :
    (∫ u₂ in u₁..(3/14), ∫ u₃ in u₂..(3/14),
        buchstab ((1 - u₁ - u₂ - u₃) / u₂) / (u₁ * u₂ ^ 2 * u₃)) ≤
      3 / (5 * u₁) * (14/3 - (1 - Real.log (3/14) + Real.log u₁) / u₁) := by
  have hu1 : 0 < u₁ := by linarith
  have key : (∫ u₂ in u₁..(3/14), 3 / (5 * u₁) * ((Real.log (3/14) - Real.log u₂) / u₂ ^ 2)) =
      3 / (5 * u₁) * (14/3 - (1 - Real.log (3/14) + Real.log u₁) / u₁) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun u => (1 - Real.log (3/14) + Real.log u) / u)]
    · congr 1; norm_num
    · intro x hx
      rw [uIcc_of_le h2] at hx
      exact hasDerivAt_mid (by linarith [hx.1])
    · apply ContinuousOn.intervalIntegrable
      intro x hx
      rw [uIcc_of_le h2] at hx
      apply ContinuousAt.continuousWithinAt
      have : x ≠ 0 := by linarith [hx.1]
      have : x ^ 2 ≠ 0 := by positivity
      have : 5 * x ≠ 0 := by positivity
      fun_prop (disch := assumption)
  rw [← key]
  apply intervalIntegral_le_of_nonneg_of_le h2
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le h2] at hx
    apply ContinuousAt.continuousWithinAt
    have : x ≠ 0 := by linarith [hx.1]
    have : x ^ 2 ≠ 0 := by positivity
    have : 5 * x ≠ 0 := by positivity
    fun_prop (disch := assumption)
  · intro x hx
    exact omega3_inner_nonneg h1 hx.1 hx.2
  · intro x hx
    have := omega3_inner_le h1 hx.1 hx.2
    have hx0 : 0 < x := by linarith [hx.1]
    calc _ ≤ 3 / (5 * u₁ * x ^ 2) * (Real.log (3/14) - Real.log x) := this
      _ = 3 / (5 * u₁) * ((Real.log (3/14) - Real.log x) / x ^ 2) := by field_simp

theorem omega3_middle_nonneg {u₁ : ℝ} (h1 : 1/7 ≤ u₁) (h2 : u₁ ≤ 3/14) :
    0 ≤ ∫ u₂ in u₁..(3/14), ∫ u₃ in u₂..(3/14),
        buchstab ((1 - u₁ - u₂ - u₃) / u₂) / (u₁ * u₂ ^ 2 * u₃) := by
  apply intervalIntegral.integral_nonneg h2
  intro x hx
  exact omega3_inner_nonneg h1 hx.1 hx.2

/-- Outer antiderivative `K(u) = log u/β + (2 - log β + log u)/u` with `β = 3/14`. -/
theorem hasDerivAt_outer {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun u => Real.log u * (14/3) + (2 - Real.log (3/14) + Real.log u) / u)
      (3 / 5 * 0 + (14/3 / u + (Real.log (3/14) - Real.log u - 1) / u ^ 2)) u := by
  have h1 := (hasDerivAt_log (ne_of_gt hu)).mul_const (14/3)
  have h2 := (((hasDerivAt_log (ne_of_gt hu)).const_add (2 - Real.log (3/14)))).div
    (hasDerivAt_id u) (ne_of_gt hu)
  convert h1.add h2 using 1
  simp only [id]
  field_simp
  ring

/-- **`Ω₃ ≤ 14 log(3/2) - 28/5`** at `α = 1/7`, `β = 3/14`, from `ω ≤ 3/5`. -/
theorem Omega3_le : Omega3 (1/7) (3/14) ≤ 14 * Real.log (3/2) - 28/5 := by
  unfold Omega3
  have key : (∫ u₁ in (1/7:ℝ)..(3/14),
      3 / (5 * u₁) * (14/3 - (1 - Real.log (3/14) + Real.log u₁) / u₁)) =
      7 * Real.log (3/2) - 14/5 := by
    have e : ∀ u₁ ∈ uIcc (1/7:ℝ) (3/14),
        3 / (5 * u₁) * (14/3 - (1 - Real.log (3/14) + Real.log u₁) / u₁) =
          3 / 5 * (14/3 / u₁ + (Real.log (3/14) - Real.log u₁ - 1) / u₁ ^ 2) := by
      intro u₁ hu
      rw [uIcc_of_le (by norm_num)] at hu
      have : u₁ ≠ 0 := by linarith [hu.1]
      field_simp
      ring
    rw [intervalIntegral.integral_congr e, intervalIntegral.integral_const_mul]
    have hint : (∫ u in (1/7:ℝ)..(3/14), 14/3 / u + (Real.log (3/14) - Real.log u - 1) / u ^ 2)
        = (Real.log (3/14) * (14/3) + (2 - Real.log (3/14) + Real.log (3/14)) / (3/14)) -
          (Real.log (1/7) * (14/3) + (2 - Real.log (3/14) + Real.log (1/7)) / (1/7)) := by
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun u => Real.log u * (14/3) + (2 - Real.log (3/14) + Real.log u) / u)
        (f' := fun u => 3 / 5 * 0 + (14/3 / u + (Real.log (3/14) - Real.log u - 1) / u ^ 2))
        (a := 1/7) (b := 3/14) ?_ ?_
      · simpa using this
      · intro x hx
        rw [uIcc_of_le (by norm_num)] at hx
        exact hasDerivAt_outer (by linarith [hx.1])
      · apply ContinuousOn.intervalIntegrable
        intro x hx
        rw [uIcc_of_le (by norm_num)] at hx
        apply ContinuousAt.continuousWithinAt
        have : x ≠ 0 := by linarith [hx.1]
        have : x ^ 2 ≠ 0 := by positivity
        fun_prop (disch := assumption)
    rw [hint]
    have e2 : Real.log (3/14) = Real.log (3/2) + Real.log (1/7) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    rw [e2]
    ring
  have hle : (∫ u₁ in (1/7:ℝ)..(3/14), ∫ u₂ in u₁..(3/14), ∫ u₃ in u₂..(3/14),
      buchstab ((1 - u₁ - u₂ - u₃) / u₂) / (u₁ * u₂ ^ 2 * u₃)) ≤ 7 * Real.log (3/2) - 14/5 := by
    rw [← key]
    apply intervalIntegral_le_of_nonneg_of_le (by norm_num)
    · apply ContinuousOn.intervalIntegrable
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      apply ContinuousAt.continuousWithinAt
      have : x ≠ 0 := by linarith [hx.1]
      have : x ^ 2 ≠ 0 := by positivity
      have : 5 * x ≠ 0 := by positivity
      fun_prop (disch := assumption)
    · intro x hx
      exact omega3_middle_nonneg hx.1 hx.2
    · intro x hx
      exact omega3_middle_le hx.1 hx.2
  linarith

/-- `log v ≥ 2y + 2y³/3`, `y = (v-1)/(v+1)`, for `v ≥ 1` (first two atanh terms). -/
theorem log_ge_atanh2 {v : ℝ} (hv : 1 ≤ v) :
    2 * ((v - 1) / (v + 1)) + 2 / 3 * ((v - 1) / (v + 1)) ^ 3 ≤ Real.log v := by
  set y := (v - 1) / (v + 1) with hy
  have hv1 : 0 < v + 1 := by linarith
  have hy0 : 0 ≤ y := div_nonneg (by linarith) hv1.le
  have hy1 : y < 1 := by rw [hy, div_lt_one hv1]; linarith
  have habs : |y| < 1 := by rw [abs_of_nonneg hy0]; exact hy1
  have hS := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hle := sum_le_hasSum (Finset.range 2) (fun i _ => by positivity) hS
  have h1 : 1 + y = 2 * v / (v + 1) := by rw [hy]; field_simp; ring
  have h2 : 1 - y = 2 / (v + 1) := by rw [hy]; field_simp; ring
  have hlog : Real.log (1 + y) - Real.log (1 - y) = Real.log v := by
    rw [h1, h2, ← Real.log_div (by positivity) (by positivity)]
    congr 1; field_simp
  rw [hlog] at hle
  simp [Finset.sum_range_succ] at hle
  norm_num at hle
  linarith

/-- The rational-function minorant of the `Ω₁ - Ω₂` integrand. -/
noncomputable def gJ (v : ℝ) : ℝ :=
  (2 * ((v - 1) / (v + 1)) + 2 / 3 * ((v - 1) / (v + 1)) ^ 3) * (1 / (5/2 - v) - 1 / (v + 1))

/-- Its antiderivative. -/
noncomputable def GJ (v : ℝ) : ℝ :=
  -(4344 * v ^ 2 + 6588 * v + 3028) / (441 * (v + 1) ^ 3) - 312 / 343 * Real.log (5/2 - v)
    - 4552 / 1029 * Real.log (v + 1)

theorem hasDerivAt_GJ {v : ℝ} (h1 : 0 < v + 1) (h2 : 0 < 5/2 - v) : HasDerivAt GJ (gJ v) v := by
  have hA : HasDerivAt (fun v : ℝ => -(4344 * v ^ 2 + 6588 * v + 3028))
      (-(4344 * (2 * v) + 6588)) v := by
    have := ((hasDerivAt_pow 2 v).const_mul 4344).add ((hasDerivAt_id v).const_mul 6588)
    have := (this.add_const 3028).neg
    convert this using 1; simp
  have hB : HasDerivAt (fun v : ℝ => 441 * (v + 1) ^ 3) (441 * (3 * (v + 1) ^ 2)) v := by
    have := ((hasDerivAt_id v).add_const 1).pow 3
    have := this.const_mul 441
    convert this using 1; simp
  have hC : HasDerivAt (fun v : ℝ => Real.log (5/2 - v)) (-1 / (5/2 - v)) v := by
    have := ((hasDerivAt_id v).const_sub (5/2)).log (ne_of_gt h2)
    convert this using 1
  have hD : HasDerivAt (fun v : ℝ => Real.log (v + 1)) (1 / (v + 1)) v := by
    have := ((hasDerivAt_id v).add_const 1).log (ne_of_gt h1)
    convert this using 1
  have hB0 : 441 * (v + 1) ^ 3 ≠ 0 := by positivity
  have := ((hA.div hB hB0).sub (hC.const_mul (312 / 343))).sub (hD.const_mul (4552 / 1029))
  unfold GJ
  convert this using 1
  unfold gJ
  have : v + 1 ≠ 0 := ne_of_gt h1
  have : (5:ℝ)/2 - v ≠ 0 := ne_of_gt h2
  have : (5:ℝ) - 2 * v ≠ 0 := by linarith
  have : (5:ℝ) - v * 2 ≠ 0 := by linarith
  field_simp
  ring

theorem integral_gJ :
    (∫ v in (1:ℝ)..(3/2), gJ v) =
      36653 / 55125 + 312 / 343 * Real.log (3/2) - 4552 / 1029 * Real.log (5/4) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := GJ)]
  · unfold GJ
    have e1 : Real.log (5/2 - 3/2 : ℝ) = 0 := by norm_num
    have e2 : Real.log (5/2 - 1 : ℝ) = Real.log (3/2) := by norm_num
    have e3 : Real.log (3/2 + 1 : ℝ) = Real.log (5/4) + Real.log 2 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have e4 : Real.log (1 + 1 : ℝ) = Real.log 2 := by norm_num
    rw [e1, e2, e3, e4]
    ring
  · intro v hv
    rw [uIcc_of_le (by norm_num)] at hv
    exact hasDerivAt_GJ (by linarith [hv.1]) (by linarith [hv.2])
  · apply ContinuousOn.intervalIntegrable
    intro v hv
    rw [uIcc_of_le (by norm_num)] at hv
    apply ContinuousAt.continuousWithinAt
    unfold gJ
    have : v + 1 ≠ 0 := by linarith [hv.1]
    have : (5:ℝ)/2 - v ≠ 0 := by linarith [hv.2]
    fun_prop (disch := assumption)

/-- The `Ω₁ - Ω₂` integral is at least the closed form. -/
theorem J_lower :
    36653 / 55125 + 312 / 343 * Real.log (3/2) - 4552 / 1029 * Real.log (5/4) ≤
      ∫ v in (1:ℝ)..(3/2), Real.log v * (1 / (5/2 - v) - 1 / (v + 1)) := by
  rw [← integral_gJ]
  apply intervalIntegral.integral_mono_on (by norm_num)
  · apply ContinuousOn.intervalIntegrable
    intro v hv
    rw [uIcc_of_le (by norm_num)] at hv
    apply ContinuousAt.continuousWithinAt
    unfold gJ
    have : v + 1 ≠ 0 := by linarith [hv.1]
    have : (5:ℝ)/2 - v ≠ 0 := by linarith [hv.2]
    fun_prop (disch := assumption)
  · apply ContinuousOn.intervalIntegrable
    intro v hv
    rw [uIcc_of_le (by norm_num)] at hv
    apply ContinuousAt.continuousWithinAt
    have : v + 1 ≠ 0 := by linarith [hv.1]
    have : (5:ℝ)/2 - v ≠ 0 := by linarith [hv.2]
    have : v ≠ 0 := by linarith [hv.1]
    fun_prop (disch := assumption)
  · intro v hv
    unfold gJ
    have hw : 0 ≤ 1 / (5/2 - v) - 1 / (v + 1) := by
      rw [sub_nonneg]
      apply one_div_le_one_div_of_le (by linarith [hv.2]) (by linarith [hv.1])
    exact mul_le_mul_of_nonneg_right (log_ge_atanh2 hv.1) hw

/-- Rational upper bound for `log (3/2)`. -/
theorem log_three_halves_le :
    Real.log (3/2) ≤ (∑ i ∈ Finset.range 14, (1/3:ℝ) ^ (i + 1) / (i + 1)) +
      (1/3:ℝ) ^ 15 / (1 - 1/3) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 1/3) (by norm_num) 14
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/3)] at h
  have e : Real.log (1 - 1/3) = - Real.log (3/2) := by
    rw [← Real.log_inv]; norm_num
  rw [e] at h
  have := (abs_le.1 h).1
  linarith

/-- Rational upper bound for `log (5/4)`. -/
theorem log_five_fourths_le :
    Real.log (5/4) ≤ (∑ i ∈ Finset.range 8, (1/5:ℝ) ^ (i + 1) / (i + 1)) +
      (1/5:ℝ) ^ 9 / (1 - 1/5) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 1/5) (by norm_num) 8
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/5)] at h
  have e : Real.log (1 - 1/5) = - Real.log (5/4) := by
    rw [← Real.log_inv]; norm_num
  rw [e] at h
  have := (abs_le.1 h).1
  linarith

end Erdos287.W2984Publication
