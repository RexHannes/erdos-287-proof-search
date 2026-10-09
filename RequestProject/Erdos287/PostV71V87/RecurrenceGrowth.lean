import RequestProject.Erdos287.PostV71V87.AnalyticToolkit

/-!
# Erdős #287 — the recurrence growth function `g(L) = L log L / log log L`

Elementary real-analysis facts about `gRec L = L · log L / log log L` used by the repaired
V87 recurrence theorem:

* `gRec_mono`     — monotone on `[e^e, ∞)`;
* `gRec_half`     — `g(x/2) ≥ g(x)/4` for `x ≥ e^{2e}`;
* `gRec_le_sq`    — `g(x) ≤ x²` for `x ≥ e^e`;
* `gRec_nonneg`.
-/

open Real

namespace Erdos287.PostV71V87

/-- `g(L) = L · log L / log log L`. -/
noncomputable def gRec (L : ℝ) : ℝ := L * Real.log L / Real.log (Real.log L)

/-- `u / log u` is monotone on `[e, ∞)`. -/
theorem div_log_mono {u v : ℝ} (hu : Real.exp 1 ≤ u) (huv : u ≤ v) :
    u / Real.log u ≤ v / Real.log v := by
  have hv : Real.exp 1 ≤ v := le_trans hu huv
  have hupos : 0 < u := lt_of_lt_of_le (Real.exp_pos 1) hu
  have hvpos : 0 < v := lt_of_lt_of_le (Real.exp_pos 1) hv
  have hlu : 1 ≤ Real.log u := by rw [Real.le_log_iff_exp_le hupos]; exact hu
  have hlv : 1 ≤ Real.log v := by rw [Real.le_log_iff_exp_le hvpos]; exact hv
  have h := Real.log_div_self_antitoneOn hu hv huv
  simp only at h
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  rw [div_le_div_iff₀ hvpos hupos] at h
  linarith

theorem log_ge_e_of {x : ℝ} (hx : Real.exp (Real.exp 1) ≤ x) : Real.exp 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) hx)]; exact hx

theorem gRec_eq (x : ℝ) : gRec x = x * (Real.log x / Real.log (Real.log x)) := by
  unfold gRec; ring

theorem gRec_nonneg {x : ℝ} (hx : Real.exp (Real.exp 1) ≤ x) : 0 ≤ gRec x := by
  have h1 := log_ge_e_of hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hl : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos 1) h1
  have hll : 1 ≤ Real.log (Real.log x) := by rw [Real.le_log_iff_exp_le hl]; exact h1
  unfold gRec; positivity

/-- `g` is monotone on `[e^e, ∞)`. -/
theorem gRec_mono {x y : ℝ} (hx : Real.exp (Real.exp 1) ≤ x) (hxy : x ≤ y) : gRec x ≤ gRec y := by
  have hy : Real.exp (Real.exp 1) ≤ y := le_trans hx hxy
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have h1 := log_ge_e_of hx
  have h2 : Real.log x ≤ Real.log y := Real.log_le_log hxpos hxy
  have hφ := div_log_mono h1 h2
  rw [gRec_eq, gRec_eq]
  have hl : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos 1) h1
  have hll : 1 ≤ Real.log (Real.log x) := by rw [Real.le_log_iff_exp_le hl]; exact h1
  have hφ0 : 0 ≤ Real.log x / Real.log (Real.log x) := by positivity
  exact mul_le_mul hxy hφ hφ0 (by linarith)

/-- `g(x) ≤ x²` for `x ≥ e^e`. -/
theorem gRec_le_sq {x : ℝ} (hx : Real.exp (Real.exp 1) ≤ x) : gRec x ≤ x ^ 2 := by
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have h1 := log_ge_e_of hx
  have hl : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos 1) h1
  have hll : 1 ≤ Real.log (Real.log x) := by rw [Real.le_log_iff_exp_le hl]; exact h1
  have hlx : Real.log x ≤ x := by have := Real.log_le_sub_one_of_pos hxpos; linarith
  rw [gRec_eq]
  have : Real.log x / Real.log (Real.log x) ≤ x := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  calc x * (Real.log x / Real.log (Real.log x)) ≤ x * x :=
        mul_le_mul_of_nonneg_left this hxpos.le
    _ = x ^ 2 := by ring

/-- `g(x/2) ≥ g(x)/4` once `x ≥ e^{2e}`. -/
theorem gRec_half {x : ℝ} (hx : Real.exp (2 * Real.exp 1) ≤ x) : gRec x / 4 ≤ gRec (x / 2) := by
  have he := Real.exp_pos 1
  have he1 : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  set u := Real.log x with hudef
  have hu : 2 * Real.exp 1 ≤ u := by rw [hudef, Real.le_log_iff_exp_le hxpos]; exact hx
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hlog2 : Real.log (x / 2) = u - Real.log 2 := Real.log_div hxpos.ne' (by norm_num)
  have hhalf : u / 2 ≤ Real.log (x / 2) := by rw [hlog2]; linarith
  have hu2e : Real.exp 1 ≤ u / 2 := by linarith
  have hφ1 := div_log_mono hu2e hhalf
  have hupos : 0 < u := by linarith
  have hlu2 : 0 < Real.log (u / 2) := Real.log_pos (by linarith)
  have hlu2le : Real.log (u / 2) ≤ Real.log u := Real.log_le_log (by linarith) (by linarith)
  have hφ2 : (u / 2) / Real.log u ≤ (u / 2) / Real.log (u / 2) :=
    div_le_div_of_nonneg_left (by linarith) hlu2 hlu2le
  have hlu : 0 < Real.log u := lt_of_lt_of_le hlu2 hlu2le
  rw [gRec_eq, gRec_eq, ← hudef]
  have hkey : u / Real.log u / 2 ≤ Real.log (x / 2) / Real.log (Real.log (x / 2)) := by
    have : u / Real.log u / 2 = (u / 2) / Real.log u := by ring
    linarith
  calc x * (u / Real.log u) / 4 = (x / 2) * (u / Real.log u / 2) := by ring
    _ ≤ (x / 2) * (Real.log (x / 2) / Real.log (Real.log (x / 2))) :=
        mul_le_mul_of_nonneg_left hkey (by linarith)

end Erdos287.PostV71V87
