import RequestProject.Erdos287.W2984Publication.ScalarOmega

/-!
# W2.984 — the outward-rational certificate `Ω₁ - Ω₂ + Ω₃ < 3.984`

**ERDŐS #287 REMAINS OPEN.  Kernel-checked real arithmetic; no floating point.**

Chain (all steps are theorems of this subtree):

1. `Omega1_sub_Omega2` : `Ω₁ - Ω₂ = 4 - 2J`, `J = ∫_1^{3/2} log v (1/(5/2-v) - 1/(v+1)) dv`;
2. `J_lower` : `J ≥ 36653/55125 + (312/343) log(3/2) - (4552/1029) log(5/4)`;
3. `Omega3_le` : `Ω₃ ≤ 14 log(3/2) - 28/5` (Buchstab bound `ω ≤ 3/5` on `[5/3,4]`);
4. hence `Ω₁ - Ω₂ + Ω₃ ≤ c₀ + (4178/343) log(3/2) + (9104/1029) log(5/4)` with
   `c₀ = 4 - 28/5 - 73306/55125` (`pairConstant_le_logs`);
5. `log_three_halves_le` (14 Mercator terms + tail), `log_five_fourths_le` (8 terms + tail);
6. **`pairConstant_le_certificate`** :
   `Ω₁ - Ω₂ + Ω₃ ≤ 796682507263/200000000000 = 3.983412536315`;
7. **`pairConstant_lt`** : `Ω₁ - Ω₂ + Ω₃ < 3.984`, and the explicit room
   `3.984 - 796682507263/200000000000 = 117492737/200000000000` (`certificate_room`).

The true value is `≈ 3.98329` (non-rigorous midpoint quadrature, *not* used anywhere).
-/

namespace Erdos287.W2984Publication

open Real

/-- The V92 outward-rational certificate value `3.983412536315`. -/
noncomputable def chenCertificate : ℝ := 796682507263 / 200000000000

/-- Merikoski's pair constant at `α = 1/7`, `β = 3/14`. -/
noncomputable def pairConstant : ℝ := Omega1 (1/7) - Omega2 (1/7) (3/14) + Omega3 (1/7) (3/14)

theorem pairConstant_le_logs :
    pairConstant ≤ (4 - 28/5 - 73306/55125) + 4178/343 * Real.log (3/2) +
      9104/1029 * Real.log (5/4) := by
  unfold pairConstant
  have h1 := Omega1_sub_Omega2
  have h2 := J_lower
  have h3 := Omega3_le
  linarith

/-- **The certificate.** `Ω₁ - Ω₂ + Ω₃ ≤ 796682507263/200000000000`. -/
theorem pairConstant_le_certificate : pairConstant ≤ chenCertificate := by
  have h := pairConstant_le_logs
  have h1 := log_three_halves_le
  have h2 := log_five_fourths_le
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h1 h2
  norm_num at h1 h2
  unfold chenCertificate
  linarith

/-- The certificate value is `< 3.984`. -/
theorem chenCertificate_lt : chenCertificate < 3.984 := by
  unfold chenCertificate; norm_num

/-- The explicit fixed room left for the `O(δ)` and `o(1)` errors. -/
theorem certificate_room : (3.984 : ℝ) - chenCertificate = 117492737 / 200000000000 := by
  unfold chenCertificate; norm_num

/-- **`Ω₁ - Ω₂ + Ω₃ < 3.984`** at `α = 1/7`, `β = 3/14`. -/
theorem pairConstant_lt : pairConstant < 3.984 :=
  lt_of_le_of_lt pairConstant_le_certificate chenCertificate_lt

/-- Merikoski's published inequality `Ω₁ - Ω₂ + Ω₃ < 3.99` follows. -/
theorem pairConstant_lt_merikoski : pairConstant < 3.99 := by
  have := pairConstant_lt; linarith

/-! ### Explicit `O(δ)` budget (see `AFFINE_CHEN_TRANSFER_W2984.md`, §12)

The written proof identifies the `δ`-dependence of the three analytic lemmas as level losses:
`C₁ = 392/9` (`F_lin` at `7/2 - 28δ`, `|F_lin'| ≤ 2e^γ/9` on `[3, 7/2]`),
`C₂ = 196 log(3/2)` (`f_lin` is `e^γ`-Lipschitz from below, `∑_{Y<p≤Z} 1/p ~ log(3/2)`),
`C₃ ≤ 5/2` (Selberg support `θ = 1/4 - 2δ`, `θ⁻¹ ≤ 4 + 64δ`, times `Ω₃/2 ≤ 0.0383`).
The kernel facts below check the arithmetic of the resulting budget; the *identification* of
the constants is paper-level (recorded as a constant-extraction obligation). -/

/-- `f_lin(s) ≤ e^γ (s - 2)` on `[2, 4]` (Lipschitz-from-below input for `C₂`). -/
theorem flin_le_lipschitz {s : ℝ} (h2 : 2 ≤ s) : flin s ≤ eγ * (s - 2) := by
  unfold flin
  have hs : 0 < s := by linarith
  have hl : Real.log (s - 1) ≤ s - 2 := by
    have := Real.log_le_sub_one_of_pos (show 0 < s - 1 by linarith); linarith
  have he := eγ_pos
  rw [div_le_iff₀ hs]
  have h1 : 2 * eγ * Real.log (s - 1) ≤ eγ * (2 * (s - 2)) := by nlinarith
  have h2 : eγ * (2 * (s - 2)) ≤ eγ * (s - 2) * s := by
    have : 0 ≤ eγ * (s - 2) := mul_nonneg he.le (by linarith)
    nlinarith
  linarith

/-- The total `C_err = C₁ + C₂/2 + C₃/2 ≤ 392/9 + 98 log(3/2) + 5/4 < 85`. -/
theorem explicit_Cerr_lt : (392 : ℝ) / 9 + 98 * Real.log (3/2) + 5/4 < 85 := by
  have h := log_three_halves_le
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linarith

/-- **Explicit `δ₀ = 6·10⁻⁶`:** `85 δ₀ < 3.984 - 3.983412536315`. -/
theorem explicit_delta0 : (85 : ℝ) * (6 / 1000000) < 3.984 - chenCertificate := by
  unfold chenCertificate; norm_num

end Erdos287.W2984Publication
