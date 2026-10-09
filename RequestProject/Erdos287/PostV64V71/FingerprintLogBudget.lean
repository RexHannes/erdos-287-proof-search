import RequestProject.Erdos287.PostV64V71.TailClosure

/-!
# Erdős #287 — V68 fingerprint log budget from an explicit Chebyshev upper bound

**Status: LEAN PROVED CONDITIONAL ON EXPLICIT INPUT.**

The research bound `log Ξ_H < 2M/L⁵` (`FingerprintLogBound287`) is reduced, in Lean, to the
classical explicit Chebyshev upper bound in lcm form

  `LcmUpperBound12 : ∀ n, lcm(1,…,n) ≤ exp(6n/5)`   (i.e. `ψ(n) ≤ 1.2 n`).

`LcmUpperBound12` is **KNOWN EXTERNAL MATHEMATICS / NOT FORMALISED LOCALLY** (Rosser–Schoenfeld
give `ψ(x) < 1.03883 x`); it is *not* available in Mathlib, whose bound
`ψ(x) ≤ log 4 · x + 2√x log x` (`Chebyshev.psi_le`) is too weak for this margin
(`log 4 / log 2 = 2` exactly hits the target constant `2`).  It is a named proposition used only
as a hypothesis; it is never asserted.

Integer-first chain (all proved):

* `Xi_le_BH_pow_pred` — `Ξ_H ≤ B_H^(2^H - 1)`;
* `BH_le_mul_lcm` — `B_H ≤ H · lcm(1,…,H)`;
* `log_Xi_le` — `log Ξ_H ≤ (2^H - 1)(log H + log lcm(1,…,H))`;
* `two_pow_Hcan_le` — `2^{Hcan M} ≤ M / (log M)⁶`;
* `fingerprintLogBound_of_lcm` — `LcmUpperBound12 → FingerprintLogBound287`;
* `determinant_supply_implies_no_tail'` — `DeterminantSupply287 → LcmUpperBound12 →
  NoCounterexampleAbove (2^1500)`.
-/

open scoped BigOperators

namespace Erdos287.PostV64V71

open Erdos287

/-- **External input (not formalised locally)**: the explicit Chebyshev upper bound
`ψ(n) ≤ 1.2 n` in lcm form, `lcm(1,…,n) ≤ exp(6n/5)` for all `n`. -/
def LcmUpperBound12 : Prop := ∀ n : ℕ, (lcmTo n : ℝ) ≤ Real.exp (6 / 5 * n)

/-- `Ξ_H ≤ B_H^(2^H - 1)` for `H ≥ 1`. -/
theorem Xi_le_BH_pow_pred {H : ℕ} (hH : 1 ≤ H) : Xi H ≤ BH H ^ (2 ^ H - 1) :=
  le_trans (Xi_le_BH_pow H)
    (Nat.pow_le_pow_right (one_le_BH hH) (Nat.sub_le_sub_right (card_recipSums_le H) 1))

/-- `B_H ≤ H · lcm(1,…,H)`. -/
theorem BH_le_mul_lcm (H : ℕ) : BH H ≤ H * lcmTo H := by
  unfold BH
  calc ∑ j ∈ Finset.Icc 1 H, lcmTo H / j ≤ ∑ _j ∈ Finset.Icc 1 H, lcmTo H :=
        Finset.sum_le_sum fun j _ => Nat.div_le_self _ _
    _ = H * lcmTo H := by simp

/-- `log Ξ_H ≤ (2^H - 1)(log H + log lcm(1,…,H))` for `H ≥ 1`. -/
theorem log_Xi_le {H : ℕ} (hH : 1 ≤ H) :
    Real.log (Xi H) ≤ ((2 : ℝ) ^ H - 1) * (Real.log H + Real.log (lcmTo H)) := by
  have h1 : (Xi H : ℝ) ≤ (BH H : ℝ) ^ (2 ^ H - 1) := by exact_mod_cast Xi_le_BH_pow_pred hH
  have hBpos : (0 : ℝ) < BH H := by have := one_le_BH hH; exact_mod_cast this
  have h2 : Real.log (Xi H) ≤ ((2 ^ H - 1 : ℕ) : ℝ) * Real.log (BH H) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by exact_mod_cast Xi_pos H) h1
  have hcast : ((2 ^ H - 1 : ℕ) : ℝ) = (2 : ℝ) ^ H - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
  rw [hcast] at h2
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have hL0 : (0 : ℝ) < lcmTo H := by exact_mod_cast lcmTo_pos H
  have h3 : Real.log (BH H) ≤ Real.log H + Real.log (lcmTo H) := by
    rw [← Real.log_mul hH0.ne' hL0.ne']
    apply Real.log_le_log hBpos
    exact_mod_cast BH_le_mul_lcm H
  have h4 : (0 : ℝ) ≤ (2 : ℝ) ^ H - 1 := by
    have : (1 : ℝ) ≤ 2 ^ H := one_le_pow₀ (by norm_num)
    linarith
  exact le_trans h2 (mul_le_mul_of_nonneg_left h3 h4)

/-- `2^{Hcan M} ≤ M/(log M)⁶` for `M ≥ 2^1500`. -/
theorem two_pow_Hcan_le {M : ℕ} (hM : 2 ^ 1500 ≤ M) :
    (2 : ℝ) ^ Hcan M ≤ (M : ℝ) / Real.log M ^ 6 := by
  have hL := log_ge_of_large hM
  set L := Real.log M with hLdef
  have hM0 : (0 : ℝ) < M := by
    have : (0 : ℕ) < M := lt_of_lt_of_le (by positivity) hM
    exact_mod_cast this
  have hl2 := Real.log_two_gt_d9
  have h6 := log_le_div_twelve hL
  have hnn : 0 ≤ (L - 6 * Real.log L) / Real.log 2 := by
    apply div_nonneg _ (by linarith); linarith
  have hH : (Hcan M : ℝ) ≤ (L - 6 * Real.log L) / Real.log 2 := by
    unfold Hcan; rw [← hLdef]; exact Nat.floor_le hnn
  have hHlog : (Hcan M : ℝ) * Real.log 2 ≤ L - 6 * Real.log L := by
    rwa [le_div_iff₀ (by linarith)] at hH
  have e1 : (2 : ℝ) ^ Hcan M = Real.exp (Hcan M * Real.log 2) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), mul_comm]
  have e2 : (M : ℝ) / L ^ 6 = Real.exp (L - 6 * Real.log L) := by
    rw [Real.exp_sub, Real.exp_log hM0,
      show (6 : ℝ) * Real.log L = Real.log (L ^ 6) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity)]
  rw [e1, e2]
  exact Real.exp_le_exp.2 hHlog

/-- **`LcmUpperBound12 → FingerprintLogBound287`** (LEAN PROVED). -/
theorem fingerprintLogBound_of_lcm (hlcm : LcmUpperBound12) : FingerprintLogBound287 := by
  intro M hM
  obtain ⟨hH1, hH, -⟩ := canonical_height_facts hM
  have hL := log_ge_of_large hM
  set L := Real.log M with hLdef
  set H := Hcan M
  have hl2 := Real.log_two_gt_d9
  have h6 := log_le_div_twelve hL
  have hM0 : (0 : ℝ) < M := by
    have : (0 : ℕ) < M := lt_of_lt_of_le (by positivity) hM
    exact_mod_cast this
  -- `H log 2 ≤ L`
  have hHlog : (H : ℝ) * Real.log 2 ≤ L := by
    have hnn : 0 ≤ (L - 6 * Real.log L) / Real.log 2 := by
      apply div_nonneg _ (by linarith); linarith
    have : (H : ℝ) ≤ (L - 6 * Real.log L) / Real.log 2 := by
      show (Hcan M : ℝ) ≤ _
      unfold Hcan; rw [← hLdef]; exact Nat.floor_le hnn
    rw [le_div_iff₀ (by linarith)] at this
    have : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
    linarith
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH1
  -- `log H + log lcm(1..H) < 2L`
  have hlogH : Real.log H ≤ Real.log (3 / 2) + Real.log L := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log hH0 hH
  have hlog32 : Real.log (3 / 2 : ℝ) < 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
    linarith
  have hlcmH : Real.log (lcmTo H) ≤ 6 / 5 * H := by
    have hpos : (0 : ℝ) < lcmTo H := by exact_mod_cast lcmTo_pos H
    calc Real.log (lcmTo H) ≤ Real.log (Real.exp (6 / 5 * H)) := Real.log_le_log hpos (hlcm H)
      _ = 6 / 5 * H := Real.log_exp _
  have hX : Real.log H + Real.log (lcmTo H) < 2 * L := by
    have hHle : (H : ℝ) ≤ L / Real.log 2 := by
      rw [le_div_iff₀ (by linarith)]; exact hHlog
    have : (6 / 5 : ℝ) * H ≤ 6 / 5 * (L / Real.log 2) := by linarith
    have h7 : 6 / 5 * (L / Real.log 2) ≤ 1732 / 1000 * L := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hX0 : 0 ≤ Real.log H + Real.log (lcmTo H) := by
    have := Real.log_natCast_nonneg H
    have := Real.log_natCast_nonneg (lcmTo H)
    linarith
  have hlogXi := log_Xi_le hH1
  have h2pow := two_pow_Hcan_le hM
  have h2pos : (0 : ℝ) < 2 ^ H := by positivity
  calc Real.log (Xi H) ≤ ((2 : ℝ) ^ H - 1) * (Real.log H + Real.log (lcmTo H)) := hlogXi
    _ ≤ (2 : ℝ) ^ H * (Real.log H + Real.log (lcmTo H)) := by nlinarith
    _ < (2 : ℝ) ^ H * (2 * L) := mul_lt_mul_of_pos_left hX h2pos
    _ ≤ (M : ℝ) / L ^ 6 * (2 * L) :=
        mul_le_mul_of_nonneg_right h2pow (by linarith)
    _ = 2 * (M : ℝ) / L ^ 5 := by
        have : L ≠ 0 := by linarith
        field_simp

/-- **Tail theorem with a standard external input.**  `DeterminantSupply287` (OPEN) and the
explicit Chebyshev bound `LcmUpperBound12` (external) imply no counterexample above `2^1500`. -/
theorem determinant_supply_implies_no_tail' (hS : DeterminantSupply287)
    (hlcm : LcmUpperBound12) : NoCounterexampleAbove (2 ^ 1500) :=
  determinant_supply_implies_no_tail hS (fingerprintLogBound_of_lcm hlcm)

end Erdos287.PostV64V71
