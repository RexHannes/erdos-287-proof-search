import Mathlib

/-!
# Erdős #287 — Research Bank V11 §Q: the generic power-to-log conversion

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`power_to_log` (conservative, fully explicit): for `K, η, A > 0`, `C ≥ 0`, any natural `n` with
`C + A + 1 ≤ n`, and `X > 0` with

  `log X ≥ 1`  and  `log X ≥ K · n! / η^n`,

one has `K · X^{1-η} · (log X)^C ≤ X · (log X)^{-A}`.

The proof uses only `exp(y) ≥ y^n / n!` and `t^{C+A} ≤ t^{n-1}` for `t ≥ 1`.  The threshold
`powerToLogThreshold K η n = max 1 (K · n!/η^n)` is an explicit function of explicit numbers; for an
unevaluated symbolic `K` it is **not** a numerical activation threshold.
-/

namespace Erdos287
namespace ResearchBankV11
namespace PowerToLog

open Real

/-- The explicit log-threshold. -/
noncomputable def powerToLogThreshold (K η : ℝ) (n : ℕ) : ℝ := max 1 (K * n.factorial / η ^ n)

/-- **Generic power-to-log conversion.** -/
theorem power_to_log {K η A C : ℝ} (hK : 0 < K) (hη : 0 < η) (hA : 0 < A) (hC : 0 ≤ C)
    {n : ℕ} (hn : C + A + 1 ≤ n) {X : ℝ} (hX : 0 < X) (h1 : 1 ≤ Real.log X)
    (hthr : K * n.factorial / η ^ n ≤ Real.log X) :
    K * X ^ (1 - η) * Real.log X ^ C ≤ X * Real.log X ^ (-A) := by
  set t := Real.log X with ht
  have ht0 : 0 < t := by linarith
  have hηn : 0 < η ^ n := pow_pos hη n
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  -- `X^η = exp(η t) ≥ (η t)^n / n!`
  have hXη : X ^ η = Real.exp (η * t) := by rw [Real.rpow_def_of_pos hX, mul_comm]
  have hexp : (η * t) ^ n / n.factorial ≤ X ^ η := by
    rw [hXη]; exact Real.pow_div_factorial_le_exp _ (by positivity) n
  -- `t^{C+A} ≤ t^n / t`
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have htCA : t ^ (C + A) ≤ t ^ ((n : ℝ) - 1) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  have htn : t ^ ((n : ℝ) - 1) = t ^ n / t := by
    rw [Real.rpow_sub ht0, Real.rpow_one, Real.rpow_natCast]
  -- `K t^n / t ≤ (η t)^n / n!`
  have hkey : K * (t ^ n / t) ≤ (η * t) ^ n / n.factorial := by
    have : K * n.factorial / η ^ n ≤ t := hthr
    rw [div_le_iff₀ hηn] at this
    rw [mul_pow, le_div_iff₀ hfac]
    have htn0 : 0 ≤ t ^ n / t := by positivity
    calc K * (t ^ n / t) * n.factorial = (K * n.factorial) * (t ^ n / t) := by ring
      _ ≤ (t * η ^ n) * (t ^ n / t) := by gcongr
      _ = η ^ n * t ^ n := by field_simp
  have hmain : K * t ^ (C + A) ≤ X ^ η :=
    calc K * t ^ (C + A) ≤ K * (t ^ n / t) := by rw [← htn]; gcongr
      _ ≤ (η * t) ^ n / n.factorial := hkey
      _ ≤ X ^ η := hexp
  -- rewrite the goal
  have hX1η : X ^ (1 - η) = X / X ^ η := by
    rw [Real.rpow_sub hX, Real.rpow_one]
  have htA : t ^ (-A) = 1 / t ^ A := by rw [Real.rpow_neg ht0.le, one_div]
  have hXη0 : 0 < X ^ η := Real.rpow_pos_of_pos hX η
  have htA0 : 0 < t ^ A := Real.rpow_pos_of_pos ht0 A
  rw [hX1η, htA]
  have hCA : t ^ (C + A) = t ^ C * t ^ A := Real.rpow_add ht0 C A
  rw [hCA] at hmain
  have e1 : K * (X / X ^ η) * t ^ C = X * (K * t ^ C) / X ^ η := by ring
  have e2 : X * (1 / t ^ A) = X / t ^ A := by ring
  rw [e1, e2, div_le_div_iff₀ hXη0 htA0]
  have := mul_le_mul_of_nonneg_left hmain hX.le
  calc X * (K * t ^ C) * t ^ A = X * (K * (t ^ C * t ^ A)) := by ring
    _ ≤ X * X ^ η := this

/-- The threshold form: `log X ≥ powerToLogThreshold K η n` suffices. -/
theorem power_to_log_of_threshold {K η A C : ℝ} (hK : 0 < K) (hη : 0 < η) (hA : 0 < A)
    (hC : 0 ≤ C) {n : ℕ} (hn : C + A + 1 ≤ n) {X : ℝ} (hX : 0 < X)
    (hthr : powerToLogThreshold K η n ≤ Real.log X) :
    K * X ^ (1 - η) * Real.log X ^ C ≤ X * Real.log X ^ (-A) :=
  power_to_log hK hη hA hC hn hX (le_trans (le_max_left _ _) hthr)
    (le_trans (le_max_right _ _) hthr)

end PowerToLog
end ResearchBankV11
end Erdos287
