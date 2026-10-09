import Mathlib

/-!
# Erdős #287 — post-V71 bank: analytic toolkit (imported and proved prime-counting bounds)

* `chebyshev_upper` — **imported external formal theorem**: Mathlib's
  `Chebyshev.eventually_primeCounting_le` (Chebyshev's upper bound
  `π(x) ≤ (log 4 + ε) x / log x` eventually), specialised to `ε = 1`.
* `primeCounting_lower` — **proved here** from the central binomial coefficient:
  `n · log 4 ≤ (π(2n) + 1) · log(2n)` for `n ≥ 1`.
* `log_le_four_rpow` — `log x ≤ 4 x^{1/4}`.
-/

open Real

namespace Erdos287.PostV71V87

/-- The Chebyshev constant used throughout: `log 4 + 1`. -/
noncomputable def Cpi : ℝ := Real.log 4 + 1

theorem Cpi_pos : 0 < Cpi := by
  unfold Cpi; have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith

/-- **Imported (Mathlib): Chebyshev's upper bound.**  There is `X0 ≥ 2` such that
`π(⌊x⌋) ≤ (log 4 + 1) x / log x` for all real `x ≥ X0`. -/
theorem chebyshev_upper :
    ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ Cpi * x / Real.log x := by
  have h := Chebyshev.eventually_primeCounting_le (ε := 1) one_pos
  rw [Filter.eventually_atTop] at h
  obtain ⟨X0, hX0⟩ := h
  exact ⟨max 2 X0, le_max_left _ _, fun x hx => hX0 x (le_trans (le_max_right _ _) hx)⟩

/-- `C(2n, n) ≤ (2n)^{π(2n)}`. -/
theorem centralBinom_le_pow_primeCounting (n : ℕ) (hn : 0 < n) :
    n.centralBinom ≤ (2 * n) ^ Nat.primeCounting (2 * n) := by
  rw [← Nat.prod_pow_factorization_centralBinom n]
  have hsplit : ∏ p ∈ Finset.range (2 * n + 1), p ^ n.centralBinom.factorization p =
      ∏ p ∈ Nat.primesBelow (2 * n + 1), p ^ n.centralBinom.factorization p := by
    refine (Finset.prod_subset (Finset.filter_subset _ _) (fun p hp hnp => ?_)).symm
    have : ¬ p.Prime := by
      intro hpp; exact hnp (Finset.mem_filter.2 ⟨hp, hpp⟩)
    rw [Nat.factorization_eq_zero_of_not_prime _ this, pow_zero]
  rw [hsplit]
  have hc : (Nat.primesBelow (2 * n + 1)).card = Nat.primeCounting (2 * n) := by
    rw [Nat.primesBelow_card_eq_primeCounting']; rfl
  rw [← hc]
  refine Finset.prod_le_pow_card _ _ _ (fun p _ => ?_)
  unfold Nat.centralBinom
  exact Nat.pow_factorization_choose_le (by omega)

/-- **Proved: Chebyshev-type lower bound.**  `n log 4 ≤ (π(2n) + 1) log(2n)` for `n ≥ 1`. -/
theorem primeCounting_lower (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * Real.log 4 ≤ ((Nat.primeCounting (2 * n) : ℝ) + 1) * Real.log (2 * n) := by
  have h1 := Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
  have h2 := centralBinom_le_pow_primeCounting n hn
  have h3 : 4 ^ n ≤ (2 * n) ^ (Nat.primeCounting (2 * n) + 1) := by
    calc 4 ^ n ≤ 2 * n * n.centralBinom := h1
      _ ≤ 2 * n * (2 * n) ^ Nat.primeCounting (2 * n) := Nat.mul_le_mul_left _ h2
      _ = (2 * n) ^ (Nat.primeCounting (2 * n) + 1) := by ring
  have h4 : ((4 : ℝ)) ^ n ≤ ((2 * n : ℝ)) ^ (Nat.primeCounting (2 * n) + 1) := by
    exact_mod_cast h3
  have h5 := Real.log_le_log (by positivity) h4
  rw [Real.log_pow, Real.log_pow] at h5
  push_cast at h5
  linarith

/-- `log x ≤ 4 x^{1/4}` for `x ≥ 0`. -/
theorem log_le_four_rpow {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
  have := Real.log_le_rpow_div hx (by norm_num : (0 : ℝ) < 1 / 4)
  linarith [show x ^ (1 / 4 : ℝ) / (1 / 4) = 4 * x ^ (1 / 4 : ℝ) by ring]

theorem rpow_quarter_pow_four {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 4 : ℝ)) ^ 4 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

theorem rpow_quarter_sq {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, Real.sqrt_eq_rpow]; norm_num

end Erdos287.PostV71V87
