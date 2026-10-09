import RequestProject.Erdos287.ResearchBankV21.FiniteSieveSetup

/-!
# Erdős #287 — Research Bank V21 §2: normalized sieve monotonicity

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Kernel-proved finite algebra (LEAN BANK), no analytic provider:

* `normCost_eq_sum_divSum` — for `q_p < 1` the exact identity
  `C_λ(q) = ∑_S a_λ(S) ∏_{p∈S} q_p/(1-q_p)`;
* `normCost_mono` — **monotonicity**: if `0 ≤ q_p ≤ h_p < 1` for every `p` and
  `a_λ(S) ≥ 0` for every `S`, then `C_λ(q) ≤ C_λ(h)`.  The hypothesis used is nonnegativity of
  the DIVISOR SUMS `a_λ(S)`; **no sign condition on the coefficients `λ(A)` is assumed**;
* `normCost_nonneg` — `C_λ(q) ≥ 0` under the same hypothesis.

Firewalls / regressions:
* `signed_coefficient_nonneg_divSum` — a sieve whose coefficient `λ({p}) = -1` is negative but
  whose divisor sums are all `≥ 0` (FINITE REGRESSION: signed λ need not be nonnegative);
* `monotonicity_needs_divSum_nonneg` — without `a_λ ≥ 0` monotonicity fails
  (FINITE REGRESSION).
-/

namespace Erdos287
namespace ResearchBankV21
namespace NormalizedSieveMonotonicity

open Finset FiniteSieveSetup

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- **The exact normalized-functional identity** `C_λ(q) = ∑_S a_λ(S) ∏_{p∈S} q_p/(1-q_p)`. -/
theorem normCost_eq_sum_divSum (lam : Finset P → ℝ) (q : P → ℝ) (hq : ∀ p, q p < 1) :
    normCost lam q = ∑ S : Finset P, divSum lam S * ∏ p ∈ S, odds q p := by
  have hne : ∀ p, (1 - q p) ≠ 0 := fun p => by linarith [hq p]
  rw [sum_divSum_mul]
  have key : ∀ A : Finset P,
      ∑ S : Finset P, (if A ⊆ S then ∏ p ∈ S, odds q p else 0) =
        (∏ p ∈ A, q p) / denom q := by
    intro A
    have h1 := sum_supset_prod A (odds q) (fun _ => (1 : ℝ))
    simp only [Finset.prod_const_one, mul_one] at h1
    rw [h1]
    have hodds : ∀ p, odds q p + 1 = (1 - q p)⁻¹ := fun p => by
      unfold odds; field_simp [hne p]; ring
    simp_rw [hodds]
    unfold odds denom
    rw [← Finset.prod_mul_prod_compl A (fun p => 1 - q p), Finset.prod_div_distrib,
      Finset.prod_inv_distrib]
    have hA : (∏ p ∈ A, (1 - q p)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ => hne p
    have hAc : (∏ p ∈ Aᶜ, (1 - q p)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ => hne p
    field_simp
  simp_rw [key]
  unfold normCost numer
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun A _ => ?_
  ring

omit [Fintype P] [DecidableEq P] in
/-- The odds are monotone on `(-∞,1)`. -/
theorem odds_mono {q h : P → ℝ} (p : P) (hqh : q p ≤ h p) (hh : h p < 1) :
    odds q p ≤ odds h p := by
  unfold odds
  have h1 : 0 < 1 - q p := by linarith
  have h2 : 0 < 1 - h p := by linarith
  rw [div_le_div_iff₀ h1 h2]
  nlinarith

omit [Fintype P] [DecidableEq P] in
theorem odds_nonneg {q : P → ℝ} (p : P) (hq0 : 0 ≤ q p) (hq : q p < 1) : 0 ≤ odds q p := by
  unfold odds
  exact div_nonneg hq0 (by linarith)

/-- **Monotonicity of the normalized sieve functional.**  Uses nonnegativity of the divisor sums
`a_λ(S)` only — the coefficients `λ(A)` may have any sign. -/
theorem normCost_mono (lam : Finset P → ℝ) (hdiv : ∀ S, 0 ≤ divSum lam S) {q h : P → ℝ}
    (hq0 : ∀ p, 0 ≤ q p) (hqh : ∀ p, q p ≤ h p) (hh : ∀ p, h p < 1) :
    normCost lam q ≤ normCost lam h := by
  have hq1 : ∀ p, q p < 1 := fun p => lt_of_le_of_lt (hqh p) (hh p)
  rw [normCost_eq_sum_divSum lam q hq1, normCost_eq_sum_divSum lam h hh]
  refine Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left ?_ (hdiv S)
  exact Finset.prod_le_prod (fun p _ => odds_nonneg p (hq0 p) (hq1 p))
    (fun p _ => odds_mono p (hqh p) (hh p))

/-- `C_λ(q) ≥ 0` when all divisor sums are nonnegative. -/
theorem normCost_nonneg (lam : Finset P → ℝ) (hdiv : ∀ S, 0 ≤ divSum lam S) {q : P → ℝ}
    (hq0 : ∀ p, 0 ≤ q p) (hq : ∀ p, q p < 1) : 0 ≤ normCost lam q := by
  rw [normCost_eq_sum_divSum lam q hq]
  exact Finset.sum_nonneg fun S _ => mul_nonneg (hdiv S)
    (Finset.prod_nonneg fun p _ => odds_nonneg p (hq0 p) (hq p))

/-! ### Regressions on the one-prime universe `P = Unit` -/

theorem unit_univ : (Finset.univ : Finset (Finset Unit)) = {∅, {()}} := by decide

theorem unit_powerset : ({()} : Finset Unit).powerset = {∅, {()}} := by decide

/-- A signed sieve on one prime: `λ(∅) = 1`, `λ({p}) = -1`. -/
def signedLam : Finset Unit → ℝ := fun A => if A = ∅ then 1 else -1

/-- **Firewall: signed coefficients with nonnegative divisor sums.**  `λ({p}) = -1 < 0`, yet
every divisor sum is `≥ 0`, so `normCost_mono` applies although `λ` is not nonnegative. -/
theorem signed_coefficient_nonneg_divSum :
    signedLam {()} < 0 ∧ (∀ S, 0 ≤ divSum signedLam S) := by
  refine ⟨by norm_num [signedLam], fun S => ?_⟩
  have hS : S ∈ (Finset.univ : Finset (Finset Unit)) := Finset.mem_univ _
  rw [unit_univ] at hS
  simp only [Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with rfl | rfl
  · simp [divSum, signedLam]
  · rw [divSum, unit_powerset, Finset.sum_pair (by decide)]
    simp [signedLam]

/-- A sieve with a negative divisor sum: `λ(∅) = 0`, `λ({p}) = -1`. -/
def badLam : Finset Unit → ℝ := fun A => if A = ∅ then 0 else -1

/-- **Regression: monotonicity genuinely needs `a_λ ≥ 0`.**  With `a_λ({p}) = -1`,
`C_λ(0) = 0 > -1 = C_λ(1/2)`. -/
theorem monotonicity_needs_divSum_nonneg :
    divSum badLam {()} < 0 ∧
      normCost badLam (fun _ => 1 / 2) < normCost badLam (fun _ => 0) := by
  refine ⟨by rw [divSum, unit_powerset, Finset.sum_pair (by decide)]; simp [badLam], ?_⟩
  simp only [normCost, numer, denom, unit_univ]
  rw [Finset.sum_pair (by decide)]
  simp [badLam]
  norm_num

end NormalizedSieveMonotonicity
end ResearchBankV21
end Erdos287
