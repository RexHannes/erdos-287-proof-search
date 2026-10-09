import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V14 §A1: fixed functional parameters

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Recorded exactly:

    K = 2^4170,   P = 12 K,   a = 2982,   δ = 1/80,
    μ_F > 350774/10000,   W_F < 559454/10000,   A0 = 2000599/599000.

Kernel-proved exact margins:

    350774/10000 − (A0 · 559454/10000 + 2/5)/11 − 18 = 163216957/2995000000   (`margin_at_bounds`)
    μ_F − (A0 W_F + 2/5)/11 − 18 > 163216957/2995000000                       (`margin_gt`)
    remaining margin after the score-error budget 1/20 > 13466957/2995000000 > 0
                                                                             (`remaining_margin_gt`)

**Firewall.**  The numerical integrals defining `μ_F`, `W_F` are *not* formalized.  Their audited
rational bounds enter only through the input structure `CertifiedFunctionalBounds`, which is
never constructed in the bank.  It carries no arithmetic moment: actual moments `S0, S1` and the
actual pair count live in a different structure (V14 §A10 / V15) and are linked to `μ_F`, `W_F`
only through explicit provider contracts.
-/

namespace Erdos287
namespace ResearchBankV14
namespace BalancedKernelParameters

/-- `K = 2^4170` coordinates. -/
def K : ℕ := 2 ^ 4170

/-- `P = 12 K`. -/
def P : ℕ := 12 * K

/-- `a = 2982`. -/
def aParam : ℕ := 2982

/-- `δ = 1/80`. -/
def delta : ℚ := 1 / 80

/-- Audited rational lower bound for `μ_F`. -/
def muFLower : ℚ := 350774 / 10000

/-- Audited rational upper bound for `W_F`. -/
def WFUpper : ℚ := 559454 / 10000

/-- `A0 = 2000599/599000`. -/
def A0 : ℚ := 2000599 / 599000

/-- Total score-error budget `1/20`. -/
def scoreBudget : ℚ := 1 / 20

/-- The certified margin. -/
def certifiedMargin : ℚ := 163216957 / 2995000000

/-- The remaining margin after the score-error budget. -/
def remainingMargin : ℚ := 13466957 / 2995000000

theorem K_eq : K = 2 ^ 4170 := rfl

theorem K_pos : 0 < K := pow_pos (by norm_num) _

theorem P_eq : P = 12 * K := rfl

/-- `K ≡ 1 (mod 11)` (since `2^10 ≡ 1 (mod 11)` and `10 ∣ 4170`). -/
theorem K_mod_11 : K % 11 = 1 := by
  unfold K
  rw [show (4170 : ℕ) = 10 * 417 from rfl, pow_mul, Nat.pow_mod]
  norm_num

theorem eleven_le_K : 11 ≤ K := by
  rw [K_eq]
  calc (11 : ℕ) ≤ 2 ^ 4 := by norm_num
    _ ≤ 2 ^ 4170 := pow_le_pow_right₀ (by norm_num) (by norm_num)

theorem A0_pos : 0 < A0 := by unfold A0; norm_num

/-- **Exact margin at the audited bounds.** -/
theorem margin_at_bounds :
    muFLower - (A0 * WFUpper + 2 / 5) / 11 - 18 = certifiedMargin := by
  unfold muFLower A0 WFUpper certifiedMargin; norm_num

/-- `163216957/2995000000 − 1/20 = 13466957/2995000000`. -/
theorem budget_split : certifiedMargin - scoreBudget = remainingMargin := by
  unfold certifiedMargin scoreBudget remainingMargin; norm_num

theorem remainingMargin_pos : 0 < remainingMargin := by unfold remainingMargin; norm_num

/-- **Certified functional bounds** (input structure; the integrals themselves are not
formalized).  Never constructed in the bank. -/
structure CertifiedFunctionalBounds where
  /-- The functional first-moment constant `μ_F`. -/
  muF : ℝ
  /-- The functional pair constant `W_F`. -/
  WF : ℝ
  /-- Audited bound `μ_F > 350774/10000`. -/
  muF_gt : ((muFLower : ℚ) : ℝ) < muF
  /-- Audited bound `W_F < 559454/10000`. -/
  WF_lt : WF < ((WFUpper : ℚ) : ℝ)

/-- **Strict margin** from the certified bounds. -/
theorem margin_gt (B : CertifiedFunctionalBounds) :
    ((certifiedMargin : ℚ) : ℝ) < B.muF - (((A0 : ℚ) : ℝ) * B.WF + 2 / 5) / 11 - 18 := by
  have h := margin_at_bounds
  have hA := A0_pos
  have h1 := B.muF_gt
  have h2 := B.WF_lt
  have hA' : (0 : ℝ) < ((A0 : ℚ) : ℝ) := by exact_mod_cast hA
  have h3 : ((A0 : ℚ) : ℝ) * B.WF < ((A0 : ℚ) : ℝ) * ((WFUpper : ℚ) : ℝ) :=
    mul_lt_mul_of_pos_left h2 hA'
  have h' : ((muFLower : ℚ) : ℝ) - (((A0 : ℚ) : ℝ) * ((WFUpper : ℚ) : ℝ) + 2 / 5) / 11 - 18 =
      ((certifiedMargin : ℚ) : ℝ) := by
    rw [← h]; push_cast; ring
  linarith

/-- **Remaining margin after the score-error budget `1/20`.** -/
theorem remaining_margin_gt (B : CertifiedFunctionalBounds) :
    ((remainingMargin : ℚ) : ℝ) <
      B.muF - (((A0 : ℚ) : ℝ) * B.WF + 2 / 5) / 11 - 18 - ((scoreBudget : ℚ) : ℝ) ∧
    (0 : ℝ) < ((remainingMargin : ℚ) : ℝ) := by
  have h := margin_gt B
  have hs : ((certifiedMargin : ℚ) : ℝ) - ((scoreBudget : ℚ) : ℝ) =
      ((remainingMargin : ℚ) : ℝ) := by
    rw [← budget_split]; push_cast; ring
  refine ⟨by linarith, by exact_mod_cast remainingMargin_pos⟩

/-- The score-error budget accommodates the uniform error `η = 1/400` in the three normalized
moments: `η · (1 + 1/11 + 18) ≤ 1/20`. -/
theorem eta_budget : (1 / 400 : ℚ) * (1 + 1 / 11 + 18) ≤ scoreBudget := by
  unfold scoreBudget; norm_num

end BalancedKernelParameters
end ResearchBankV14
end Erdos287
