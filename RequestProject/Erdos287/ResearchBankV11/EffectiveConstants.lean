import Mathlib

/-!
# Erdős #287 — Research Bank V11 §Q: the effective constant bundle

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`NumericalExternalConstants` is an explicit data structure for the numerical constants that the
external analytic inputs would have to supply (Kloosterman, generalized BV, ordinary BV, SW,
divisor, smoothing, and the log-saving term), each with its power saving `η_i`, the log-power
exponent `A₀` of the log term and the log-loss exponent `C` of the power terms, with positivity
proofs.

**No instance is provided anywhere in this bank**: no numerical values are available.  Unknown
external constants are not numerical activation data.

`symbolicError c X = K_log · X · (log X)^{-A₀} + ∑_i K_i · X^{1-η_i} · (log X)^C`.
-/

namespace Erdos287
namespace ResearchBankV11
namespace EffectiveConstants

/-- **The numerical external constant bundle** (never instantiated in this bank). -/
structure NumericalExternalConstants where
  K_Kloosterman : ℝ
  K_GBV : ℝ
  K_BV : ℝ
  K_SW : ℝ
  K_divisor : ℝ
  K_smoothing : ℝ
  K_log : ℝ
  η_Kloosterman : ℝ
  η_GBV : ℝ
  η_BV : ℝ
  η_SW : ℝ
  η_divisor : ℝ
  η_smoothing : ℝ
  A₀ : ℝ
  C : ℝ
  K_pos : 0 < K_Kloosterman ∧ 0 < K_GBV ∧ 0 < K_BV ∧ 0 < K_SW ∧ 0 < K_divisor ∧
    0 < K_smoothing ∧ 0 < K_log
  η_pos : 0 < η_Kloosterman ∧ 0 < η_GBV ∧ 0 < η_BV ∧ 0 < η_SW ∧ 0 < η_divisor ∧
    0 < η_smoothing
  A₀_pos : 0 < A₀
  C_nonneg : 0 ≤ C

namespace NumericalExternalConstants

variable (c : NumericalExternalConstants)

/-- The six power-saving terms `(K_i, η_i)`. -/
def powerTerms : List (ℝ × ℝ) :=
  [(c.K_Kloosterman, c.η_Kloosterman), (c.K_GBV, c.η_GBV), (c.K_BV, c.η_BV), (c.K_SW, c.η_SW),
    (c.K_divisor, c.η_divisor), (c.K_smoothing, c.η_smoothing)]

theorem powerTerms_length : c.powerTerms.length = 6 := rfl

theorem powerTerms_pos : ∀ Kη ∈ c.powerTerms, 0 < Kη.1 ∧ 0 < Kη.2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := c.K_pos
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := c.η_pos
  intro Kη hKη
  simp only [powerTerms, List.mem_cons, List.mem_nil_iff, or_false] at hKη
  rcases hKη with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by assumption, by assumption⟩

/-- **The symbolic error function.** -/
noncomputable def symbolicError (X : ℝ) : ℝ :=
  c.K_log * X * Real.log X ^ (-c.A₀) +
    (c.powerTerms.map fun Kη => Kη.1 * X ^ (1 - Kη.2) * Real.log X ^ c.C).sum

end NumericalExternalConstants

/-- **The current bank's numerical constants: none.** -/
def currentConstants : Option NumericalExternalConstants := none

theorem currentConstants_eq_none : currentConstants = none := rfl

end EffectiveConstants
end ResearchBankV11
end Erdos287
