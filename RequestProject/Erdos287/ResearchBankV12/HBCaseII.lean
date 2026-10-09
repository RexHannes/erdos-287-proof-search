import RequestProject.Erdos287.ResearchBankV12.HBSelectionConcrete
import RequestProject.Erdos287.ResearchBankV12.TypeIIWholeRectangle

/-!
# Erdős #287 — Research Bank V12 §10 (routing): Case II boxes

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

A Case-II selection `ν ∈ [1/8, 1/4]` (a partial-product exponent) fixes the legal factorization
at the original level: `0 ≤ r ≤ r*(ν) = λ − ν + ζ`, `0 ≤ s ≤ s*(ν) = ν − ζ`.  Every such box is
either in `smallBV`, or it is an actual Case-II Type-II box (`CaseIIBox`) on which the §10
whole-rectangle margins hold (`caseII_routed`).  Also: the Case-II rectangle genuinely reaches
outside the BV region (`caseII_reaches_outside_BV`), so the Type-II branch is needed.
-/

namespace Erdos287
namespace ResearchBankV12
namespace HBCaseII

open ConcreteParameters TypeIIWholeRectangle HBSelectionConcrete ResearchBankV10.HBSelection

/-- A legal Case-II box for the selected `ν`. -/
structure LegalCaseIIBox (ν θ r s : ℚ) : Prop where
  θ_nonneg : 0 ≤ θ
  θ_le : θ ≤ theta0
  r_nonneg : 0 ≤ r
  r_le : r ≤ rStar ν
  s_nonneg : 0 ≤ s
  s_le : s ≤ sStar ν

/-- **Case-II routing**: BV, or restored Type-II with the fixed worst-case margins. -/
theorem caseII_routed {l : List HBFactor} {ν θ r s : ℚ} (hsel : CaseIIWitness l ν)
    (hb : LegalCaseIIBox ν θ r s) :
    smallBV θ r s ∨
      (CaseIIBox ν θ r s ∧ 1 / 208 ≤ g1 θ r s ν ∧ 9 / 208 - theta0 ≤ g2 θ r ν ∧
        7 / 208 ≤ g3 θ r ν) := by
  by_cases hbv : smallBV θ r s
  · exact Or.inl hbv
  · have hbox : CaseIIBox ν θ r s :=
      ⟨hb.θ_nonneg, hb.θ_le, hb.r_nonneg, hb.r_le, hb.s_nonneg, hb.s_le, hbv⟩
    exact Or.inr ⟨hbox, worst_case_margins hbox hsel.2.1 hsel.2.2⟩

/-- The top corner of every Case-II rectangle lies outside `smallBV` (so Type II is needed). -/
theorem caseII_reaches_outside_BV {ν θ : ℚ} (hθ : 0 ≤ θ) (hν1 : 1 / 8 ≤ ν) (hν2 : ν ≤ 1 / 4) :
    ¬ smallBV θ (rStar ν) (sStar ν) := by
  have := (ResearchBankV10.HBSupportCoverage.caseII_params concreteParams hθ hν1 hν2).2.2.2.2.2.2.2
  unfold smallBV; rw [rStar_eq_v10, sStar_eq_v10, ← concreteParams_ζ]; linarith

end HBCaseII
end ResearchBankV12
end Erdos287
