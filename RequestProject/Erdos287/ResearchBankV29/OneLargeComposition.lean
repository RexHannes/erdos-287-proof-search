import RequestProject.Erdos287.ResearchBankV29.TypeIIBranchComposition

/-!
# Erdős #287 — Research Bank V29 §7.3: one-large branch composition

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

## Audit finding

The one-large branch enters V28 only as `oneLarge : BranchClassBound Us Ur D1` with `D1`
UNINTERPRETED.  No coefficient sequence / modulus of the one-large branch is constructed from the
physical source anywhere in V2–V28, and no separate one-large analytic theorem with literal
hypotheses (sequence, modulus range, coefficient bound) exists in the bank.  The field is
therefore kept as the external-shape provider `OneLargeAnalyticProvider` (a class bound over
source-factorized weights), and the identification `D1 = physical one-large functional` is
recorded as missing.

## Proved here (LEAN BANK)

* `oneLarge_sum_split` — the one-large contribution may be split over any finite family of
  sub-boxes with the class bound applied to each (linearity + triangle inequality), i.e. the
  composition step from "every box satisfies the provider hypotheses" to the branch bound.
-/

namespace Erdos287
namespace ResearchBankV29
namespace OneLargeComposition

open ResearchBankV22.IndependentFactorization ResearchBankV28.RepairedAnalyticBundle

/-- **Box-wise composition of a branch class bound** (LEAN BANK). -/
theorem oneLarge_sum_split {Us Ur : ℕ → ℕ → Finset ℕ} {D1 : ℕ → (Finset ℕ → ℝ) → ℝ}
    (P : BranchClassBound Us Ur D1) {ι : Type} [Fintype ι] (c : ι → ℝ) (S : ℕ) :
    ∀ ε > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ g : ι → Finset ℕ → ℝ,
      (∀ i, SourceFactorization (g i) (Us S M) (Ur S M)) →
      |D1 M (fun A => ∑ i, c i * g i A)| ≤ (∑ i, |c i|) * ε := by
  intro ε hε
  obtain ⟨M₀, hM₀⟩ := P.class_bound S ε hε
  refine ⟨M₀, fun M hM g hg => ?_⟩
  rw [P.linear]
  calc |∑ i, c i * D1 M (g i)| ≤ ∑ i, |c i * D1 M (g i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |c i| * |D1 M (g i)| := by simp [abs_mul]
    _ ≤ ∑ i, |c i| * ε := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hM₀ M hM (g i) (hg i)) (abs_nonneg _)
    _ = (∑ i, |c i|) * ε := by rw [Finset.sum_mul]

end OneLargeComposition
end ResearchBankV29
end Erdos287
