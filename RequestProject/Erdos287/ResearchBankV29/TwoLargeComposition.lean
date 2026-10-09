import RequestProject.Erdos287.ResearchBankV29.OneLargeComposition

/-!
# Erdős #287 — Research Bank V29 §7.4: two-large branch composition

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

## Audit finding

Identical to the one-large branch: `twoLarge : BranchClassBound Us Ur D2` with `D2`
UNINTERPRETED; no two-large coefficient sequence / modulus is built from the physical source in
V2–V28.  The field is kept as the external-shape `TwoLargeAnalyticProvider`; the identification
`D2 = physical two-large functional` is recorded as missing.

## Proved here (LEAN BANK)

* `twoLarge_sum_split` — box-wise composition (same argument as `oneLarge_sum_split`);
* `four_branch_sum_small` — the four branch class bounds (zero / one-large / two-large /
  boundary) give eventual smallness of the summed functional on every source decomposition with a
  fixed coefficient mass (reuse of the V28 `derived_source_class_provider` and V24
  `distribution_error_small`).
-/

namespace Erdos287
namespace ResearchBankV29
namespace TwoLargeComposition

open ResearchBankV22.IndependentFactorization ResearchBankV28.RepairedAnalyticBundle
open ResearchBankV24.RepairedProvider

/-- **Box-wise composition for the two-large branch** (LEAN BANK). -/
theorem twoLarge_sum_split {Us Ur : ℕ → ℕ → Finset ℕ} {D2 : ℕ → (Finset ℕ → ℝ) → ℝ}
    (P : BranchClassBound Us Ur D2) {ι : Type} [Fintype ι] (c : ι → ℝ) (S : ℕ) :
    ∀ ε > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ g : ι → Finset ℕ → ℝ,
      (∀ i, SourceFactorization (g i) (Us S M) (Ur S M)) →
      |D2 M (fun A => ∑ i, c i * g i A)| ≤ (∑ i, |c i|) * ε :=
  OneLargeComposition.oneLarge_sum_split P c S

/-- **Four-branch smallness** (LEAN CONDITIONAL on the four branch class bounds). -/
theorem four_branch_sum_small {Us Ur : ℕ → ℕ → Finset ℕ} {D0 D1 D2 Db : ℕ → (Finset ℕ → ℝ) → ℝ}
    (h0 : BranchClassBound Us Ur D0) (h1 : BranchClassBound Us Ur D1)
    (h2 : BranchClassBound Us Ur D2) (hb : BranchClassBound Us Ur Db) (S : ℕ)
    (lam : ℕ → Finset ℕ → ℝ) {Cm : ℝ} (hCm : 0 ≤ Cm)
    (hdec : ∀ M, SourceDecomposition (lam M) (Us S M) (Ur S M) Cm) :
    ∀ ε > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀, |sumDE D0 D1 D2 Db M (lam M)| ≤ ε :=
  distribution_error_small (derived_source_class_provider h0 h1 h2 hb) S lam hCm hdec

end TwoLargeComposition
end ResearchBankV29
end Erdos287
