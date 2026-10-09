import RequestProject.Erdos287.ResearchBankV29.ZeroBranchComposition
import RequestProject.Erdos287.ResearchBankV26.HBBranchCoverage

/-!
# Erdős #287 — Research Bank V29 §7.2: Type-II branch composition

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

## Audit finding

The V28 bundle has NO separate Type-II field: the Type-II (bilinear, DI) contribution is the
nonzero-frequency functional `DEnz`, which enters through
`nonzero : ∀ S τ M, NonzeroCleanRealization DIClass M (DEnz M (LamFam … S τ M)) Cnz`.
The V26 identities (Heath-Brown, rough convolution, product boxes, singleton bins, dyadic map,
trichotomy) are proved for explicit finite sums, but no declaration maps the physical pair source
through them to `DEnz`, and no clean state is generated (see `PhysicalCleanState`).  Therefore
the "branch already satisfies source contract" content is NOT eliminated; it is exactly the
`nonzero` field, kept inside the internal glue owner (`ProviderElimination`).

## Proved here (LEAN BANK / LEAN CONDITIONAL)

* `typeII_coverage` — the V26 structural trichotomy restated: every normalized HB exponent vector
  with `0 < α ≤ 2/5` is Type-II, one-large or two-large (so the three branch fields of V28 cover
  every source box once a source map exists);
* `typeII_branch_small_of_realization` — the V28 derived nonzero theorem, restated as the Type-II
  branch bound: DI provider + clean realizations ⟹ eventually `[DEnz]_+ ≤ ε`.
-/

namespace Erdos287
namespace ResearchBankV29
namespace TypeIIBranchComposition

open ResearchBankV26.HBBranchCoverage ResearchBankV27.DISpectral
  ResearchBankV28.RepairedAnalyticBundle

/-- **HB branch coverage** (LEAN BANK, V26 reuse). -/
theorem typeII_coverage {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : ι → ℝ)
    (he : ∀ i ∈ s, 0 ≤ e i) (hsum : ∑ i ∈ s, e i = 1) {α : ℝ} (hα : 0 < α) (hα' : α ≤ 2 / 5) :
    TypeII s e α ∨ OneLarge s e α ∨ TwoLarge s e α :=
  branch_trichotomy s e he hsum hα hα'

/-- **Type-II branch bound from clean realizations** (LEAN CONDITIONAL; V28 reuse). -/
theorem typeII_branch_small_of_realization {DIClass : KloostermanData → Prop} {Cnz : ℝ}
    (hDI : DISpectralProvider (1 / 1100) DIClass) (val : ℕ → ℝ)
    (hreal : ∀ M : ℕ, NonzeroCleanRealization DIClass M (val M) Cnz) :
    ∀ ε > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀, max (val M) 0 ≤ ε :=
  nonzero_branch_small hDI val hreal

end TypeIIBranchComposition
end ResearchBankV29
end Erdos287
