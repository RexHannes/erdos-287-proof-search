import RequestProject.Erdos287.ResearchBankV29.NonzeroPruning
import RequestProject.Erdos287.ResearchBankV25.LocalizationContract

/-!
# Erdős #287 — Research Bank V29 §7.1: zero-frequency / BDH branch composition

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

## Audit finding

In V28 the zero-frequency branch enters ONLY as the field
`zeroFreq : BranchClassBound Us Ur D0` of `FinalAnalyticProviders`, for an UNINTERPRETED functional
`D0 : ℕ → (Finset ℕ → ℝ) → ℝ`.  The V25 chain (fixed-modulus centering, correction aggregation,
conditioned-energy projection, `zero_frequency_localized_bound`) bounds the explicit sum
`FullSum f Qs κ rq Ns γ` of a `ZeroFreqData`, but no declaration of V2–V28 defines `D0` in terms of
a `ZeroFreqData` built from the physical pair source.  Hence the zero branch bound cannot be
*derived* for `D0`: the `zeroFreq` field is kept, classified EXTERNAL-SHAPE (a masked SW/BDH class
bound) with the INTERNAL identification `D0 = physical zero-frequency functional` missing.

## Proved here (LEAN BANK)

* `branchClassBound_zero` — the zero functional satisfies every `BranchClassBound` (vacuity: the
  field constrains nothing while `D0` is uninterpreted);
* `branchClassBound_of_uniform` — the generic composition step "linear functional + a uniform
  eventual bound on every source-factorized weight ⟹ `BranchClassBound`";
* `zero_frequency_eventually_le` — the V25 localized bound, re-packaged: for every `A`, eventually
  `‖FullSum‖ ≤ √(Σ τ_J) √(C₁ Bnd/log^A) + C₂ MN/log^A` (direct reuse of
  `zero_frequency_localized_bound`, no new estimate).
-/

namespace Erdos287
namespace ResearchBankV29
namespace ZeroBranchComposition

open ResearchBankV22.IndependentFactorization ResearchBankV28.RepairedAnalyticBundle
open ResearchBankV25.LocalizationContract ResearchBankV25.CorrectionAggregation

/-- **Zero functional is a branch class bound** (LEAN BANK; vacuity witness). -/
theorem branchClassBound_zero (Us Ur : ℕ → ℕ → Finset ℕ) :
    BranchClassBound Us Ur (fun _ _ => 0) :=
  ⟨fun _ _ _ _ _ => by simp, fun _ _ hε => ⟨0, fun _ _ _ _ => by simpa using hε.le⟩⟩

/-- **Generic branch composition step** (LEAN BANK). -/
theorem branchClassBound_of_uniform {Us Ur : ℕ → ℕ → Finset ℕ} {DEb : ℕ → (Finset ℕ → ℝ) → ℝ}
    (hlin : ∀ M {ι : Type} [Fintype ι] (c : ι → ℝ) (g : ι → Finset ℕ → ℝ),
      DEb M (fun A => ∑ i, c i * g i A) = ∑ i, c i * DEb M (g i))
    (bound : ℕ → ℕ → ℝ) (hb : ∀ S M g, SourceFactorization g (Us S M) (Ur S M) → |DEb M g| ≤ bound S M)
    (hsmall : ∀ S, ∀ ε > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀, bound S M ≤ ε) :
    BranchClassBound Us Ur DEb := by
  refine ⟨hlin, fun S ε hε => ?_⟩
  obtain ⟨M₀, hM₀⟩ := hsmall S ε hε
  exact ⟨M₀, fun M hM g hg => (hb S M g hg).trans (hM₀ M hM)⟩

/-- **V25 zero-frequency bound, re-packaged** (LEAN CONDITIONAL on the V25 `BDHEnergyProvider`
and `MaskedSWProvider`; direct reuse). -/
theorem zero_frequency_eventually_le {f : ℕ} [NeZero f] {c : ℤ} {J : ℕ} (Z : ZeroFreqData f c J)
    {Bnd MN : ℝ → ℝ} (hB : BDHEnergyProvider f J Z.Ns Z.γ Z.U Bnd)
    (hM : MaskedSWProvider f c J Z.Qs Z.Ns Z.γ MN) (A : ℕ) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∃ x0 : ℝ, ∀ x ≥ x0,
      ‖FullSum f (Z.Qs x) (Z.κ x) (Z.rq x) (Z.Ns x) (Z.γ x)‖ ≤
        Real.sqrt (∑ q ∈ Z.Qs x, tauJ J q) * Real.sqrt (C₁ * Bnd x / Real.log x ^ A) +
          C₂ * MN x / Real.log x ^ A :=
  zero_frequency_localized_bound Z hB hM A

end ZeroBranchComposition
end ResearchBankV29
end Erdos287
