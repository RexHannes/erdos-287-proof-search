import RequestProject.Erdos287.ResearchBankV30.FullPairComposition

/-!
# Erdős #287 — Research Bank V30 §15: same-source chain

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

## What IS established (LEAN CONDITIONAL, `same_source_end_to_end`)

At the level of the objects that exist in the bank, ONE physical source `(τC, W)` feeds every
consumer: `S0 τC W` (principal normalization), `S1 τC W` (first moment) and `Pair τC W` (the pair
count majorized by the glue owner's actual-measure decomposition) — no model sequence replaces
`Pair τC W` anywhere in the final chain, and all branch functionals are evaluated at the SAME
weight `LamFam S τ M`.

## What is NOT established — SEMANTIC MISMATCH (SUCCESS D)

The task asks to track the source identity through the tensor/cell split, fixed-state split, HB
split, dyadic/fine boxes, colour split and clean-state extraction.  In V2–V28 these splits are
proved as identities about EXPLICIT finite sums (V25 centering, V26 HB/boxes/bins, V27 colour
orbits), but **no declaration applies them to `Pair τC W`**: the branch functionals
`D0, D1, D2, Db, DEnz` are uninterpreted parameters, linked to `Pair` only by the glue owner's
`tensor.decomp` inequality.  `same_source_not_established` proves that the four branch fields,
the DI field and the nonzero realization are all satisfied by the ZERO functionals with the empty
DI class — so nothing in the bank forces the branch functionals to be the physical branch sums.

**First mismatch:** the zero-frequency functional `D0` (first branch in the chain) is not
defined from the physical source `(τC, W)`; the same holds for `D1, D2, Db, DEnz`.
-/

namespace Erdos287
namespace ResearchBankV30
namespace SameSourceChain

open ResearchBankV16.RouteCConsumer
open ResearchBankV14.ConditionalAsymptoticImplication (S0Contract S1Contract)
open ResearchBankV23.PrincipalEuler ResearchBankV24.RepairedRouteCBaseline
open ResearchBankV27.DISpectral ResearchBankV28.RepairedAnalyticBundle
open ResearchBankV29.ProviderElimination

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Same source end to end** (LEAN CONDITIONAL, at the level of existing objects). -/
theorem same_source_end_to_end {τC : FixedTupleC V} {W : WeightSystem τC} {K : ℕ} {h : ℕ → ℝ}
    {F : ℝ → ℝ} {E : Finset ℕ} {Psm Prd : ℕ → ℝ → Finset ℕ} {lev X : ℝ → ℝ}
    {wτ : ℝ → ℝ → ℕ → ℝ} {r : ℕ} {Sd : ResearchBankV23.SingularFactors.SingularData} {LF I : ℝ}
    {N Li : ℕ → ℝ} {phiW : ℝ} {model : ℕ → ℕ → PrincipalModel h} {Kh : ℕ} {EAB : ℕ → ℝ}
    {Us Ur : ℕ → ℕ → Finset ℕ} {D0 D1 D2 Db DEnz : ℕ → (Finset ℕ → ℝ) → ℝ} {Ct Cnz err : ℝ}
    {muF : ℝ} {DIClass : KloostermanData → Prop}
    (Mn : MinimalExternalAnalyticProviders τC W K h F Psm Prd lev X wτ r Sd LF I N Li phiW model
      Kh EAB Us Ur D0 D1 D2 Db muF DIClass)
    (Gl : InternalGlueOwner τC W h E Psm Prd lev X wτ N Li phiW model EAB D0 D1 D2 Db DEnz Ct Cnz
      err DIClass) :
    S0Contract (S0 τC W) N ∧ S1Contract (S1 τC W) N muF ∧
      ∀ S τ M, Pair τC W M / N M ≤
        (model S M).Mnew (pref Li phiW N M) (LamFam E Psm Prd lev X wτ S τ M) +
          |sumDE D0 D1 D2 Db M (LamFam E Psm Prd lev X wτ S τ M)| +
          max (DEnz M (LamFam E Psm Prd lev X wτ S τ M)) 0 + Ct * Real.sqrt |EAB M| + 90 + err :=
  ⟨Mn.euler.normalization_agreement, Mn.s1, Gl.tensor.decomp⟩

/-- **The same-source chain is NOT established by the bank** (LEAN BANK): the zero functionals
with the empty DI class satisfy every branch field, the DI field and the nonzero realization. -/
theorem same_source_not_established (Us Ur : ℕ → ℕ → Finset ℕ) :
    BranchClassBound Us Ur (fun _ _ => 0) ∧
      DISpectralProvider (1 / 1100) (fun _ => False) ∧
      ∀ M : ℕ, NonzeroCleanRealization (fun _ => False) (M : ℝ) 0 0 :=
  ⟨ResearchBankV29.ZeroBranchComposition.branchClassBound_zero Us Ur,
    ResearchBankV29.DIClassRealization.di_provider_empty_class _,
    fun M => ResearchBankV29.NonzeroPruning.nonzero_realization_zero _ (Nat.cast_nonneg M) le_rfl⟩

end SameSourceChain
end ResearchBankV30
end Erdos287
