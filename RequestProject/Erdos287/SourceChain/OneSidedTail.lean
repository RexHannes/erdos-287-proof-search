import RequestProject.Erdos287.SourceChain.OneSidedSevenBlock
import RequestProject.Erdos287.SourceChain.MinimalTail

/-!
# Erdős #287 — source chain: minimal-provider tail with the corrected one-sided framework

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.  Conditional theorem.**

Same analytic inputs as `Tail287_of_MinimalAnalyticProviders`, but the structural input is the
one-sided `OneSidedSevenBlockTailFramework` (first-moment lower bound, pair-moment upper bound,
model errors `e₁, e₂ → 0`) instead of the two-sided `SevenBlockTailFramework`.
-/

namespace Erdos287.SourceChain

open Erdos287.CurrentTail

variable {ι : Type*}

/-- **Conditional tail theorem, one-sided framework.**  NOT an unconditional result. -/
theorem Tail287_of_MinimalAnalyticProviders_oneSided (S : TailSourceFamily ι)
    (C : OrderingBCells S) (Fw : OneSidedSevenBlockTailFramework S) (hBase : BaseSWProvider S)
    (hCop : CoprimalityPaid S) (hRed : OrderingBPoissonReduction S C) (hCent : CenteringPaid S C)
    (hP : ∀ p, PiecePaid S C p) : Tail287Statement :=
  tail_of_remainder_littleO_oneSided S Fw (RSigmaP_littleO_of_minimal S C hBase hCop hRed hCent hP)

end Erdos287.SourceChain
