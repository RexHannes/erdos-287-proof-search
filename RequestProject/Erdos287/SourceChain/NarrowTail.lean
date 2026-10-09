import RequestProject.Erdos287.SourceChain.MinimalTail
import RequestProject.Erdos287.SourceChain.PieceDerivations

/-!
# Erdős #287 — source chain: the critical piece paid from the narrow spectral provider

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**  The theorem here is *conditional*.

* `sharpPaid_of_spectralY` — the critical clean actual–actual piece `F_AA^♯` is paid from
  1. the narrow spectral provider `PascadiSpectralY` with exceptional exponent `θexc ≤ 7/32`
     (statement only about bilinear Kloosterman forms of arbitrary bounded coefficients);
  2. the clean-AA kernel membership `SharpMembership` (source membership, separate declaration);
  3. a sub-power partition count `P ≤ C_P x^η`;
  4. the spectator reciprocal norm;
  5. the ledger `391/256 · σ + η/2 < δ/2`.
* `Tail287_of_NarrowProviders` — the conditional tail theorem in which the critical piece is
  no longer a provider; only the seven non-critical cell pieces keep a named payment.
-/

namespace Erdos287.SourceChain

open Erdos287.CurrentTail

variable {ι : Type*}

/-- **The critical piece `F_AA^♯` is paid from the narrow spectral provider.** -/
theorem sharpPaid_of_spectralY {S : TailSourceFamily ι} (C : OrderingBCells S)
    (Fs : FamilyScale S) {CD θQ θR θH δ θexc σ η Cp : ℝ}
    (hspec : SpectatorReciprocalNorm S Fs CD)
    (hθ : θexc ≤ 7 / 32) (hY : PascadiSpectralY θQ θR θH δ θexc)
    (P : ℕ → ℝ) (hP0 : ∀ X, 0 ≤ P X) (hCp : 0 ≤ Cp) (hPle : ∀ X, P X ≤ Cp * Fs.x X ^ η)
    (hmem : ∃ X1 : ℕ, ∀ X ≥ X1, ∀ ξ ∈ (S.T X).Xi,
      SharpMembership (Fs.x X) ((S.T X).f ξ) (C.Bc X ξ) (C.piece X ξ .sharp) (P X) σ θQ θR θH)
    (hledger : 391 / 256 * σ + η / 2 < δ / 2) :
    PiecePaid S C .sharp :=
  piecePaid_of_powerSaving C Fs hspec .sharp
    (sharp_powerSaving C Fs (QuantitativeTH_of_spectralY hθ hY) P hP0 hCp hPle hmem hledger)

/-- **Conditional tail theorem with the narrow spectral provider for the critical piece.**
NOT an unconditional result: every argument is a named hypothesis. -/
theorem Tail287_of_NarrowProviders (S : TailSourceFamily ι) (C : OrderingBCells S)
    (Fs : FamilyScale S) {CD θQ θR θH δ θexc σ η Cp : ℝ}
    (Fw : SevenBlockTailFramework S) (hBase : BaseSWProvider S) (hCop : CoprimalityPaid S)
    (hRed : OrderingBPoissonReduction S C) (hCent : CenteringPaid S C)
    (hspec : SpectatorReciprocalNorm S Fs CD)
    (hθ : θexc ≤ 7 / 32) (hY : PascadiSpectralY θQ θR θH δ θexc)
    (P : ℕ → ℝ) (hP0 : ∀ X, 0 ≤ P X) (hCp : 0 ≤ Cp) (hPle : ∀ X, P X ≤ Cp * Fs.x X ^ η)
    (hmem : ∃ X1 : ℕ, ∀ X ≥ X1, ∀ ξ ∈ (S.T X).Xi,
      SharpMembership (Fs.x X) ((S.T X).f ξ) (C.Bc X ξ) (C.piece X ξ .sharp) (P X) σ θQ θR θH)
    (hledger : 391 / 256 * σ + η / 2 < δ / 2)
    (hOther : ∀ p, p ≠ CellPiece.sharp → PiecePaid S C p) : Tail287Statement := by
  refine Tail287_of_MinimalAnalyticProviders S C Fw hBase hCop hRed hCent (fun p => ?_)
  by_cases hp : p = CellPiece.sharp
  · subst hp
    exact sharpPaid_of_spectralY C Fs hspec hθ hY P hP0 hCp hPle hmem hledger
  · exact hOther p hp

end Erdos287.SourceChain
