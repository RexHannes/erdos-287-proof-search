import Mathlib
import RequestProject.TrustedBank.Gate1A.AvgJDRInterface
import RequestProject.TrustedBank.Gate1B.SeparableWeights

/-!
# Δv6 open interfaces (**all OPEN**)

This file *states* open propositions.  **No inhabitant / proof is supplied for any of
them**, no `axiom` is declared, and nothing in `RequestProject/TrustedBank/` imports this
file.  Each item below is a specification of what would have to be supplied, not an
assumption that it holds.

Honest scoping remark (unchanged from the earlier challenge files): the authoritative
Gate-1A / Gate-1B source definitions are **not present in this repository**, so the
interfaces are stated against abstract data.  Instantiating them is itself an open
source-audit task.

Open items recorded here:

* `SourceAvgJDR` — the candidate `SOURCE-AVG-JDR` energy bound (OPEN_ANALYTIC).
* `SourceIdentityRequirement` — the `Ctilde = H·S + negligible` identity
  (SOURCE_FIELD_REQUIRED: not present in this repository).
* `MixedStartNSE`, `RLS45`, `ACBV45`, `JointAffineCorrelation45` (OPEN_ANALYTIC).
* `BCrossUniversal` (OPEN_ANALYTIC).
* `LCBeta` — the global adjacent log-cofactor prime supply for Erdős #287 (OPEN), and
  `LogCofactorAsymptoticInterface` — the elementary-asymptotic step
  `J ≤ η log M / log log M ⟹ the finite blocker hypotheses` (OPEN, external).
-/

open scoped BigOperators

namespace Challenges
namespace Delta6

/-! ## Gate 1A -/

/-- **SOURCE-AVG-JDR (OPEN).**  Abstractly: the centered source operator `S`, indexed by
the triples `(r, m, k)`, obeys the energy bound `∑ ‖S‖² ≤ targetEnergy`.  Whether this
holds for the authoritative source operator is exactly the open question. -/
def SourceAvgJDR {σ : Type*} [Fintype σ] (S : σ → ℂ) (targetEnergy : ℝ) : Prop :=
  ∑ i, ‖S i‖ ^ 2 ≤ targetEnergy

/-- **SOURCE_FIELD_REQUIRED.**  The source identity `Ctilde = H·S + negligible`.  It is
*not* asserted anywhere: the authoritative definition of `Ctilde^{gen}` is absent from
this repository, so any theorem using it takes it as an explicit hypothesis (see
`TrustedBank.Gate1A.avgJDR_transfer`). -/
def SourceIdentityRequirement {σ : Type*} (Ct S neg : σ → ℂ) (H : ℝ) : Prop :=
  ∀ i, Ct i = (H : ℂ) * S i + neg i

/-- **Superseded / non-controlling routes.**  Recorded so that they are not mistaken for
targets: pointwise SB-ν, SRB-only closure, M-SYNC-WEAK as a primary target, and the
`U^5 / U^3` bookkeeping routes.  They may survive as auxiliary lemmas; none of them is
the controlling formulation. -/
inductive SupersededRoute
  | pointwiseSBnu
  | srbOnlyClosure
  | mSyncWeakPrimary
  | u5u3Bookkeeping
  deriving DecidableEq, Repr

/-! ## Gate 1B -/

/-- **MixedStartNSE (OPEN).**  Abstract shape: for two *different* starts `θ ≠ θ'`, the
mixed-start correlation is diagonal-dominated.  Same-start injectivity
(`TrustedBank.Gate1B.sameStart_injective`) does **not** give this; see
`TrustedBank.Gate1B.mixedStart_not_diagonal`. -/
def MixedStartNSE (crossCorrelation diagonalBound : ℝ) : Prop :=
  crossCorrelation ≤ diagonalBound

/-- **RLS45 (OPEN).**  The mixed-start reduced large-sieve step, as an abstract bound of
the source energy by the claimed level-`4/5` bound. -/
def RLS45 (sourceEnergy claimedBound : ℝ) : Prop :=
  sourceEnergy ≤ claimedBound

/-- **ACBV45 (OPEN).**  The convolution-type BV capacity at level `4/5`.

Metadata: ACBV45 is **not** currently a direct corollary of the published 5/8-type
distribution results.  Those theorems carry coefficient-class (well-factorable /
convolution) hypotheses which must be mapped to the actual source coefficients
separately; that mapping is not performed anywhere in this repository. -/
def ACBV45 (sourceDiscrepancy claimedBound : ℝ) : Prop :=
  sourceDiscrepancy ≤ claimedBound

/-- **JointAffineCorrelation45 (OPEN).**  The joint affine correlation input. -/
def JointAffineCorrelation45 (correlation claimedBound : ℝ) : Prop :=
  correlation ≤ claimedBound

/-- **B_cross universal (OPEN).**  A universal bound for the cross bilinear form.
Positive Cauchy on `B_cross` / `B_x` is retracted as a universal closure. -/
def BCrossUniversal (bCross claimedBound : ℝ) : Prop :=
  bCross ≤ claimedBound

/-- Retracted / dead universal source closures, recorded so they are not revived by
accident. -/
inductive RetractedRoute
  | illegalShellCartesian
  | actualSourceR2Zhao
  | sameStartSD45
  | rawMAM45CircleNorm
  | positiveCauchyBCross
  | acbv45AsPublished
  deriving DecidableEq, Repr

/-! ## Erdős #287 -/

/-- **LCB_η (OPEN).**  The global adjacent log-cofactor prime supply: for every large
`M` there is an `x` in the relevant window such that both `x` and `x+1` carry prime
factors satisfying the finite blocker hypotheses of
`TrustedBank.Erdos287Good.Gap2CE.logCofactor_finite_blocker`.

This is **not** proved, and #287 must never be derived from it without (i) an effective
threshold and (ii) a finite verification below that threshold. -/
def LCBeta (M J : ℕ) : Prop :=
  ∃ x : ℕ, ∃ q₀ q₁ : ℕ, q₀.Prime ∧ q₁.Prime ∧
    M ≤ 2 * J * q₀ ∧ M ≤ 2 * J * q₁ ∧ M < q₀ ^ 2 ∧ M < q₁ ^ 2 ∧
    q₀ ∣ x ∧ q₁ ∣ (x + 1) ∧ x + 1 ≤ M

/-- **Log-cofactor asymptotic interface (OPEN, external).**  The elementary-asymptotic
step `J ≤ η log M / log log M` (for fixed rational `0 < η < 1/2`), which would feed the
finite blocker.  Formalizing the real-logarithmic asymptotics is deliberately deferred:
only the finite blocker is banked. -/
def LogCofactorAsymptoticInterface (eta : ℚ) (J : ℕ → ℕ) : Prop :=
  0 < eta ∧ eta < 1 / 2 ∧
    ∀ᶠ M : ℕ in Filter.atTop,
      (J M : ℝ) ≤ (eta : ℝ) * Real.log M / Real.log (Real.log M)

end Delta6
end Challenges
