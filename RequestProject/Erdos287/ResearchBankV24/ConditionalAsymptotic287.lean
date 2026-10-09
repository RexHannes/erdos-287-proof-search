import RequestProject.Erdos287.ResearchBankV24.ConditionalPairBaseline
import RequestProject.Erdos287.ResearchBankV20.ConditionalAsymptotic287

/-!
# Erdős #287 — Research Bank V24 §4: CONDITIONAL asymptotic #287 after the positive-sieve repair

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* **`conditional_asymptotic_287_after_positive_sieve_repair`** (LEAN CONDITIONAL ONLY) —

      repaired Route-C baseline (V24, from the explicit analytic providers)
      + S0 (taken from the SAME normalization field of the principal provider) / S1 contracts
      + Route-C-thin score certificate and exact margin check
      + frozen compiler / contact / rigidity / harmonic consumer chain (V20 → V17 → V16 → V14)
      ⟹ ∃ M₀, ∀ M ≥ M₀, no counterexample has maximum `M`.

This is an ASYMPTOTIC CONDITIONAL theorem: it does NOT construct an explicit `M₀`, does NOT
perform the finite splice, and does NOT prove the global Erdős #287.
-/

namespace Erdos287
namespace ResearchBankV24
namespace ConditionalAsymptotic287

open ResearchBankV16.RouteCConsumer
open ResearchBankV17.ThinFunctional
open ResearchBankV13.FiniteRepresentationModel
open ResearchBankV14.ConditionalAsymptoticImplication (S0Contract S1Contract)
open ResearchBankV23.PrincipalEuler
open RepairedProvider RepairedRouteCBaseline ConditionalPairBaseline

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Conditional asymptotic #287 after the positive-sieve repair** (LEAN CONDITIONAL ONLY on the
explicit analytic providers `P`, `D` and the S1 contract; no explicit `M₀`, no finite splice,
NOT the global theorem). -/
theorem conditional_asymptotic_287_after_positive_sieve_repair {muLo WHi err : ℚ} {muF : ℝ}
    {K : ℕ} {h : ℕ → ℝ} {F : ℝ → ℝ} {E : Finset ℕ}
    {Psm Prd : ℕ → ℝ → Finset ℕ} {lev X : ℝ → ℝ} {wτ : ℝ → ℝ → ℕ → ℝ} {r : ℕ}
    {Sd : ResearchBankV23.SingularFactors.SingularData} {LF I : ℝ} {N Li : ℕ → ℝ} {phiW : ℝ}
    {model : ℕ → ℕ → PrincipalModel h} {Kh : ℕ} {EAB : ℕ → ℝ} {Us Ur : ℕ → ℕ → Finset ℕ}
    {DE : ℕ → (Finset ℕ → ℝ) → ℝ} {Ct : ℝ} (τC : FixedTupleC V) (W : WeightSystem τC)
    (C : ThinFunctionalCertificate muLo WHi muF (LF / I)) (hchk : ThinMarginCheck muLo WHi err)
    (h1 : S1Contract (S1 τC W) N muF)
    (P : RepairedCompletedSieveProvider K h F Psm Prd lev X wτ r Sd LF I (S0 τC W) N Li phiW model
      Kh EAB Us Ur DE)
    (D : SameWeightActualMeasureProvider τC W N model (pref Li phiW N)
      (LamFam E Psm Prd lev X wτ) DE EAB Ct ((err : ℚ) : ℝ))
    (G : SieveGeometry E Psm Prd h model Us Ur) (cd : RoundedCellData Prd wτ X)
    (hLi : ∀ M, 0 ≤ Li M) (hphi : 0 < phiW) (hWF : 0 ≤ LF / I) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, NoCounterexampleAt M :=
  ResearchBankV20.ConditionalAsymptotic287.conditional_asymptotic_287_of_baseline τC W N C hchk
    (repaired_uses_frozen_normalization τC W P) h1
    (conditional_pair_baseline_after_repair τC W P D G cd hLi hphi hWF)

end ConditionalAsymptotic287
end ResearchBankV24
end Erdos287
