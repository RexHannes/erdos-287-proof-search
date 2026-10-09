import RequestProject.Erdos287.ResearchBankV24.RepairedRouteCBaseline
import RequestProject.Erdos287.ResearchBankV20.ThinPairBaseline

/-!
# Erdős #287 — Research Bank V24 §3: the conditional pair baseline

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**
**This is NOT a proved pair theorem.**

* `repaired_uses_frozen_normalization` (LEAN CONDITIONAL) — the normalization `N` in the
  repaired principal term satisfies the frozen `S0Contract (S0 τ W) N`: it is the SAME frozen
  normalization, taken from the provider's `normalization_agreement`;
* **`conditional_pair_baseline_after_repair`** (LEAN CONDITIONAL) — the explicit providers
  give the frozen V20 `ThinPairBaselineBound τ W N W_F err` (definitionally the V16
  `RouteCBaselineProvider`) with `W_F = L_ij(F)/I`.
-/

namespace Erdos287
namespace ResearchBankV24
namespace ConditionalPairBaseline

open ResearchBankV16.RouteCConsumer ResearchBankV16.ConditionalRouteCImplication
open ResearchBankV20.ThinPairBaseline
open ResearchBankV23.PrincipalEuler
open ResearchBankV14.ConditionalAsymptoticImplication (S0Contract)
open RepairedProvider RepairedRouteCBaseline

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The repaired principal term uses the SAME frozen normalization `N` as S0/S1. -/
theorem repaired_uses_frozen_normalization {K : ℕ} {h : ℕ → ℝ} {F : ℝ → ℝ}
    {Psm Prd : ℕ → ℝ → Finset ℕ} {lev X : ℝ → ℝ} {wτ : ℝ → ℝ → ℕ → ℝ} {r : ℕ}
    {Sd : ResearchBankV23.SingularFactors.SingularData} {LF I : ℝ} {N Li : ℕ → ℝ} {phiW : ℝ}
    {model : ℕ → ℕ → PrincipalModel h} {Kh : ℕ} {EAB : ℕ → ℝ} {Us Ur : ℕ → ℕ → Finset ℕ}
    {DE : ℕ → (Finset ℕ → ℝ) → ℝ} (τC : FixedTupleC V) (W : WeightSystem τC)
    (P : RepairedCompletedSieveProvider K h F Psm Prd lev X wτ r Sd LF I (S0 τC W) N Li phiW model
      Kh EAB Us Ur DE) :
    S0Contract (S0 τC W) N :=
  P.euler.normalization_agreement

/-- **The conditional pair baseline after the positive-sieve repair** (LEAN CONDITIONAL). -/
theorem conditional_pair_baseline_after_repair {K : ℕ} {h : ℕ → ℝ} {F : ℝ → ℝ} {E : Finset ℕ}
    {Psm Prd : ℕ → ℝ → Finset ℕ} {lev X : ℝ → ℝ} {wτ : ℝ → ℝ → ℕ → ℝ} {r : ℕ}
    {Sd : ResearchBankV23.SingularFactors.SingularData} {LF I : ℝ} {N Li : ℕ → ℝ} {phiW : ℝ}
    {model : ℕ → ℕ → PrincipalModel h} {Kh : ℕ} {EAB : ℕ → ℝ} {Us Ur : ℕ → ℕ → Finset ℕ}
    {DE : ℕ → (Finset ℕ → ℝ) → ℝ} {Ct err : ℝ} (τC : FixedTupleC V) (W : WeightSystem τC)
    (P : RepairedCompletedSieveProvider K h F Psm Prd lev X wτ r Sd LF I (S0 τC W) N Li phiW model
      Kh EAB Us Ur DE)
    (D : SameWeightActualMeasureProvider τC W N model (pref Li phiW N)
      (LamFam E Psm Prd lev X wτ) DE EAB Ct err)
    (G : SieveGeometry E Psm Prd h model Us Ur) (cd : RoundedCellData Prd wτ X)
    (hLi : ∀ M, 0 ≤ Li M) (hphi : 0 < phiW) (hWF : 0 ≤ LF / I) :
    ThinPairBaselineBound τC W N (LF / I) err :=
  repaired_routeC_baseline_of_providers τC W P D G cd hLi hphi hWF

end ConditionalPairBaseline
end ResearchBankV24
end Erdos287
