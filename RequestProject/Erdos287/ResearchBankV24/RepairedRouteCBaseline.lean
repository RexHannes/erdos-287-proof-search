import RequestProject.Erdos287.ResearchBankV24.RepairedCompletedSieveProvider
import RequestProject.Erdos287.ResearchBankV16.ConditionalRouteCImplication

/-!
# Erdős #287 — Research Bank V24 §2: the repaired Route-C baseline

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

## Data

* `LamFam E Psm Prd lev X wτ S τ M` — the ACTUAL completed weight `Λ_new^+` at family index
  `(S, τ)` and scale `M`: `μ_E ⋆ β_sm^+ ⋆ ℓ_rd` with small universe `Psm S M`, rough universe
  `Prd S M`, level `lev M = M^rho`, rounded endpoints `wτ τ M`, support `X M = M^{vartheta0}`;
* `RoundedCellData` — the rounding cells: monotone cell map, cell endpoints `wc`
  (`wτ τ M = wc ∘ cell` on the rough universe), three-bin allocation, atom bound `R`;
* `SieveGeometry` — disjointness of `E`, `Psm`, `Prd`, `h < 1` on the sieve primes, and the
  identification of the principal model universe and of the source-class universes with the
  SAME `E ∪ Psm`, `Prd`.

## EXTERNAL PROVIDER

* `SameWeightActualMeasureProvider` — the actual-measure / tensor decomposition for the SAME
  weight: `Pair/N ≤ M_new(Λ) + |DE(Λ)| + C_t √(E|A-B|²) + 90 + err`, with the very same `Λ` in
  the principal functional `M_new` and in the distribution error `DE` (this plays the role of
  the frozen V20 `PairDecompositionProvider` for the new weight; never constructed).

## LEAN CONDITIONAL

* `ellRd_congr` (LEAN BANK) — `ℓ_rd` only sees the endpoints on its own universe;
* `lamFam_source_decomposition` (LEAN BANK) — every `LamFam S τ M` satisfies the V16
  coefficient contract with mass `(R+1)^{#cells} 3^R`, independent of `M`;
* **`repaired_routeC_baseline_of_providers`** — the bundle `RepairedCompletedSieveProvider` +
  `SameWeightActualMeasureProvider` + geometry ⟹ the frozen V16
  `RouteCBaselineProvider τ W N W_F err`, i.e. `‖B_x‖² ≤ A_C W_F + 90 + err + o(1)` for the
  frozen pair functional.  The proof uses the SAME `LamFam S τ M` for the V23 signed-principal
  budget and for the V16 source-class error.
-/

namespace Erdos287
namespace ResearchBankV24
namespace RepairedRouteCBaseline

open Finset
open ResearchBankV22.RoundedRoughSieve ResearchBankV22.CompletedPositiveWeight
open ResearchBankV22.RosserCostProvider ResearchBankV22.PositiveSieveParameters
open ResearchBankV23.PrincipalEuler ResearchBankV23.HatApproximationProvider
open ResearchBankV23.PrincipalBudget
open ResearchBankV16.RouteCParameters ResearchBankV16.RouteCConsumer
open ResearchBankV16.ConditionalRouteCImplication
open RepairedProvider

/-- `ℓ_rd` only depends on the endpoints of its own universe (LEAN BANK). -/
theorem ellRd_congr {γ : Type*} [LinearOrder γ] {U : Finset γ} {w w' : γ → ℝ}
    (hw : ∀ p ∈ U, w p = w' p) (X : ℝ) : ellRd U w X = ellRd U w' X := by
  funext A
  unfold ellRd ellW
  split_ifs with hA h1 h2 h2 <;> try rfl
  all_goals exfalso
  · apply h2; intro p hp he
    have := h1 p hp he
    unfold roundedCond at this ⊢
    have hab : above A p ⊆ U := (filter_subset _ _).trans hA
    rwa [prod_congr rfl fun q hq => (hw q (hab hq)).symm, ← hw p (hA hp)]
  · apply h1; intro p hp he
    have := h2 p hp he
    unfold roundedCond at this ⊢
    have hab : above A p ⊆ U := (filter_subset _ _).trans hA
    rwa [prod_congr rfl fun q hq => hw q (hab hq), hw p (hA hp)]

/-- The ACTUAL completed weight of the family at index `(S, τ)` and scale `M`. -/
noncomputable def LamFam (E : Finset ℕ) (Psm Prd : ℕ → ℝ → Finset ℕ) (lev X : ℝ → ℝ)
    (wτ : ℝ → ℝ → ℕ → ℝ) (S : ℕ) (τ : ℝ) (M : ℕ) : Finset ℕ → ℝ :=
  LambdaNewPlus E (Psm S M) (Prd S M) (lev M) (wτ τ M) (X M)

/-- The rounding cells of the family. -/
structure RoundedCellData (Prd : ℕ → ℝ → Finset ℕ) (wτ : ℝ → ℝ → ℕ → ℝ) (X : ℝ → ℝ) where
  nC : ℕ → ℝ → ℕ
  cell : ∀ S τ, ℕ → ℕ → Fin (nC S τ)
  mono : ∀ S τ (M : ℕ), Monotone (cell S τ M)
  wc : ∀ S τ, ℕ → Fin (nC S τ) → ℝ
  endpoint : ∀ S τ (M : ℕ), ∀ p ∈ Prd S M, wτ τ M p = wc S τ M (cell S τ M p)
  alloc : ∀ S τ, (Fin (nC S τ) → ℕ) → Fin 3 → Fin (nC S τ) → ℕ
  alloc_sum : ∀ S τ κ j, ∑ i, alloc S τ κ i j = κ j
  R : ℕ → ℝ → ℕ
  atoms : ∀ S τ (M : ℕ) A, A ⊆ Prd S M → ellRd (Prd S M) (wτ τ M) (X M) A ≠ 0 → A.card ≤ R S τ

/-- The sieve geometry: disjoint universes, `h < 1` on sieve primes, and the SAME universes in
the principal model and in the source class. -/
structure SieveGeometry (E : Finset ℕ) (Psm Prd : ℕ → ℝ → Finset ℕ) (h : ℕ → ℝ)
    (model : ℕ → ℕ → PrincipalModel h) (Us Ur : ℕ → ℕ → Finset ℕ) : Prop where
  hU : ∀ S M, (model S M).U = E ∪ Psm S M ∪ Prd S M
  hUs : ∀ S M, Us S M = E ∪ Psm S M
  hUr : ∀ S M, Ur S M = Prd S M
  d1 : ∀ S x, Disjoint E (Psm S x)
  d2 : ∀ S x, Disjoint E (Prd S x)
  d3 : ∀ S x, Disjoint (Psm S x) (Prd S x)
  hh : ∀ S x, ∀ p ∈ E ∪ Psm S x ∪ Prd S x, h p < 1

/-- **Every completed weight of the family satisfies the V16 coefficient contract** with an
`M`-independent mass (LEAN BANK). -/
theorem lamFam_source_decomposition {E : Finset ℕ} {Psm Prd : ℕ → ℝ → Finset ℕ} {lev X : ℝ → ℝ}
    {wτ : ℝ → ℝ → ℕ → ℝ} (cd : RoundedCellData Prd wτ X) (d1 : ∀ S x, Disjoint E (Psm S x))
    (d2 : ∀ S x, Disjoint E (Prd S x)) (d3 : ∀ S x, Disjoint (Psm S x) (Prd S x))
    (S : ℕ) (τ : ℝ) (M : ℕ) :
    SourceDecomposition (LamFam E Psm Prd lev X wτ S τ M) (E ∪ Psm S M) (Prd S M)
      (((cd.R S τ + 1) ^ cd.nC S τ : ℕ) * 3 ^ cd.R S τ) := by
  have hcong := ellRd_congr (cd.endpoint S τ M) (X M)
  have hL : LamFam E Psm Prd lev X wτ S τ M =
      LambdaNewPlus E (Psm S M) (Prd S M) (lev M) (fun p => cd.wc S τ M (cd.cell S τ M p)) (X M) := by
    unfold LamFam LambdaNewPlus completedWeight
    rw [hcong]
  rw [hL]
  have := rounded_completed_weight_matches_V16_contract (d1 S M) (d2 S M) (d3 S M)
    (cd.cell S τ M) (cd.mono S τ M) (cd.wc S τ M) (cd.alloc S τ) (cd.alloc_sum S τ)
    (level := lev M) (R := cd.R S τ) (fun A hA hne => cd.atoms S τ M A hA (by rw [hcong]; exact hne))
  simpa [Fintype.card_fin] using this

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Same-weight actual-measure / tensor decomposition** (EXTERNAL PROVIDER; never
constructed): the frozen pair functional is bounded by the principal functional and the
distribution error of the SAME weight `Λ S τ M`, the tensor approximation error, and the fixed
off-principal part `90 + err`. -/
structure SameWeightActualMeasureProvider (τC : FixedTupleC V) (W : WeightSystem τC) (N : ℕ → ℝ)
    {h : ℕ → ℝ} (model : ℕ → ℕ → PrincipalModel h) (pref : ℕ → ℝ)
    (Λ : ℕ → ℝ → ℕ → Finset ℕ → ℝ) (DE : ℕ → (Finset ℕ → ℝ) → ℝ) (EAB : ℕ → ℝ) (Ct err : ℝ) :
    Prop where
  Ct_nonneg : 0 ≤ Ct
  decomp : ∀ S τ M, Pair τC W M / N M ≤
    (model S M).Mnew (pref M) (Λ S τ M) + |DE M (Λ S τ M)| + Ct * Real.sqrt |EAB M| + 90 + err

/-- **The repaired Route-C baseline** (LEAN CONDITIONAL on the explicit providers).  The SAME
completed weight `LamFam S τ M` is used in the principal term (V23 budget) and in the error term
(V16 source class). -/
theorem repaired_routeC_baseline_of_providers {K : ℕ} {h : ℕ → ℝ} {F : ℝ → ℝ} {E : Finset ℕ}
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
    RouteCBaselineProvider τC W N (LF / I) err := by
  refine ⟨fun η hη => ?_⟩
  -- principal side: V23 budget for the SAME weight
  obtain ⟨S, -, τ, -, M1, hM1⟩ := principal_budget_le_A_C P.rosser P.tuple P.euler G.hU G.d1 G.d2
    G.d3 G.hh hLi hphi hWF (η / 3) (by positivity)
  -- error side: V16 source class for the SAME weight
  set Cm : ℝ := (((cd.R S τ + 1) ^ cd.nC S τ : ℕ) : ℝ) * 3 ^ cd.R S τ
  have hCm : 0 ≤ Cm := by positivity
  have hdec : ∀ M, SourceDecomposition (LamFam E Psm Prd lev X wτ S τ M) (Us S M) (Ur S M) Cm := by
    intro M
    rw [G.hUs, G.hUr]
    exact lamFam_source_decomposition cd G.d1 G.d2 G.d3 S τ M
  obtain ⟨M2, hM2⟩ := distribution_error_small P.source S (LamFam E Psm Prd lev X wτ S τ) hCm hdec
    (η / 3) (by positivity)
  -- tensor side
  have hCt := D.Ct_nonneg
  set δ : ℝ := η / (3 * (Ct + 1))
  have hδ : 0 < δ := by positivity
  obtain ⟨M3, hM3⟩ := hat_approximation_eventually_small P.hat (δ ^ 2) (by positivity)
  refine ⟨max M1 (max M2 M3), fun M hM => ?_⟩
  have hM1' : M1 ≤ M := le_trans (le_max_left _ _) hM
  have hM2' : M2 ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
  have hM3' : M3 ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM
  have e1 := hM1 M hM1'
  have e2 := hM2 M hM2'
  have e3 : Real.sqrt |EAB M| ≤ δ := by
    rw [Real.sqrt_le_left hδ.le]
    exact hM3 M hM3'
  have e3' : Ct * Real.sqrt |EAB M| ≤ η / 3 := by
    calc Ct * Real.sqrt |EAB M| ≤ Ct * δ := mul_le_mul_of_nonneg_left e3 hCt
      _ ≤ (Ct + 1) * δ := by nlinarith
      _ = η / 3 := by simp only [δ]; field_simp
  have hdec' := D.decomp S τ M
  have hmain : (model S M).Mnew (pref Li phiW N M) (LamFam E Psm Prd lev X wτ S τ M) ≤
      ((A_C : ℚ) : ℝ) * (LF / I) + η / 3 := e1
  linarith

end RepairedRouteCBaseline
end ResearchBankV24
end Erdos287
