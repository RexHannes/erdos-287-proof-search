import RequestProject.Erdos287.ResearchBankV30.SameNormalizationChain

/-!
# Erdős #287 — Research Bank V30 §18: quantifier order

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The intended order is realized by the SHAPE of the statements (LEAN CONDITIONAL):

1. tuple / kernel / base / tensor data — the theorem PARAMETERS `τC, W, h, E, Psm, Prd, lev, X,
   wτ, model, Kh, EAB, …` and the finite pattern / colouring type `V` are fixed first;
2. `ρ = 1/1000000` — a fixed rational constant (`rho_fixed`), not a function of `x`;
3. the small-sieve parameter `S` and 4. the cell width `τ` — chosen by `∃ S, ∃ τ` AFTER the
   tolerance `η` and BEFORE `M₀` and `M`;
5. finite patterns / colourings / exceptional states — part of the fixed parameters (step 1);
6. branchwise representations — the V24 source decomposition of `LamFam S τ M` has a coefficient
   mass `(R(S,τ)+1)^{nC(S,τ)} 3^{R(S,τ)}` depending only on `(S, τ)` (`mass_independent_of_M`);
7. `x = M → ∞` — the innermost `∀ M ≥ M₀`.

`quantifier_order_respected` is the `B_x` / pair bound in exactly this order; `S, τ` are bound by
an existential OUTSIDE `∀ M` and occur in the conclusion (through the weight `LamFam S τ M` in
`BxSq`), so the weight used at every scale `M` has parameters that cannot depend on `M`.
-/

namespace Erdos287
namespace ResearchBankV30
namespace QuantifierOrder

open ResearchBankV16.RouteCParameters ResearchBankV16.RouteCConsumer
open ResearchBankV23.PrincipalEuler ResearchBankV24.RepairedProvider
open ResearchBankV24.RepairedRouteCBaseline
open ResearchBankV27.DISpectral ResearchBankV28.ExactParameterInstantiation
open ResearchBankV28.RepairedAnalyticBundle ResearchBankV28.FinalPairComposition
open ResearchBankV29.ProviderElimination ResearchBankV29.FunctionalCertificate

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `ρ` is a fixed constant (LEAN BANK). -/
theorem rho_fixed : ResearchBankV22.PositiveSieveParameters.rho = 1 / 1000000 := rfl

/-- The representation mass depends only on `(S, τ)` (LEAN BANK). -/
theorem mass_independent_of_M {Prd : ℕ → ℝ → Finset ℕ} {wτ : ℝ → ℝ → ℕ → ℝ} {X : ℝ → ℝ}
    {E : Finset ℕ} {Psm : ℕ → ℝ → Finset ℕ} {lev : ℝ → ℝ} (cd : RoundedCellData Prd wτ X)
    (d1 : ∀ S x, Disjoint E (Psm S x)) (d2 : ∀ S x, Disjoint E (Prd S x))
    (d3 : ∀ S x, Disjoint (Psm S x) (Prd S x)) (S : ℕ) (τ : ℝ) :
    ∀ M : ℕ, SourceDecomposition (LamFam E Psm Prd lev X wτ S τ M) (E ∪ Psm S M) (Prd S M)
      ((((cd.R S τ + 1) ^ cd.nC S τ : ℕ) : ℝ) * 3 ^ cd.R S τ) :=
  fun M => lamFam_source_decomposition cd d1 d2 d3 S τ M

/-- **The quantifier order is respected** (LEAN CONDITIONAL). -/
theorem quantifier_order_respected {τC : FixedTupleC V} {W : WeightSystem τC} {K : ℕ}
    {h : ℕ → ℝ} {F : ℝ → ℝ} {E : Finset ℕ} {Psm Prd : ℕ → ℝ → Finset ℕ} {lev X : ℝ → ℝ}
    {wτ : ℝ → ℝ → ℕ → ℝ} {r : ℕ} {Sd : ResearchBankV23.SingularFactors.SingularData} {LF I : ℝ}
    {N Li : ℕ → ℝ} {phiW : ℝ} {model : ℕ → ℕ → PrincipalModel h} {Kh : ℕ} {EAB : ℕ → ℝ}
    {Us Ur : ℕ → ℕ → Finset ℕ} {D0 D1 D2 Db DEnz : ℕ → (Finset ℕ → ℝ) → ℝ} {Ct Cnz : ℝ}
    {muF : ℝ} {DIClass : KloostermanData → Prop}
    (Mn : MinimalExternalAnalyticProviders τC W K h F Psm Prd lev X wτ r Sd LF I N Li phiW model
      Kh EAB Us Ur D0 D1 D2 Db muF DIClass)
    (C : FunctionalKernelCertificate muF (LF / I))
    (Gl : InternalGlueOwner τC W h E Psm Prd lev X wτ N Li phiW model EAB D0 D1 D2 Db DEnz Ct Cnz
      ((errFinal : ℚ) : ℝ) DIClass)
    (G : SieveGeometry E Psm Prd h model Us Ur) (cd : RoundedCellData Prd wτ X)
    (hLi : ∀ M, 0 ≤ Li M) (hphi : 0 < phiW) :
    ∀ η > 0, ∃ S : ℕ, ∃ τ : ℝ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
      BxSq model (pref Li phiW N) (LamFam E Psm Prd lev X wτ) (sumDE D0 D1 D2 Db) DEnz EAB Ct
          S τ M ≤ ((A_C : ℚ) : ℝ) * (LF / I) + η ∧
        Pair τC W M / N M ≤ ((A_C : ℚ) : ℝ) * (LF / I) + 27 / 5 + η :=
  FullPairComposition.full_pair_composition Mn C Gl G cd hLi hphi

end QuantifierOrder
end ResearchBankV30
end Erdos287
