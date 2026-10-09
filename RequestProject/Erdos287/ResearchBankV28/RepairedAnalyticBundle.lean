import RequestProject.Erdos287.ResearchBankV24.ConditionalAsymptotic287
import RequestProject.Erdos287.ResearchBankV27.CleanNonzero
import RequestProject.Erdos287.ResearchBankV28.ExactParameterInstantiation

/-!
# Erdős #287 — Research Bank V28 §11: the minimal final analytic bundle

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`FinalAnalyticProviders` collects ONLY genuinely unformalized analytic inputs (EXTERNAL
PROVIDER interfaces; the bundle is never constructed):

* `rosser`, `tuple` — Rosser scalar asymptotic and prime-harmonic tuple input (V22);
* `euler` — principal Euler/Mellin provider (V23; carries the frozen S0 normalization);
* `hat` — tensor/hat reference approximation (V23);
* `di` — the ONE minimal `DISpectralProvider` (V27) at `η = 1/1100` for the class `DIClass`
  of public DI forms (the realized forms must lie in `DIClass`);
* `zeroFreq` — the masked-SW / BDH zero-frequency branch class bound;
* `oneLarge`, `twoLarge` — the one-large / two-large HB branch class bounds;
* `boundary` — the product-boundary branch class bound (V26 union-of-boundary estimate);
* `nonzero` — for every family weight, a clean realization of the nonzero-frequency branch: clean
  states at scale `x = M` together with their per-instance `RepresentationMomentProvider`,
  `DivisorSumProvider` and the named `NonzeroPruningContract` (V27);
* `tensor` — the same-weight actual-measure decomposition `BranchedActualMeasureProvider`
  (tensor approximation / actual measure, still external);
* `s1` — the S1 contract; `cert` — the certified functional bounds `μ_F > μ_lo`, `W_F < W_hi`.

It does NOT contain fixed-modulus centering, residue-energy projection, HB algebra, cell
colouring, positive-sieve finite algebra, finite-label colour grouping, CRT orbit counting or
parameter arithmetic: those are kernel theorems (V21–V27).  Nor does it contain the retired
monolithic source-class provider: the V24 `SourceClassDistributionProvider` is DERIVED here
(`derived_source_class_provider`) from the four branch class bounds.

**LEAN BANK / LEAN CONDITIONAL.**
* `derived_source_class_provider` — the four branch class bounds give the V24
  `SourceClassDistributionProvider` for the summed branch functional;
* `nonzero_branch_small` — from the V27 derived clean-nonzero theorem:
  eventually `[DE_nz(Λ)]_+ ≤ ε`.
-/

namespace Erdos287
namespace ResearchBankV28
namespace RepairedAnalyticBundle

open Finset
open ResearchBankV22.RosserCostProvider ResearchBankV22.IndependentFactorization
open ResearchBankV23.PrincipalEuler ResearchBankV23.HatApproximationProvider
open ResearchBankV16.RouteCConsumer
open ResearchBankV14.ConditionalAsymptoticImplication (S0Contract S1Contract)
open ResearchBankV17.ThinFunctional
open ResearchBankV24.RepairedProvider ResearchBankV24.RepairedRouteCBaseline
open ResearchBankV27.CleanNonzero ResearchBankV27.DecoratedLemma ResearchBankV27.DISpectral
  ResearchBankV27.GlobalConductorSum

/-- A branch class bound (EXTERNAL PROVIDER shape): the branch functional is linear and is
eventually small on every source-factorized weight. -/
structure BranchClassBound (Us Ur : ℕ → ℕ → Finset ℕ) (DEb : ℕ → (Finset ℕ → ℝ) → ℝ) : Prop where
  linear : ∀ M {ι : Type} [Fintype ι] (c : ι → ℝ) (g : ι → Finset ℕ → ℝ),
    DEb M (fun A => ∑ i, c i * g i A) = ∑ i, c i * DEb M (g i)
  class_bound : ∀ S : ℕ, ∀ ε > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ g : Finset ℕ → ℝ,
    SourceFactorization g (Us S M) (Ur S M) → |DEb M g| ≤ ε

/-- The summed branch functional `DE_src = DE_zero + DE_one + DE_two + DE_bdry`. -/
def sumDE (D0 D1 D2 Db : ℕ → (Finset ℕ → ℝ) → ℝ) : ℕ → (Finset ℕ → ℝ) → ℝ :=
  fun M g => D0 M g + D1 M g + D2 M g + Db M g

/-- **The V24 source-class provider is DERIVED** from the four branch class bounds (LEAN BANK). -/
theorem derived_source_class_provider {Us Ur : ℕ → ℕ → Finset ℕ}
    {D0 D1 D2 Db : ℕ → (Finset ℕ → ℝ) → ℝ} (h0 : BranchClassBound Us Ur D0)
    (h1 : BranchClassBound Us Ur D1) (h2 : BranchClassBound Us Ur D2)
    (hb : BranchClassBound Us Ur Db) :
    SourceClassDistributionProvider Us Ur (sumDE D0 D1 D2 Db) := by
  refine ⟨fun M ι _ c g => ?_, fun S ε hε => ?_⟩
  · simp only [sumDE]
    rw [h0.linear, h1.linear, h2.linear, hb.linear, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  · obtain ⟨A0, hA0⟩ := h0.class_bound S (ε / 4) (by positivity)
    obtain ⟨A1, hA1⟩ := h1.class_bound S (ε / 4) (by positivity)
    obtain ⟨A2, hA2⟩ := h2.class_bound S (ε / 4) (by positivity)
    obtain ⟨Ab, hAb⟩ := hb.class_bound S (ε / 4) (by positivity)
    refine ⟨max (max A0 A1) (max A2 Ab), fun M hM g hg => ?_⟩
    have e0 := hA0 M (by omega) g hg
    have e1 := hA1 M (by omega) g hg
    have e2 := hA2 M (by omega) g hg
    have eb := hAb M (by omega) g hg
    simp only [sumDE]
    calc |D0 M g + D1 M g + D2 M g + Db M g| ≤ |D0 M g| + |D1 M g| + |D2 M g| + |Db M g| := by
          have := abs_add_le (D0 M g + D1 M g + D2 M g) (Db M g)
          have := abs_add_le (D0 M g + D1 M g) (D2 M g)
          have := abs_add_le (D0 M g) (D1 M g)
          linarith
      _ ≤ ε := by linarith

/-- **Clean realization of the nonzero-frequency branch** at scale `x` for the value `val`
(named composition interface; its analytic content is the per-instance
`RepresentationMomentProvider`, `DivisorSumProvider` and `NonzeroPruningContract`). -/
def NonzeroCleanRealization (DIClass : KloostermanData → Prop) (x val Cnz : ℝ) : Prop :=
  ∃ (β : Type) (ε NU : ℝ) (Rnz : ℂ) (Ds : Finset ℕ) (bs : ℕ → Finset β)
    (st : ℕ → β → CleanState x) (Γ : ℕ → β → ℂ) (C : ℕ),
    0 ≤ NU ∧ NU ≤ Cnz ∧ ε ≤ 347 / 836000 ∧
    (∀ D ∈ Ds, ∀ b ∈ bs D, (st D b).D = D) ∧
    (∀ D ∈ Ds, ∀ b ∈ bs D, (st D b).DD.KD.Nq / (st D b).d = NU) ∧
    (∀ D ∈ Ds, ∀ b ∈ bs D, RepresentationMomentProvider (st D b).DD) ∧
    (∀ D ∈ Ds, ∀ b ∈ bs D, CleanAdmissible DIClass (1 / 1100) (st D b)) ∧
    (∀ D ∈ Ds, ∑ b ∈ bs D, ‖Γ D b‖ ≤ ((Nat.divisors D).card : ℝ) ^ C) ∧
    DivisorSumProvider Ds C x (1 / 19000) ε ∧
    NonzeroPruningContract Rnz Ds bs Γ (fun D b => (st D b).P) NU x ∧
    val = Rnz.re

/-- **Nonzero branch is eventually small** (LEAN CONDITIONAL on `DISpectralProvider` and the
clean realizations): derived from the V27 clean-nonzero THEOREM with `A = 1`. -/
theorem nonzero_branch_small {DIClass : KloostermanData → Prop} {Cnz : ℝ}
    (hDI : DISpectralProvider (1 / 1100) DIClass) (val : ℕ → ℝ)
    (hreal : ∀ M : ℕ, NonzeroCleanRealization DIClass M (val M) Cnz) :
    ∀ ε > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀, max (val M) 0 ≤ ε := by
  intro ε hε
  obtain ⟨X0, hX0⟩ := clean_nonzero_derived 1
  refine ⟨⌈max X0 (Real.exp (|Cnz| / ε))⌉₊ + 3, fun M hM => ?_⟩
  have hMr : max X0 (Real.exp (|Cnz| / ε)) ≤ (M : ℝ) := by
    have := Nat.le_ceil (max X0 (Real.exp (|Cnz| / ε)))
    have : ((⌈max X0 (Real.exp (|Cnz| / ε))⌉₊ + 3 : ℕ) : ℝ) ≤ M := by exact_mod_cast hM
    push_cast at this; linarith
  have hM3 : (3 : ℝ) ≤ M := by
    have : ((⌈max X0 (Real.exp (|Cnz| / ε))⌉₊ + 3 : ℕ) : ℝ) ≤ M := by exact_mod_cast hM
    push_cast at this; linarith [Nat.cast_nonneg (α := ℝ) ⌈max X0 (Real.exp (|Cnz| / ε))⌉₊]
  obtain ⟨β, ε', NU, Rnz, Ds, bs, st, Γ, C, hNU, hNUC, hε', hstD, hnorm, hRep, hadm, hroot, hdiv,
    hprune, hval⟩ := hreal M
  have hb := hX0 M (le_trans (le_max_left _ _) hMr) ε' NU Rnz hNU hε' hDI Ds bs st Γ C hstD hnorm
    hRep hadm hroot hdiv hprune
  rw [Real.rpow_one] at hb
  have hlogpos : 0 < Real.log M := Real.log_pos (by linarith)
  have hlog : |Cnz| / ε ≤ Real.log M := by
    rw [← Real.log_exp (|Cnz| / ε)]
    exact Real.log_le_log (Real.exp_pos _) (le_trans (le_max_right _ _) hMr)
  rw [hval]
  refine hb.trans ?_
  rw [div_le_iff₀ hlogpos]
  have h1 : NU ≤ |Cnz| := hNUC.trans (le_abs_self _)
  have h2 : |Cnz| ≤ ε * Real.log M := by
    rw [div_le_iff₀ hε] at hlog; linarith
  linarith

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Same-weight branched actual-measure / tensor decomposition** (EXTERNAL PROVIDER; never
constructed): for the SAME weight `Λ S τ M` in every term,
`Pair/N ≤ M_new(Λ) + |DE_src(Λ)| + [DE_nz(Λ)]_+ + C_t √|E_AB| + 90 + err`. -/
structure BranchedActualMeasureProvider (τC : FixedTupleC V) (W : WeightSystem τC) (N : ℕ → ℝ)
    {h : ℕ → ℝ} (model : ℕ → ℕ → PrincipalModel h) (pref : ℕ → ℝ)
    (Λ : ℕ → ℝ → ℕ → Finset ℕ → ℝ) (DEsrc DEnz : ℕ → (Finset ℕ → ℝ) → ℝ) (EAB : ℕ → ℝ)
    (Ct err : ℝ) : Prop where
  Ct_nonneg : 0 ≤ Ct
  decomp : ∀ S τ M, Pair τC W M / N M ≤
    (model S M).Mnew (pref M) (Λ S τ M) + |DEsrc M (Λ S τ M)| + max (DEnz M (Λ S τ M)) 0 +
      Ct * Real.sqrt |EAB M| + 90 + err

/-- **The final analytic bundle** (EXTERNAL PROVIDER interfaces only; never constructed). -/
structure FinalAnalyticProviders (τC : FixedTupleC V) (W : WeightSystem τC)
    (K : ℕ) (h : ℕ → ℝ) (F : ℝ → ℝ) (E : Finset ℕ) (Psm Prd : ℕ → ℝ → Finset ℕ) (lev X : ℝ → ℝ)
    (wτ : ℝ → ℝ → ℕ → ℝ) (r : ℕ) (Sd : ResearchBankV23.SingularFactors.SingularData) (LF I : ℝ)
    (N Li : ℕ → ℝ) (phiW : ℝ) (model : ℕ → ℕ → PrincipalModel h) (Kh : ℕ) (EAB : ℕ → ℝ)
    (Us Ur : ℕ → ℕ → Finset ℕ) (D0 D1 D2 Db DEnz : ℕ → (Finset ℕ → ℝ) → ℝ) (Ct Cnz err : ℝ)
    (muLo WHi : ℚ) (muF : ℝ) (DIClass : KloostermanData → Prop) where
  rosser : RosserScalarProvider K h F Psm Prd lev X
  tuple : PrimeHarmonicTupleProvider h Prd X wτ
  euler : PrincipalEulerProvider h r Sd LF I (S0 τC W) N Li phiW model
  hat : HatReferenceApproximationProvider Kh EAB
  di : DISpectralProvider (1 / 1100) DIClass
  zeroFreq : BranchClassBound Us Ur D0
  oneLarge : BranchClassBound Us Ur D1
  twoLarge : BranchClassBound Us Ur D2
  boundary : BranchClassBound Us Ur Db
  nonzero : ∀ (S : ℕ) (τ : ℝ) (M : ℕ),
    NonzeroCleanRealization DIClass M (DEnz M (LamFam E Psm Prd lev X wτ S τ M)) Cnz
  tensor : BranchedActualMeasureProvider τC W N model (pref Li phiW N) (LamFam E Psm Prd lev X wτ)
    (sumDE D0 D1 D2 Db) DEnz EAB Ct err
  s1 : S1Contract (S1 τC W) N muF
  cert : ThinFunctionalCertificate muLo WHi muF (LF / I)

end RepairedAnalyticBundle
end ResearchBankV28
end Erdos287
