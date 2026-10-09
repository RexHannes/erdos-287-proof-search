import RequestProject.Erdos287.ResearchBankV29.FunctionalCertificate
import RequestProject.Erdos287.ResearchBankV28.PreEffectivityTheorem

/-!
# Erdős #287 — Research Bank V29 §12: provider elimination

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

## The split of the V28 bundle

`FinalAnalyticProviders` (V28) has 14 fields.  V29 splits them into three disjoint groups:

1. `MinimalExternalAnalyticProviders` — ONLY analytic inputs: `rosser`, `tuple`, `euler`, `hat`,
   `di`, `zeroFreq`, `oneLarge`, `twoLarge`, `boundary`, `s1`.  It contains no DIClass membership,
   no kernel realization, no pruning identity, no branch classification, no normalization or weight
   equality (those are definitional, `SourceNormalization`), no parameter arithmetic, no graph /
   compiler fact and no finite certificate.
2. `FunctionalKernelCertificate` — FINITE CERTIFIED INPUT (`FunctionalCertificate`).
3. `InternalGlueOwner` — the INTERNAL composition content that V29 could NOT eliminate, because
   the bank has no physical source object from which to derive it:
   * `tensor` — the same-weight actual-measure majorization `Pair/N ≤ M_new(Λ) + |DE_src(Λ)| +
     [DE_nz(Λ)]_+ + C_t √|E_AB| + 90 + err` for the given branch functionals;
   * `nonzero` — the clean realization of `DE_nz` (clean states in `DIClass`, per-state
     representation moments, divisor-sum bound, `NonzeroPruningContract`).
   Both are statements about how the PHYSICAL pair source decomposes into the branch functionals
   `D0, D1, D2, Db, DEnz`, which are uninterpreted parameters in V2–V28.

`old_FinalAnalyticProviders_of_minimal` rebuilds the old bundle FROM
(minimal external) + (certificate) + (internal glue owner) — the requested direction.

## Why the glue owner cannot simply be dropped (SUCCESS C / D evidence)

`old_FinalAnalyticProviders_of_degenerate` shows that the old bundle can ALSO be built with
`D0 = D1 = D2 = Db = DEnz = 0`, `DIClass = ∅`, `C_nz = 0` from a `DegenerateTensorProvider`
alone (plus rosser/tuple/euler/hat/s1/certificate): then `zeroFreq`, `oneLarge`, `twoLarge`,
`boundary`, `di` and `nonzero` are all discharged VACUOUSLY (`branchClassBound_zero`,
`di_provider_empty_class`, `nonzero_realization_zero`).  The price is that the degenerate tensor
provider asserts `Pair/N ≤ M_new(Λ) + C_t √|E_AB| + 90 + err` with NO distribution remainder —
strictly stronger than any tensor-approximation theorem, i.e. it is the pair baseline itself.
Hence: the V28 branch fields constrain nothing until the branch functionals are DEFINED from the
physical source; the same-source chain is not established in the bank (SUCCESS D), and using the
degenerate route would be a provider mismatch (SUCCESS C).  V29/V30 do NOT use it for the final
theorem.
-/

namespace Erdos287
namespace ResearchBankV29
namespace ProviderElimination

open ResearchBankV22.RosserCostProvider ResearchBankV23.PrincipalEuler
open ResearchBankV23.HatApproximationProvider ResearchBankV16.RouteCConsumer
open ResearchBankV14.ConditionalAsymptoticImplication (S0Contract S1Contract)
open ResearchBankV17.ThinFunctional ResearchBankV24.RepairedRouteCBaseline
open ResearchBankV27.DISpectral ResearchBankV28.RepairedAnalyticBundle
open ResearchBankV28.ExactParameterInstantiation ResearchBankV13.FiniteRepresentationModel
open FunctionalCertificate

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The minimal external analytic providers** (EXTERNAL PROVIDER interfaces only). -/
structure MinimalExternalAnalyticProviders (τC : FixedTupleC V) (W : WeightSystem τC)
    (K : ℕ) (h : ℕ → ℝ) (F : ℝ → ℝ) (Psm Prd : ℕ → ℝ → Finset ℕ) (lev X : ℝ → ℝ)
    (wτ : ℝ → ℝ → ℕ → ℝ) (r : ℕ) (Sd : ResearchBankV23.SingularFactors.SingularData) (LF I : ℝ)
    (N Li : ℕ → ℝ) (phiW : ℝ) (model : ℕ → ℕ → PrincipalModel h) (Kh : ℕ) (EAB : ℕ → ℝ)
    (Us Ur : ℕ → ℕ → Finset ℕ) (D0 D1 D2 Db : ℕ → (Finset ℕ → ℝ) → ℝ) (muF : ℝ)
    (DIClass : KloostermanData → Prop) where
  rosser : RosserScalarProvider K h F Psm Prd lev X
  tuple : PrimeHarmonicTupleProvider h Prd X wτ
  euler : PrincipalEulerProvider h r Sd LF I (S0 τC W) N Li phiW model
  hat : HatReferenceApproximationProvider Kh EAB
  di : DISpectralProvider (1 / 1100) DIClass
  zeroFreq : BranchClassBound Us Ur D0
  oneLarge : BranchClassBound Us Ur D1
  twoLarge : BranchClassBound Us Ur D2
  boundary : BranchClassBound Us Ur Db
  s1 : S1Contract (S1 τC W) N muF

/-- **The internal glue owner** (INTERNAL COMPOSITION OBLIGATION, NOT eliminated in V29). -/
structure InternalGlueOwner (τC : FixedTupleC V) (W : WeightSystem τC) (h : ℕ → ℝ)
    (E : Finset ℕ) (Psm Prd : ℕ → ℝ → Finset ℕ) (lev X : ℝ → ℝ) (wτ : ℝ → ℝ → ℕ → ℝ)
    (N Li : ℕ → ℝ) (phiW : ℝ) (model : ℕ → ℕ → PrincipalModel h) (EAB : ℕ → ℝ)
    (D0 D1 D2 Db DEnz : ℕ → (Finset ℕ → ℝ) → ℝ) (Ct Cnz err : ℝ)
    (DIClass : KloostermanData → Prop) : Prop where
  tensor : BranchedActualMeasureProvider τC W N model (pref Li phiW N) (LamFam E Psm Prd lev X wτ)
    (sumDE D0 D1 D2 Db) DEnz EAB Ct err
  nonzero : ∀ (S : ℕ) (τ : ℝ) (M : ℕ),
    NonzeroCleanRealization DIClass M (DEnz M (LamFam E Psm Prd lev X wτ S τ M)) Cnz

/-- **The old bundle FROM the minimal bundle + certificate + internal glue owner**. -/
def old_FinalAnalyticProviders_of_minimal {τC : FixedTupleC V} {W : WeightSystem τC} {K : ℕ}
    {h : ℕ → ℝ} {F : ℝ → ℝ} {E : Finset ℕ} {Psm Prd : ℕ → ℝ → Finset ℕ} {lev X : ℝ → ℝ}
    {wτ : ℝ → ℝ → ℕ → ℝ} {r : ℕ} {Sd : ResearchBankV23.SingularFactors.SingularData} {LF I : ℝ}
    {N Li : ℕ → ℝ} {phiW : ℝ} {model : ℕ → ℕ → PrincipalModel h} {Kh : ℕ} {EAB : ℕ → ℝ}
    {Us Ur : ℕ → ℕ → Finset ℕ} {D0 D1 D2 Db DEnz : ℕ → (Finset ℕ → ℝ) → ℝ} {Ct Cnz err : ℝ}
    {muF : ℝ} {DIClass : KloostermanData → Prop}
    (Mn : MinimalExternalAnalyticProviders τC W K h F Psm Prd lev X wτ r Sd LF I N Li phiW model
      Kh EAB Us Ur D0 D1 D2 Db muF DIClass)
    (C : FunctionalKernelCertificate muF (LF / I))
    (Gl : InternalGlueOwner τC W h E Psm Prd lev X wτ N Li phiW model EAB D0 D1 D2 Db DEnz Ct Cnz
      err DIClass) :
    FinalAnalyticProviders τC W K h F E Psm Prd lev X wτ r Sd LF I N Li phiW model Kh EAB Us Ur
      D0 D1 D2 Db DEnz Ct Cnz err muLo WHi muF DIClass where
  rosser := Mn.rosser
  tuple := Mn.tuple
  euler := Mn.euler
  hat := Mn.hat
  di := Mn.di
  zeroFreq := Mn.zeroFreq
  oneLarge := Mn.oneLarge
  twoLarge := Mn.twoLarge
  boundary := Mn.boundary
  nonzero := Gl.nonzero
  tensor := Gl.tensor
  s1 := Mn.s1
  cert := (certificate_iff_thin muF (LF / I)).1 C

/-- The remainder-free tensor provider of the degenerate route (recorded ONLY as a mismatch
witness: it is the pair baseline itself, not an external theorem). -/
structure DegenerateTensorProvider (τC : FixedTupleC V) (W : WeightSystem τC) (N : ℕ → ℝ)
    {h : ℕ → ℝ} (model : ℕ → ℕ → PrincipalModel h) (pref : ℕ → ℝ)
    (Λ : ℕ → ℝ → ℕ → Finset ℕ → ℝ) (EAB : ℕ → ℝ) (Ct err : ℝ) : Prop where
  Ct_nonneg : 0 ≤ Ct
  decomp : ∀ S τ M, Pair τC W M / N M ≤
    (model S M).Mnew (pref M) (Λ S τ M) + Ct * Real.sqrt |EAB M| + 90 + err

/-- **Degenerate reconstruction of the old bundle** (LEAN BANK): every V28 field except
rosser/tuple/euler/hat/s1/cert/tensor is discharged vacuously with zero branch functionals. -/
def old_FinalAnalyticProviders_of_degenerate {τC : FixedTupleC V} {W : WeightSystem τC} {K : ℕ}
    {h : ℕ → ℝ} {F : ℝ → ℝ} {E : Finset ℕ} {Psm Prd : ℕ → ℝ → Finset ℕ} {lev X : ℝ → ℝ}
    {wτ : ℝ → ℝ → ℕ → ℝ} {r : ℕ} {Sd : ResearchBankV23.SingularFactors.SingularData} {LF I : ℝ}
    {N Li : ℕ → ℝ} {phiW : ℝ} {model : ℕ → ℕ → PrincipalModel h} {Kh : ℕ} {EAB : ℕ → ℝ}
    {Us Ur : ℕ → ℕ → Finset ℕ} {Ct err : ℝ} {muF : ℝ}
    (hR : RosserScalarProvider K h F Psm Prd lev X) (hT : PrimeHarmonicTupleProvider h Prd X wτ)
    (P : PrincipalEulerProvider h r Sd LF I (S0 τC W) N Li phiW model)
    (hH : HatReferenceApproximationProvider Kh EAB) (h1 : S1Contract (S1 τC W) N muF)
    (C : FunctionalKernelCertificate muF (LF / I))
    (T : DegenerateTensorProvider τC W N model (pref Li phiW N) (LamFam E Psm Prd lev X wτ) EAB
      Ct err) :
    FinalAnalyticProviders τC W K h F E Psm Prd lev X wτ r Sd LF I N Li phiW model Kh EAB Us Ur
      (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) Ct 0 err
      muLo WHi muF (fun _ => False) where
  rosser := hR
  tuple := hT
  euler := P
  hat := hH
  di := DIClassRealization.di_provider_empty_class _
  zeroFreq := ZeroBranchComposition.branchClassBound_zero Us Ur
  oneLarge := ZeroBranchComposition.branchClassBound_zero Us Ur
  twoLarge := ZeroBranchComposition.branchClassBound_zero Us Ur
  boundary := ZeroBranchComposition.branchClassBound_zero Us Ur
  nonzero := fun _ _ M =>
    NonzeroPruning.nonzero_realization_zero _ (Nat.cast_nonneg M) le_rfl
  tensor := ⟨T.Ct_nonneg, fun S τ M => by
    have := T.decomp S τ M
    simp only [sumDE, add_zero, abs_zero, max_self]
    linarith⟩
  s1 := h1
  cert := (certificate_iff_thin muF (LF / I)).1 C

end ProviderElimination
end ResearchBankV29
end Erdos287
