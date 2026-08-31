import Mathlib
import RequestProject.Erdos287.SmallQSmallRAdapters3221
import RequestProject.Erdos287.HardDyadicProviders3221
import RequestProject.Erdos287.BalancedSevenComparisonCompiler3221

/-!
# V24, §12–§14 — the full-`q` provider-exhaustiveness compiler

`SP2-BALANCED7-FULL-Q45`  (OPEN — conditional compiler only)

This module contains **implications only**.  It gathers the three sector suppliers of the
full-`q` partition into one antecedent bundle and derives the full-`q` bound.  Two firewalls
are proved alongside:

* `allQProviderInputs_currently_unavailable` — the bundle is currently *unsatisfiable*,
  because the hard dyadic census is incomplete (`hardDyadicExhaustiveness_not_automatic`).
  So nothing downstream of this compiler is in force;
* `fullQ_closure_is_not_effective` — the full-`q` bound is an asymptotic statement and does
  not, by itself, produce an explicit threshold `M₀`; the effective status stays separate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ArithmeticFunction
open scoped BigOperators

namespace Erdos287
namespace V24FullQCompiler

open Erdos287.V24FullQ Erdos287.V24Adapters Erdos287.V24Hard

/-! ## §12.1  Parameters of the full-`q` compiler -/

/-- The literal data the full-`q` compiler is run on. -/
structure FullQParams where
  /-- The structural cut `u = ⌊X^{1/3}⌋`. -/
  u : ℕ
  /-- The affine modulus `N = 2P + s`. -/
  N : ℕ
  /-- The generated seven-prime coefficient. -/
  coeff : ℕ × ℕ → ℝ
  /-- Declared `q`-range of the SmallQ adapter. -/
  qRange : Finset ℕ
  /-- Declared `r`-range of the SmallQ adapter. -/
  rRange : Finset ℕ
  /-- The affine sign as an integer. -/
  sgn : ℤ
  /-- The affine sign. -/
  s : Erdos287.Vaughan.AffineSign
  /-- Norm claimed by the SmallQ provider. -/
  smallQNorm : ℝ
  /-- Norm claimed by the SmallR provider. -/
  smallRNorm : ℝ
  /-- Norm claimed by the hard dyadic providers, after reassembly. -/
  hardNorm : ℝ
  /-- The intended provider of the two small sectors. -/
  provider : Provider

/-- The literal full-`q` sum the compiler controls. -/
noncomputable def fullQSum (prm : FullQParams) : ℝ :=
  ∑ x ∈ Nat.divisorsAntidiagonal prm.N, (moebius x.1 : ℝ) * Real.log x.2 * prm.coeff x

/-! ## §12.2  The antecedent bundle -/

/-- **`BalancedSevenAllQProviderInputs`** — `CONDITIONAL / UNINHABITED ANTECEDENTS`.

All three sectors supplied, plus the hard dyadic exhaustiveness interface. -/
structure BalancedSevenAllQProviderInputs (prm : FullQParams) : Prop where
  /-- The SmallQ literal Type-I adapter. -/
  smallQ : Affine287SP2SmallQTypeIAdapterInput prm.u prm.N prm.coeff prm.qRange prm.rRange
    prm.sgn prm.s prm.smallQNorm prm.provider
  /-- The SmallR switched Type-I adapter, with its switch flags. -/
  smallR : Affine287SP2SmallRSwitchTypeIInput prm.u prm.N prm.coeff prm.smallRNorm prm.provider
    false true true false true true
  /-- Every admissible hard dyadic cell is owned. -/
  hardExhaustive : HardDyadicProviderExhaustiveness287Input
  /-- The reassembled hard sector bound. -/
  hardBound : |sigmaHard prm.u prm.N prm.coeff| ≤ prm.hardNorm
  /-- Theorem-hypothesis dictionary for the hard sector. -/
  hardDictionary : prm.hardNorm ≤ sectorTargetNorm prm.N

/-- **`allQProviderExhaustive_of_inputs`** — `CONDITIONAL`.

Given the bundle, each of the three sectors meets the physical saving. -/
theorem allQProviderExhaustive_of_inputs {prm : FullQParams}
    (h : BalancedSevenAllQProviderInputs prm) :
    |sigmaSmallQ prm.u prm.N prm.coeff| ≤ sectorTargetNorm prm.N ∧
      |sigmaSmallR prm.u prm.N prm.coeff| ≤ sectorTargetNorm prm.N ∧
      |sigmaHard prm.u prm.N prm.coeff| ≤ sectorTargetNorm prm.N :=
  ⟨(smallQ_closed_of_literal_typeI_adapter h.smallQ).1,
   (smallR_closed_of_switched_typeI_adapter h.smallR).1,
   le_trans h.hardBound h.hardDictionary⟩

/-- **`sp2BalancedSevenFullQ_of_inputs`** — `CONDITIONAL`.

`SP2-BALANCED7-FULL-Q45`: the whole `μ · log` factorisation sum obeys the physical saving
up to the fixed factor `3` coming from the three sectors. -/
theorem sp2BalancedSevenFullQ_of_inputs {prm : FullQParams}
    (h : BalancedSevenAllQProviderInputs prm) :
    |fullQSum prm| ≤ 3 * sectorTargetNorm prm.N := by
  obtain ⟨h1, h2, h3⟩ := allQProviderExhaustive_of_inputs h
  have hre : fullQSum prm =
      sigmaSmallQ prm.u prm.N prm.coeff + sigmaSmallR prm.u prm.N prm.coeff
        + sigmaHard prm.u prm.N prm.coeff :=
    sigma_threeWay_reassembly prm.u prm.N prm.coeff
  rw [hre]
  calc |sigmaSmallQ prm.u prm.N prm.coeff + sigmaSmallR prm.u prm.N prm.coeff
          + sigmaHard prm.u prm.N prm.coeff|
      ≤ |sigmaSmallQ prm.u prm.N prm.coeff| + |sigmaSmallR prm.u prm.N prm.coeff|
        + |sigmaHard prm.u prm.N prm.coeff| := abs_add_three _ _ _
    _ ≤ 3 * sectorTargetNorm prm.N := by linarith

/-! ## §13  Conditional Balanced7 asymptotic closure -/

/-- **`balancedSevenAsymptotic_of_fullQ_and_comparison`** — `CONDITIONAL`.

Full-`q` provider exhaustiveness together with the V23 comparison compiler gives, at the
shared cutoff, both the full-`q` bound and the repository's comparison object.  Neither
antecedent is inhabited here. -/
theorem balancedSevenAsymptotic_of_fullQ_and_comparison
    {prm : FullQParams} {cprm : Erdos287.V23CompilerLayer.ComparisonParams} {B0 Dcut : ℝ}
    (hfull : BalancedSevenAllQProviderInputs prm)
    (hcmp : Erdos287.V23CompilerLayer.BalancedSevenComparisonInputs cprm)
    (hB0 : 0 < B0) (hDcut : Dcut = Erdos287.V20Compiler.highConductorCutoff B0 cprm.X) :
    |fullQSum prm| ≤ 3 * sectorTargetNorm prm.N ∧
      ∃ hard model err : ℝ,
        Erdos287.V20Compiler.MuLogComparisonAtCutoff cprm.X Dcut B0 hard model err :=
  ⟨sp2BalancedSevenFullQ_of_inputs hfull, _, _, _,
   Erdos287.V23CompilerLayer.balancedSevenComparison_of_inputs hcmp hB0 hDcut⟩

/-! ## §14  Firewalls -/

/-- **`allQProviderInputs_currently_unavailable`.**  `LEAN_PROVED`.

The full-`q` antecedent bundle is *unsatisfiable in the current repository*: the hard dyadic
census is incomplete, so `HardDyadicProviderExhaustiveness287Input` is refuted.  Hence the
compiler above is in force for no parameter set, and `SP2-BALANCED7-FULL-Q45` is OPEN. -/
theorem allQProviderInputs_currently_unavailable (prm : FullQParams) :
    ¬ BalancedSevenAllQProviderInputs prm := fun h =>
  hardDyadicExhaustiveness_not_automatic h.hardExhaustive

/-- **`fullQ_status_stays_open`.**  `LEAN_PROVED`.

The full-`q` compiler is an asymptotic device.  A well-formed Balanced7 status record whose
only exceptional-character treatment is ineffective carries no explicit threshold and is not
effectively closed, whatever the full-`q` status says. -/
theorem fullQ_status_stays_open (R : Erdos287.V23LowCond.BalancedSevenStatusRecord)
    (hw : Erdos287.V23LowCond.WellFormedStatus R) (hine : R.exceptionalIneffective = true) :
    R.explicitThreshold = none ∧ R.effectiveClosed = false := by
  refine ⟨hw.2 hine, ?_⟩
  by_contra hc
  have hEff : R.effectiveClosed = true := by
    cases h : R.effectiveClosed
    · exact absurd h hc
    · rfl
  exact hw.1 hEff (hw.2 hine)

/-- **`fullQ_bound_gives_no_threshold`.**  `LEAN_PROVED`.

Formally: the full-`q` conclusion is not a statement about any threshold `M₀`, since it holds
for the identically-zero coefficient at every `N`.  Effective closure therefore remains a
separate status. -/
theorem fullQ_bound_gives_no_threshold :
    ∀ N : ℕ, ∃ c : ℕ × ℕ → ℝ, |∑ x ∈ Nat.divisorsAntidiagonal N,
      (moebius x.1 : ℝ) * Real.log x.2 * c x| ≤ 3 * sectorTargetNorm N := by
  intro N
  refine ⟨fun _ => 0, ?_⟩
  simp only [mul_zero, Finset.sum_const_zero, abs_zero]
  have := sectorTargetNorm_nonneg N
  linarith

end V24FullQCompiler
end Erdos287
