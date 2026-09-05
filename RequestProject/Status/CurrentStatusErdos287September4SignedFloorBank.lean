import RequestProject.CurrentProgramme.Erdos287September4PhysicalW
import RequestProject.CurrentProgramme.Erdos287September4CanonicalStateSign
import RequestProject.CurrentProgramme.Erdos287September4T0T2DeepEvenCancellation
import RequestProject.CurrentProgramme.Erdos287September4BsrcLocalMobiusCollapse
import RequestProject.CurrentProgramme.Erdos287September4BoundaryDivisorLattice
import RequestProject.CurrentProgramme.Erdos287September4SignedBsrcCompiler
import RequestProject.CurrentProgramme.Erdos287September4BoundaryCertificateChecker
import RequestProject.CurrentProgramme.Erdos287September4LargeLTailCompiler

/-!
# Append-only status layer — the September-4 signed `B_src` floor bank

This module is **append-only** and is a *strictly later* layer than the September-3 status
modules: no earlier row is deleted, edited or downgraded.  Rows this layer does not mention
keep their earlier value; in particular the September-3 rows

    24-window finite extension / extended ceiling 67108856338751594 /
    Pratt engine / 2-adic Möbius pairing / odd-divisor Tot source identity /
    T = T⁰ − T² split / d and 4d fixed-residue arithmetic /
    canonical ≤4 interval compiler / conditional fixed-residue AP compiler

remain `kernelProved`, and

    AP analytic socket / Maynard owner / Maynard numerical constant /
    Maynard activation threshold / numerical E_T / E_L / global effectivity / Erdős #287

keep their earlier `externalUninhabited` / `notBanked` / `conditionalOpen` / `open_` values.
Nothing proved in the September-4 source algebra changes any of them.

```
PHYSICAL W                                   : kernelProved
W SUPPORT ⊆ [7/10, 9/10]                     : kernelProved
W SUP NORM = 1                               : kernelProved
VAR(W) = 2  (Mathlib eVariationOn)           : kernelProved
C_W = 2‖W‖_∞ + Var(W) = 4                    : kernelProved
CANONICAL STATE SIGN INVARIANCE              : kernelProved
T⁰−T² DEEP-EVEN CANCELLATION                 : kernelProved
INTERIOR LOCAL MÖBIUS COLLAPSE               : kernelProved
BOUNDARY DATATYPE                            : built
BOUNDARY EXHAUSTIVENESS                      : partial_
SIGNED B_src SYMBOLIC COMPILER (finite)      : kernelProved
ANALYTIC LIMIT OF THE COMPILER               : externalNotFormalized
SECONDARY POLE (analytic residue −1/4)       : externalNotFormalized
SECONDARY POLE ⇒ SHOULDER (algebra)          : kernelProved
EXACT RATIONAL BUDGET  sum < 1e-6            : kernelProved
BOUNDARY CERTIFICATE CHECKER                 : kernelProved
BOUNDARY NUMERICAL CERTIFICATE               : notBuilt
LOG 42.9–62.5 FLOOR                          : conditionalKernel
ENVELOPE MONOTONICITY / ENDPOINT             : kernelProved
LOG 62.5–3727 TAIL (floor claim)             : conditionalKernel
TOT-BSRC-SIGNED-CANONICAL-FLOOR-DIRECTED45   : strictlyReduced
MERTENS ENVELOPE INPUT                       : externalUninhabited
MAYNARD OWNER / CONSTANT / THRESHOLD         : externalNotFormalized / notBanked / notBanked
NUMERICAL E_T                                : notBanked
E_T / E_L                                    : conditionalOpen
GLOBAL EFFECTIVITY                           : effectivityOpen
ERDŐS #287                                   : open_
```

`Status` is **metadata**: no row is a proof claim.  The firewall theorems of §4 and the
row-backing theorems of §5 are machine-checked.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace September4SignedFloorBankStatus

/-! ## §1  The status vocabulary of this layer -/

/-- The status vocabulary of the September-4 layer. -/
inductive Status
  /-- Proved in the Lean kernel. -/
  | kernelProved
  /-- A datatype / interface that exists and is used, but is not itself a theorem. -/
  | built
  /-- A Lean theorem whose antecedent is an external (uninhabited) hypothesis socket. -/
  | conditionalKernel
  /-- Established only in part; the residual obligation is isolated and stated. -/
  | partial_
  /-- An external hypothesis socket for which this development builds no inhabitant. -/
  | externalUninhabited
  /-- Owned by the literature or by an external computation; deliberately not formalised. -/
  | externalNotFormalized
  /-- A numerical value that is deliberately not banked. -/
  | notBanked
  /-- Data that has not been generated or supplied at all. -/
  | notBuilt
  /-- Strictly reduced relative to the earlier layer, but not closed. -/
  | strictlyReduced
  /-- Conditional, and open. -/
  | conditionalOpen
  /-- An open effectivity obligation. -/
  | effectivityOpen
  /-- Open. -/
  | open_
  deriving DecidableEq, Fintype, Repr

/-! ## §2  Nodes of this layer -/

/-- Nodes of the September-4 signed-floor ledger. -/
inductive Node
  /-- The exact physical weight `W`. -/
  | physicalW
  /-- Its support inclusion. -/
  | wSupport
  /-- Its sup norm. -/
  | wSupNorm
  /-- Its total variation (Mathlib `eVariationOn`). -/
  | wVariation
  /-- The compiler constant `C_W = 4`. -/
  | cW4
  /-- Canonical-state sign invariance. -/
  | canonicalStateSign
  /-- `T⁰ − T²` deep-even cancellation. -/
  | t0t2DeepEven
  /-- The interior divisor-lattice Möbius collapse. -/
  | interiorMobiusCollapse
  /-- The boundary-cause datatype and record. -/
  | boundaryDatatype
  /-- Exhaustiveness of the physical boundary-cause list. -/
  | boundaryExhaustiveness
  /-- The finite/truncated signed `B_src` symbolic compiler. -/
  | signedCompilerFinite
  /-- The analytic limit (integral / convergence) of that compiler. -/
  | signedCompilerAnalyticLimit
  /-- The analytic proof of the universal secondary residue `−1/4`. -/
  | secondaryPoleAnalytic
  /-- The algebraic shoulder implication downstream of the residue. -/
  | secondaryPoleShoulder
  /-- The exact rational budget arithmetic. -/
  | exactRationalBudget
  /-- The boundary certificate checker. -/
  | boundaryChecker
  /-- Actual numerical boundary certificate data. -/
  | boundaryNumericalCertificate
  /-- The compact slab `42.9 ≤ log X ≤ 62.5`. -/
  | log42p9To62p5Floor
  /-- Monotonicity and endpoint of the absolute tail envelope. -/
  | tailEnvelope
  /-- The tail floor claim on `62.5 ≤ log X ≤ 3727`. -/
  | log62p5To3727Tail
  /-- The directed signed canonical floor node of the research bank. -/
  | totBsrcSignedCanonicalFloorDirected45
  /-- The explicit-Mertens envelope input. -/
  | mertensEnvelopeInput
  /-- The analytic owner of the AP input (Maynard-type theorem). -/
  | maynardAnalyticOwner
  /-- The numerical constant of that owner. -/
  | maynardNumericalConstant
  /-- Its activation threshold. -/
  | maynardActivationThreshold
  /-- A numerical value for `E_T`. -/
  | numericalET
  /-- The directed medium-range `E_T`. -/
  | eT
  /-- The leakage error `E_L`. -/
  | eL
  /-- Global effectivity of the #287 programme. -/
  | globalEffectivity
  /-- Erdős #287 itself. -/
  | erdos287
  deriving DecidableEq, Fintype, Repr

/-! ## §3  The authoritative ledger -/

/-- The authoritative September-4 status assignment. -/
def status : Node → Status
  | Node.physicalW => Status.kernelProved
  | Node.wSupport => Status.kernelProved
  | Node.wSupNorm => Status.kernelProved
  | Node.wVariation => Status.kernelProved
  | Node.cW4 => Status.kernelProved
  | Node.canonicalStateSign => Status.kernelProved
  | Node.t0t2DeepEven => Status.kernelProved
  | Node.interiorMobiusCollapse => Status.kernelProved
  | Node.boundaryDatatype => Status.built
  | Node.boundaryExhaustiveness => Status.partial_
  | Node.signedCompilerFinite => Status.kernelProved
  | Node.signedCompilerAnalyticLimit => Status.externalNotFormalized
  | Node.secondaryPoleAnalytic => Status.externalNotFormalized
  | Node.secondaryPoleShoulder => Status.kernelProved
  | Node.exactRationalBudget => Status.kernelProved
  | Node.boundaryChecker => Status.kernelProved
  | Node.boundaryNumericalCertificate => Status.notBuilt
  | Node.log42p9To62p5Floor => Status.conditionalKernel
  | Node.tailEnvelope => Status.kernelProved
  | Node.log62p5To3727Tail => Status.conditionalKernel
  | Node.totBsrcSignedCanonicalFloorDirected45 => Status.strictlyReduced
  | Node.mertensEnvelopeInput => Status.externalUninhabited
  | Node.maynardAnalyticOwner => Status.externalNotFormalized
  | Node.maynardNumericalConstant => Status.notBanked
  | Node.maynardActivationThreshold => Status.notBanked
  | Node.numericalET => Status.notBanked
  | Node.eT => Status.conditionalOpen
  | Node.eL => Status.conditionalOpen
  | Node.globalEffectivity => Status.effectivityOpen
  | Node.erdos287 => Status.open_

/-! ## §4  Firewalls -/

/-- **`deepEven_is_not_floor_closure`.**  `KERNEL-PROVED`.  Deep-even cancellation is
kernel-proved while the compact-slab floor row is only conditional and the directed floor
node is only strictly reduced. -/
theorem deepEven_is_not_floor_closure :
    status Node.t0t2DeepEven = Status.kernelProved ∧
      status Node.log42p9To62p5Floor = Status.conditionalKernel ∧
      status Node.totBsrcSignedCanonicalFloorDirected45 = Status.strictlyReduced := by decide

/-- **`checker_coexists_with_missing_certificate`.**  `KERNEL-PROVED`.  The checker is
kernel-proved *and* no numerical certificate exists. -/
theorem checker_coexists_with_missing_certificate :
    status Node.boundaryChecker = Status.kernelProved ∧
      status Node.boundaryNumericalCertificate = Status.notBuilt := by decide

/-- **`secondaryPole_is_external`.**  `KERNEL-PROVED`.  Only the downstream algebra is
kernel-proved; the analytic residue is external. -/
theorem secondaryPole_is_external :
    status Node.secondaryPoleAnalytic = Status.externalNotFormalized ∧
      status Node.secondaryPoleShoulder = Status.kernelProved := by decide

/-- **`maynard_is_not_asserted`.**  `KERNEL-PROVED`.  No Maynard theorem, constant or
threshold is banked by this layer, and no numerical `E_T` is banked. -/
theorem maynard_is_not_asserted :
    status Node.maynardAnalyticOwner = Status.externalNotFormalized ∧
      status Node.maynardNumericalConstant = Status.notBanked ∧
      status Node.maynardActivationThreshold = Status.notBanked ∧
      status Node.numericalET = Status.notBanked := by decide

/-- **`mertens_is_not_asserted`.**  `KERNEL-PROVED`.  The explicit-Mertens envelope is an
uninhabited interface only. -/
theorem mertens_is_not_asserted :
    status Node.mertensEnvelopeInput = Status.externalUninhabited := by decide

/-- **`boundary_exhaustiveness_is_partial`.**  `KERNEL-PROVED`. -/
theorem boundary_exhaustiveness_is_partial :
    status Node.boundaryExhaustiveness = Status.partial_ ∧
      status Node.boundaryDatatype = Status.built := by decide

/-- **`erdos287_remains_open`.**  `KERNEL-PROVED`.  Nothing in this layer closes #287, and
`E_T`, `E_L` and global effectivity remain open. -/
theorem erdos287_remains_open :
    status Node.erdos287 = Status.open_ ∧
      status Node.eT = Status.conditionalOpen ∧
      status Node.eL = Status.conditionalOpen ∧
      status Node.globalEffectivity = Status.effectivityOpen := by decide

/-- **`source_algebra_does_not_upgrade_analytic_rows`.**  `KERNEL-PROVED`.  Every new
kernel-proved row of this layer is a *source-algebra* row: none of them equals the status of
an analytic row. -/
theorem source_algebra_does_not_upgrade_analytic_rows :
    status Node.interiorMobiusCollapse ≠ status Node.secondaryPoleAnalytic ∧
      status Node.canonicalStateSign ≠ status Node.maynardAnalyticOwner ∧
      status Node.signedCompilerFinite ≠ status Node.signedCompilerAnalyticLimit := by decide

/-! ## §5  Rows backed by the theorems they label -/

/-- The `physicalW` / `wSupport` rows are backed by the theorem they label. -/
theorem row_wSupport_backed :
    Function.support September4PhysicalW.W ⊆ Set.Icc (7 / 10 : ℝ) (9 / 10) :=
  September4PhysicalW.W_support_subset

/-- The `wSupNorm` row is backed by the theorem it labels. -/
theorem row_wSupNorm_backed : IsGreatest (Set.range September4PhysicalW.W) 1 :=
  September4PhysicalW.W_isGreatest_one

/-- The `wVariation` row is backed by the theorem it labels. -/
theorem row_wVariation_backed : eVariationOn September4PhysicalW.W Set.univ = 2 :=
  September4PhysicalW.physicalW_variation

/-- The `cW4` row is backed by the theorem it labels. -/
theorem row_cW4_backed : September4PhysicalW.C_W = 4 :=
  September4PhysicalW.physicalW_CW_eq_four

/-- The `canonicalStateSign` row is backed by the theorem it labels. -/
theorem row_canonicalStateSign_backed {d dlow dhigh j : ℕ} (hd : Squarefree d)
    (hsplit : d = dlow * dhigh) (hcop : Nat.Coprime dlow dhigh)
    (hj : ArithmeticFunction.cardDistinctFactors dhigh = j) :
    (ArithmeticFunction.moebius dlow : ℤ) * September4CanonicalStateSign.gState j
      = (ArithmeticFunction.moebius d : ℤ) :=
  September4CanonicalStateSign.canonicalStateSign_product hd hsplit hcop hj

/-- The `t0t2DeepEven` row is backed by the theorem it labels. -/
theorem row_t0t2DeepEven_backed (kappa : ℕ → ℕ → ℝ) (Wt B : ℕ → ℝ) (Y : ℕ → ℕ)
    (d : ℕ) (R : Finset ℕ) :
    ∑ r ∈ R.filter (fun r => Even r ∧ 2 * d ≤ Y (d * r)),
        (September4T0T2.srcTerm kappa Wt B d r * September4T0T2.ind (d ≤ Y (d * r))
          - September4T0T2.srcTerm kappa Wt B d r
              * September4T0T2.ind (2 * d ≤ Y (d * r))) = 0 :=
  September4T0T2.t0t2DeepEvenCancellation45 kappa Wt B Y d R

/-- The `interiorMobiusCollapse` row is backed by the theorem it labels. -/
theorem row_interiorMobiusCollapse_backed (Bloc bloc : ℕ → ℚ) {q : ℕ} (hq : Squarefree q) :
    ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℚ)
        * September4BsrcCollapse.Bsrc Bloc d * September4BsrcCollapse.beta bloc (q / d)
      = ∏ p ∈ q.primeFactors, (bloc p - Bloc p) :=
  September4BsrcCollapse.interiorLocalMobiusCollapse45 Bloc bloc hq

/-- The `signedCompilerFinite` row is backed by the theorem it labels. -/
theorem row_signedCompilerFinite_backed (Bsrc Wt : ℕ → ℝ) (Y : ℕ → ℕ) (D M : Finset ℕ)
    (I0 I2 : ℕ → ℝ) :
    September4SignedCompiler.R_signed Bsrc Wt Y D M I0 I2
      = -4 * ∑ d ∈ D.filter (fun d => Odd d),
          September4SignedCompiler.signedContribution Bsrc Wt Y M I0 I2 d :=
  September4SignedCompiler.signedBsrcSourceIdentity45 Bsrc Wt Y D M I0 I2

/-- The `exactRationalBudget` row is backed by the theorem it labels. -/
theorem row_exactRationalBudget_backed :
    September4Checker.poleBudget + September4Checker.oscillatoryBudget
      < September4Checker.targetBudget :=
  September4Checker.budget_sum_lt_target

/-- The `boundaryChecker` row is backed by the theorem it labels — an implication whose
second antecedent is the uninhabited domination socket. -/
theorem row_boundaryChecker_backed (c : September4Checker.BoundaryCertificate)
    (h : September4Checker.checkCert c = true)
    (D : September4Checker.BoundaryDominationInput c) {L : ℝ}
    (hL : (September4Checker.slabLo : ℝ) ≤ L) (hL' : L ≤ (September4Checker.slabHi : ℝ)) :
    D.floorRatio L < 1 / 10 ^ 6 :=
  September4Checker.boundaryCertificateChecker_sound c h D hL hL'

/-- The `boundaryNumericalCertificate` row is backed by the fact it labels: the bank of
actual certificate data is empty. -/
theorem row_boundaryNumericalCertificate_backed :
    September4Checker.bankedCertificates = [] :=
  September4Checker.no_banked_certificate

/-- The `tailEnvelope` row is backed by the theorems it labels. -/
theorem row_tailEnvelope_backed :
    StrictAntiOn September4LargeLTail.envelope (Set.Ici (4 : ℝ)) ∧
      September4LargeLTail.envelope (125 / 2) < 1 / 10 ^ 6 :=
  ⟨September4LargeLTail.envelope_strictAntiOn, September4LargeLTail.envelope_endpoint⟩

end September4SignedFloorBankStatus
end Erdos287
