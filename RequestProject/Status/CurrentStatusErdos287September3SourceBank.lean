import RequestProject.CurrentProgramme.Erdos287September3FiniteExtension24Window
import RequestProject.CurrentProgramme.Erdos287September3TotTwoAdicMobiusPairing
import RequestProject.CurrentProgramme.Erdos287September3TotFixedResidueArithmetic
import RequestProject.CurrentProgramme.Erdos287September3TotFixedResidueConditionalCompiler
import RequestProject.CurrentProgramme.Erdos287September3CanonicalSplitFourInterval

/-!
# Append-only status layer — the September-3 finite-chain / 2-adic source bank

This module is **append-only** and is a *strictly later* layer than the September-2 status
modules: no earlier row is deleted or edited.  Rows that this layer does not mention keep
their earlier value; the one row that this layer *upgrades* is the finite bank ceiling, and
the upgrade is recorded here rather than by editing the earlier layer.

```
FINITE 24-WINDOW EXTENSION (ceiling 67108856338751594) : kernelProved
COVERS 38643198608805673                               : kernelProved
2-ADIC MÖBIUS PAIR                                     : kernelProved
ODD-DIVISOR TOT SOURCE IDENTITY                        : kernelProved
ODD-d FIXED-RESIDUE ARITHMETIC (modulus d)             : kernelProved
4d FIXED-RESIDUE ARITHMETIC (modulus 4d)               : kernelProved
TOT SOURCE SPLIT  T = T⁰ − T²                          : kernelProved
CANONICAL FOUR-INTERVAL GEOMETRY                       : kernelProved
TOT FIXED-RESIDUE CONDITIONAL COMPILER                 : conditionalKernel (implication only)
AP ANALYTIC SOCKET                                     : externalUninhabited
MAYNARD ANALYTIC OWNER                                 : externalNotFormalized
MAYNARD NUMERICAL CONSTANT                             : notBanked
ENDPOINT-SUPREMUM FIELD                                : notBanked
E_T DIRECTED MEDIUM                                    : conditionalOpen
E_L                                                    : conditionalOpen
E_M                                                    : paperClosedExternal (retained)
MEDIUM ANALYTIC BRANCH                                 : open_
GLOBAL EFFECTIVITY                                     : effectivityOpen
ERDŐS #287                                             : open_
```

`Status` is **metadata**: no row is a proof claim.  The firewall theorems below, and the
row-backing theorems of §5, are machine-checked.

**FIREWALL — FINITE-CERTIFICATE-COVERAGE.**  The 24-window extension is an *arithmetic
finite result only*.  It says that no counterexample has maximum below an explicit ceiling.
It does **not** assert that the medium analytic branch is closed, and the ledger records
`mediumAnalyticBranch = open_` next to `finite24WindowExtension = kernelProved`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace September3SourceBankStatus

/-! ## §1  The status vocabulary of this layer -/

/-- The status vocabulary of the September-3 layer. -/
inductive Status
  /-- Proved in the Lean kernel. -/
  | kernelProved
  /-- A Lean theorem whose research antecedent is an uninhabited hypothesis socket. -/
  | conditionalKernel
  /-- An external hypothesis socket for which this development builds no inhabitant. -/
  | externalUninhabited
  /-- Owned by the literature; deliberately not formalised here. -/
  | externalNotFormalized
  /-- A numerical value that is deliberately not banked. -/
  | notBanked
  /-- Closed in the published literature; never a Lean theorem here. -/
  | paperClosedExternal
  /-- Conditional, and open. -/
  | conditionalOpen
  /-- An open effectivity obligation. -/
  | effectivityOpen
  /-- Open. -/
  | open_
  deriving DecidableEq, Fintype, Repr

/-! ## §2  Nodes of this layer -/

/-- Nodes of the September-3 finite-chain / 2-adic source ledger. -/
inductive Node
  /-- The 24-window finite extension of the unconditional bank. -/
  | finite24WindowExtension
  /-- The comparison `38643198608805673 < 67108856338751594`. -/
  | arithmeticCoverageEndpoint
  /-- The 2-adic Möbius pair coefficient. -/
  | twoAdicMobiusPair
  /-- The exact odd-divisor Tot source identity. -/
  | oddDivisorTotSource
  /-- Family-`0` fixed-residue arithmetic, modulus `d`. -/
  | fixedResidueModulusD
  /-- Family-`2` fixed-residue arithmetic, modulus `4d`. -/
  | fixedResidueModulusFourD
  /-- The algebraic Tot source split `T = T⁰ − T²`. -/
  | totSourceSplit
  /-- The canonical `n^ν` split four-interval geometry. -/
  | canonicalFourInterval
  /-- The conditional fixed-residue `E_T` compiler. -/
  | totFixedResidueConditionalCompiler
  /-- The external AP-discrepancy hypothesis socket. -/
  | apAnalyticSocket
  /-- The analytic owner of the AP input (Maynard-type theorem). -/
  | maynardAnalyticOwner
  /-- Any numerical constant coming from that analytic owner. -/
  | maynardNumericalConstant
  /-- An endpoint-supremum field in the socket. -/
  | endpointSupremumField
  /-- The directed medium-range `E_T`. -/
  | eTDirectedMedium
  /-- The leakage error `E_L`. -/
  | eL
  /-- The model error `E_M` (value retained from the earlier layer). -/
  | eM
  /-- The medium analytic branch as a whole. -/
  | mediumAnalyticBranch
  /-- Global effectivity of the #287 programme. -/
  | globalEffectivity
  /-- Erdős #287 itself. -/
  | erdos287
  deriving DecidableEq, Fintype, Repr

/-! ## §3  The authoritative ledger -/

/-- The authoritative September-3 status assignment. -/
def status : Node → Status
  | Node.finite24WindowExtension => Status.kernelProved
  | Node.arithmeticCoverageEndpoint => Status.kernelProved
  | Node.twoAdicMobiusPair => Status.kernelProved
  | Node.oddDivisorTotSource => Status.kernelProved
  | Node.fixedResidueModulusD => Status.kernelProved
  | Node.fixedResidueModulusFourD => Status.kernelProved
  | Node.totSourceSplit => Status.kernelProved
  | Node.canonicalFourInterval => Status.kernelProved
  | Node.totFixedResidueConditionalCompiler => Status.conditionalKernel
  | Node.apAnalyticSocket => Status.externalUninhabited
  | Node.maynardAnalyticOwner => Status.externalNotFormalized
  | Node.maynardNumericalConstant => Status.notBanked
  | Node.endpointSupremumField => Status.notBanked
  | Node.eTDirectedMedium => Status.conditionalOpen
  | Node.eL => Status.conditionalOpen
  | Node.eM => Status.paperClosedExternal
  | Node.mediumAnalyticBranch => Status.open_
  | Node.globalEffectivity => Status.effectivityOpen
  | Node.erdos287 => Status.open_

/-! ## §4  Firewalls -/

/-- **`socket_is_not_kernelProved`.**  `KERNEL-PROVED`.  An uninhabited external socket is
never a kernel-proved row. -/
theorem socket_is_not_kernelProved :
    status Node.apAnalyticSocket ≠ status Node.finite24WindowExtension := by decide

/-- **`finiteCoverage_does_not_close_medium_branch`.**  `KERNEL-PROVED`.  The finite
24-window extension is kernel-proved while the medium analytic branch stays open: the finite
certificate coverage does **not** close it. -/
theorem finiteCoverage_does_not_close_medium_branch :
    status Node.finite24WindowExtension = Status.kernelProved ∧
      status Node.mediumAnalyticBranch = Status.open_ := by decide

/-- **`conditionalCompiler_does_not_prove_erdos287`.**  `KERNEL-PROVED`. -/
theorem conditionalCompiler_does_not_prove_erdos287 :
    status Node.totFixedResidueConditionalCompiler ≠ Status.kernelProved ∧
      status Node.erdos287 = Status.open_ := by decide

/-- **`maynard_is_not_asserted`.**  `KERNEL-PROVED`.  The analytic owner is external and not
formalised, its numerical constant is not banked, and no endpoint-supremum field is banked. -/
theorem maynard_is_not_asserted :
    status Node.maynardAnalyticOwner = Status.externalNotFormalized ∧
      status Node.maynardNumericalConstant = Status.notBanked ∧
      status Node.endpointSupremumField = Status.notBanked := by decide

/-- **`eT_and_eL_remain_conditional`.**  `KERNEL-PROVED`. -/
theorem eT_and_eL_remain_conditional :
    status Node.eTDirectedMedium = Status.conditionalOpen ∧
      status Node.eL = Status.conditionalOpen := by decide

/-! ## §5  Rows backed by the theorems they label -/

/-- The `finite24WindowExtension` row is backed by the theorem it labels. -/
theorem row_finite24WindowExtension_backed (ce : Gap2CE) (h3 : 3 ≤ ce.M)
    (hM : ce.M ≤ 67108856338751594) : False :=
  ce.no_of_M_le_extendedCeiling h3 hM

/-- The `arithmeticCoverageEndpoint` row is backed by the theorem it labels. -/
theorem row_arithmeticCoverageEndpoint_backed :
    38643198608805673 < Erdos287.extendedCeiling :=
  Erdos287.arithmeticCoverage_exceeds_twoExp375

/-- The `twoAdicMobiusPair` row is backed by the theorem it labels. -/
theorem row_twoAdicMobiusPair_backed (w : ℕ → ℤ) (d : ℕ) (hd : Odd d) :
    September3TwoAdicPairing.sigmaEps w (2 * d) = - September3TwoAdicPairing.kappaEps w d :=
  September3TwoAdicPairing.twoAdicMobiusPairCoefficient w d hd

/-- The `fixedResidueModulusD` / `fixedResidueModulusFourD` rows are backed by the theorem
they label. -/
theorem row_fixedResidue_backed (d r u s : ℤ) (hd : Odd d) (hs : s = 1 ∨ s = -1) :
    (2 * d * r + s) ≡ s [ZMOD d] ∧ (4 * d * u + s) ≡ s [ZMOD (4 * d)] :=
  September3FixedResidue.fixedResidueFamilies_replace_generic_modulus d r u s hd hs

/-- The `totFixedResidueConditionalCompiler` row is backed by the implication it labels —
and only by that implication: its antecedent is the uninhabited socket. -/
theorem row_conditionalCompiler_backed
    (F : September3ConditionalCompiler.PhysicalSlotFamily) (w : ℕ → ℝ)
    (A : September3ConditionalCompiler.PhysicalFixedResidueAPBound F) :
    |September3ConditionalCompiler.E_T F w A|
      ≤ ∑ i ∈ F.slotIndex, |w i.1| * A.err (F.slotOf i) :=
  September3ConditionalCompiler.totLaneFixedResidueConditionalBound45 F w A

end September3SourceBankStatus
end Erdos287
