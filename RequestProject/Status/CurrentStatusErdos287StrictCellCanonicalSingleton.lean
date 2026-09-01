import Mathlib
import RequestProject.Status.PublicTreeReconciliation20260901
import RequestProject.CurrentProgramme.Erdos287StrictCellProductWeightBridge

/-!
# Authoritative status layer — Erdős #287, strict-cell canonical-singleton frontier

This module is **append-only** and **later**: no earlier status file is edited, and where the
two disagree about which node is the immediate physical frontier, this layer controls.

```
GENERIC FORD723 CENSUS:
    SUPERSEDED AS IMMEDIATE PHYSICAL FRONTIER
SP2-LABELLED64-CANONICALSINGLETON-PACKETCENSUS45:
    KERNEL-PROVED CONDITIONAL ON PHYSICAL BRIDGE
BALANCED7-SP2-STRICTCELL-PRODUCTWEIGHT-PHYSICAL-BRIDGE45:
    OPEN / UNINHABITED
SP2-LABELLED-SINGLETON-GENERATEDTYPEII45:
    OPEN ANALYTIC
ERDOS287:
    OPEN
```

*Superseded* means "no longer the immediate physical frontier"; it does **not** mean false,
and the Ford-(7.23) adapter files are preserved untouched.

Every `kernelProved` row below is tied to an actual theorem of this repository by a
`backing_*` declaration, and the conditional row is tied to an explicit implication whose
hypothesis is the uninhabited bridge.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace StrictCellSingletonStatus

open Erdos287.C0UnitaryFourierStatus
open Erdos287.StrictCellSingleton
open Erdos287.StrictCellBridge
open Erdos287.SP2Source
open Erdos287.V21PrimeBox
open ResearchStatus

/-! ## §1  Nodes of this layer -/

/-- Nodes recorded by the strict-cell canonical-singleton status layer. -/
inductive StrictCellNode
  /-- The generic Ford-(7.23) census. -/
  | genericFord723Census
  /-- `SP2-LABELLED64-CANONICALSINGLETON-PACKETCENSUS45`. -/
  | sp2Labelled64CanonicalSingletonPacketCensus45
  /-- `BALANCED7-SP2-STRICTCELL-PRODUCTWEIGHT-PHYSICAL-BRIDGE45`. -/
  | balanced7SP2StrictCellProductWeightPhysicalBridge45
  /-- `SP2-LABELLED-SINGLETON-GENERATEDTYPEII45`. -/
  | sp2LabelledSingletonGeneratedTypeII45
  /-- The unconditional finite package of this delta (counts, `H^*`, windows, energies). -/
  | strictCellFinitePackage
  /-- Erdős problem #287 itself. -/
  | erdos287
  deriving DecidableEq, Fintype, Repr

open StrictCellNode

/-- The authoritative ledger of this layer. -/
def strictCellLedger : StrictCellNode → ResearchStatus
  | genericFord723Census => superseded
  | sp2Labelled64CanonicalSingletonPacketCensus45 => conditionalSourcePin
  | balanced7SP2StrictCellProductWeightPhysicalBridge45 => open_
  | sp2LabelledSingletonGeneratedTypeII45 => open_
  | strictCellFinitePackage => kernelProved
  | erdos287 => open_

/-! ## §2  Ledger facts -/

/-- Erdős #287 is recorded as OPEN. -/
theorem erdos287_open : strictCellLedger erdos287 = open_ := rfl

/-- The generic Ford-(7.23) census is superseded as the immediate physical frontier. -/
theorem ford723Census_superseded : strictCellLedger genericFord723Census = superseded := rfl

/-- Superseded is not retracted and not false: the Ford adapter row is still a
`superseded` row, distinct from `retracted`. -/
theorem superseded_ne_retracted : strictCellLedger genericFord723Census ≠ retracted := by decide

/-- The packet census is conditional on the physical bridge, never unconditional. -/
theorem packetCensus_conditional :
    strictCellLedger sp2Labelled64CanonicalSingletonPacketCensus45 = conditionalSourcePin := rfl

/-- The physical bridge is open. -/
theorem bridge_open :
    strictCellLedger balanced7SP2StrictCellProductWeightPhysicalBridge45 = open_ := rfl

/-- The labelled singleton-generated Type-II input is open (analytic). -/
theorem typeII_open : strictCellLedger sp2LabelledSingletonGeneratedTypeII45 = open_ := rfl

/-- Exactly one row of this layer is unconditionally kernel-proved: the finite package. -/
theorem unique_kernelProved_row (n : StrictCellNode) :
    strictCellLedger n = kernelProved ↔ n = strictCellFinitePackage := by
  cases n <;> simp [strictCellLedger]

/-! ## §3  Backing theorems for the `kernelProved` row -/

/-- Backing: the exact weighted prime-vector → integer pushforward exists and its unit mass
is **not** automatically one. -/
theorem backing_omegaSharp_not_one :
    ∃ (C : SP2FixedCertificateData) (n : ℕ),
      SP2PacketNormalization C ∧ (omegaSharpFibre C n).Nonempty ∧
        OmegaSharp C unitWeight n ≠ 1 :=
  omegaSharp_one_not_automatic

/-- Backing: `s = |U| + 1`, `r = 8 - |U|`, `N = 9`. -/
theorem backing_coordCount (U : Finset (Fin 7)) :
    slotCount U + rankCount U = 9 :=
  ford_coordCount_eq_nine U

/-- Backing: the 64-branch census. -/
theorem backing_sixtyFour_branches : fordBranches.card = 64 := fordBranches_card

/-- Backing: seven physical prime coordinates and two terminal unit coordinates. -/
theorem backing_seven_two :
    ((Finset.univ : Finset (Fin 9)).filter
        (fun i => coordKind i = CoordKind.physicalPrime)).card = 7 ∧
      ((Finset.univ : Finset (Fin 9)).filter
        (fun i => coordKind i = CoordKind.terminalUnit)).card = 2 :=
  ⟨physicalPrimeCoords_card, terminalUnitCoords_card⟩

/-- Backing: the balanced-seven divisor-depth theorem and `H^* = -20`. -/
theorem backing_hStar (U : Finset (Fin 7)) :
    (depthSubsets U).card = 20 ∧ hStar U = -20 :=
  ⟨balancedSeven_divisorDepth U, hStar_eq_neg_twenty U⟩

/-- Backing: complement depth `6`. -/
theorem backing_complement_depth (U : Finset (Fin 7)) : complementDepth U = 6 :=
  complementDepth_eq_six U

/-- Backing: no `d_{h,j}` variables, and zero Ford hard-condition Perron contours, under the
strict-cell hypotheses. -/
theorem backing_no_d_no_contour {C : SP2FixedCertificateData} {U : Finset (Fin 7)}
    (h : StrictCellHypotheses C U) : dIndex C = ∅ ∧ perronContourCount C = 0 :=
  ⟨dIndex_eq_empty h, perronContourCount_eq_zero h⟩

/-- Backing: `k = 0` and `J = ∅` follow from the strict-cell hypotheses. -/
theorem backing_k_zero_J_empty {C : SP2FixedCertificateData} {U : Finset (Fin 7)}
    (h : StrictCellHypotheses C U) : C.k = 0 ∧ C.J = ∅ :=
  ⟨strictCell_k_zero h, strictCell_J_empty h⟩

/-- Backing: the deterministic canonical singleton selection. -/
theorem backing_canonical_singleton {U : Finset (Fin 7)} (h : U.card ≤ 3) :
    canonicalSingleton U ∉ U ∧ ∀ j ∉ U, canonicalSingleton U ≤ j :=
  ⟨canonicalSingleton_not_mem h, fun _ hj => canonicalSingleton_le h hj⟩

/-- Backing: the deterministic finite product-energy interface. -/
theorem backing_productEnergy (C : SP2FixedCertificateData) (f : Fin 7 → ℕ → ℝ) :
    ∑ v ∈ cellVectors C, (∏ i, f i (v i)) ^ 2 = ∏ i, ∑ p ∈ C.lam i, (f i p) ^ 2 :=
  productEnergy_factorises C f

/-! ## §4  Backing the conditional row and the two open rows -/

/-- The packet census really is an *implication* out of the uninhabited bridge: nothing here
asserts its hypothesis. -/
theorem census_is_an_implication
    (C : SP2FixedCertificateData) (U : Finset (Fin 7)) (Dat : PrimeBoxData)
    (w : (Fin 7 → ℕ) → ℤ) (K : ℕ → ℕ → ℂ) (m₀ n₀ : ℕ) (Hphys : ℤ) (cutoff : ℕ) (B : ℝ)
    (h : BalancedSevenSP2StrictCellProductWeightPhysicalBridge C U Dat w K m₀ n₀ Hphys cutoff
      B) :
    PhysicalK0Conditions720 C U ∧ Hphys = -20 ∧
      (∀ m n, K m n = xiOf K n₀ m * kappaOf K m₀ n) :=
  ⟨bridge_physicalK0 h, bridge_H_eq_neg_twenty h, bridge_kernel_factorisation h⟩

/-- The bridge row is open because the bridge is a genuine restriction: explicit data refute
it, and this repository constructs no inhabitant. -/
theorem backing_bridge_open :
    ∃ (C : SP2FixedCertificateData) (U : Finset (Fin 7)) (Dat : PrimeBoxData)
      (w : (Fin 7 → ℕ) → ℤ) (K : ℕ → ℕ → ℂ) (m₀ n₀ : ℕ) (Hphys : ℤ) (cutoff : ℕ) (B : ℝ),
      ¬ BalancedSevenSP2StrictCellProductWeightPhysicalBridge C U Dat w K m₀ n₀ Hphys cutoff
          B :=
  bridge_not_automatic

/-- The Type-II row is open analytic: the input is a genuine restriction and is not proved
here. -/
theorem backing_typeII_open :
    ¬ SP2LabelledSingletonGeneratedTypeIIInput countermodelCert ∅ 2 3 0 :=
  typeII_input_not_automatic

/-- A separation counterguard is banked for each of the two rank-one fields: cell weights and
kernels. -/
theorem backing_separation_counterguards :
    (¬ ∃ f : Fin 7 → ℕ → ℤ, ∀ v : Fin 7 → ℕ, diagonalWeight v = ∏ i, f i (v i)) ∧
      (¬ ∃ xi kappa : ℕ → ℂ, ∀ m n, diagonalKernel m n = xi m * kappa n) :=
  ⟨weight_not_product_separable, kernel_not_automatically_separable⟩

/-! ## §5  Scope guards -/

/-- This layer proves no analytic Type-II estimate: the only Type-II statement it contains is
the uninhabited input structure, together with a refutation at explicit parameters. -/
theorem no_analytic_typeII_claimed :
    strictCellLedger sp2LabelledSingletonGeneratedTypeII45 ≠ kernelProved := by decide

/-- This layer does not close Erdős #287. -/
theorem erdos287_not_closed : strictCellLedger erdos287 ≠ kernelProved := by decide

end StrictCellSingletonStatus
end Erdos287
