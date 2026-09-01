import Mathlib
import RequestProject.Status.CurrentStatusErdos287StrictCellCanonicalSingleton
import RequestProject.CurrentProgramme.Erdos287StrictCellSemanticRepair
import RequestProject.CurrentProgramme.Erdos287RepeatedPrimePhysicalSource
import RequestProject.CurrentProgramme.Erdos287WeightedSP2PhysicalSource
import RequestProject.CurrentProgramme.Erdos287PhysicalBComparisonV2
import RequestProject.CurrentProgramme.Erdos287CenteredQCellPhysical
import RequestProject.CurrentProgramme.Erdos287Supersqrt3221Dictionary
import RequestProject.CurrentProgramme.Erdos287SupersqrtAnalyticInterface
import RequestProject.CurrentProgramme.Erdos287PhysicalBridgeV2

/-!
# Authoritative status layer — Erdős #287, semantic repair + super-square-root frontier

This module is **append-only** and **later** than every earlier status file.  No earlier
status file is edited; where they disagree about the semantics of a banked object, this
layer controls.

```
OLD StrictCellSingleton.hStar:
    KERNEL-PROVED COMBINATORIAL SURROGATE; NOT LITERAL FORD-H BY DEFINITION
FORD-H PHYSICAL BINDING:
    UNINHABITED; the conditional value −20 is proved from it alone
OLD StrictCellHypotheses.strict_collapse:
    ABSTRACT CERTIFICATE; NOT A PHYSICAL SOURCE THEOREM
OLD bare-indicator physical bridge:
    VALID ABSTRACT SUFFICIENT INTERFACE; SUPERSEDED AS PHYSICAL DICTIONARY
WEIGHTED SP2 SLOT SOURCE:
    KERNEL-PROVED (finite algebra); source adapter UNINHABITED
REPEATED-PRIME FINITE ALGEBRA:
    KERNEL-PROVED; the old weight-zero routing is SUPERSEDED
Bsrc FINITE CORRECTION:
    KERNEL-PROVED conditional on the S₂ parameter
B COMPARISON ANALYTIC THEOREM:
    PAPER/RESEARCH CLOSED; LEAN V2 INPUT UNINHABITED
CENTERED q-CELL CHARACTER ALGEBRA:
    KERNEL-PROVED
2+5 INVERSE-SAMPLED DICTIONARY:
    KERNEL-PROVED
SUB-SQRT ANALYTIC:
    PAPER/RESEARCH PASS; LEAN INTERFACE UNINHABITED
SP2-LABELLED-SINGLETON-CENTERED-QCELL-SUPERSQRT45:
    OPEN ANALYTIC / UNINHABITED
FULL-SOURCE-LOCAL-ANALYTIC-KERNEL45, WINDOWPAIR, ERDOS287:
    OPEN
```

Every `kernelProved` row is tied to an actual theorem by a `backing_*` declaration.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace SupersqrtFrontierStatus

open Erdos287.C0UnitaryFourierStatus
open Erdos287.SemanticRepair
open Erdos287.RepeatedPrime
open Erdos287.WeightedSP2
open Erdos287.BComparisonV2
open Erdos287.CenteredQCell
open Erdos287.Supersqrt3221
open Erdos287.SupersqrtFrontier
open Erdos287.SP2Source
open Erdos287.StrictCellSingleton
open ResearchStatus

/-! ## §1  Nodes of this layer -/

/-- Nodes recorded by the semantic-repair / super-sqrt status layer. -/
inductive SupersqrtNode
  /-- The banked combinatorial `hStar` value. -/
  | combinatorialHStar
  /-- The literal Ford-`H` physical binding. -/
  | fordHPhysicalBinding
  /-- The abstract strict-collapse certificate. -/
  | abstractStrictCollapse
  /-- The old bare-indicator physical bridge, as a physical dictionary. -/
  | bareIndicatorBridge
  /-- The full weighted SP-2 slot source (finite algebra). -/
  | weightedSlotSource
  /-- The weighted source adapter (source obligation). -/
  | weightedSourceAdapter
  /-- The repeated-prime finite algebra. -/
  | repeatedPrimeFiniteAlgebra
  /-- The old repeated-prime weight-zero routing. -/
  | repeatedPrimeZeroRouting
  /-- The finite `Bsrc` correction. -/
  | bsrcFiniteCorrection
  /-- The old coefficient-one `B`-comparison normalisation. -/
  | oldBNormalisation
  /-- The V2 `B`-comparison analytic input. -/
  | bComparisonV2Input
  /-- The centered `q`-cell character algebra. -/
  | centeredQCellAlgebra
  /-- The `2 + 5` inverse-sampled `3221` dictionary. -/
  | inverseSampled3221Dictionary
  /-- The sub-square-root analytic interface. -/
  | subSqrtAnalytic
  /-- `SP2-LABELLED-SINGLETON-CENTERED-QCELL-SUPERSQRT45`. -/
  | supersqrt45
  /-- `FULL-SOURCE-LOCAL-ANALYTIC-KERNEL45`. -/
  | fullSourceLocalAnalyticKernel45
  /-- The window-pair supply. -/
  | windowPair
  /-- Erdős problem #287 itself. -/
  | erdos287
  deriving DecidableEq, Fintype, Repr

open SupersqrtNode

/-- The authoritative ledger of this layer. -/
def supersqrtLedger : SupersqrtNode → ResearchStatus
  | combinatorialHStar => kernelProved
  | fordHPhysicalBinding => conditionalSourcePin
  | abstractStrictCollapse => conditionalSourcePin
  | bareIndicatorBridge => superseded
  | weightedSlotSource => kernelProved
  | weightedSourceAdapter => open_
  | repeatedPrimeFiniteAlgebra => kernelProved
  | repeatedPrimeZeroRouting => superseded
  | bsrcFiniteCorrection => kernelProved
  | oldBNormalisation => superseded
  | bComparisonV2Input => analyticBanked
  | centeredQCellAlgebra => kernelProved
  | inverseSampled3221Dictionary => kernelProved
  | subSqrtAnalytic => analyticBanked
  | supersqrt45 => open_
  | fullSourceLocalAnalyticKernel45 => open_
  | windowPair => open_
  | erdos287 => open_

/-! ## §2  Ledger facts -/

theorem erdos287_open : supersqrtLedger erdos287 = open_ := rfl

theorem supersqrt45_open : supersqrtLedger supersqrt45 = open_ := rfl

theorem fullSourceKernel_open : supersqrtLedger fullSourceLocalAnalyticKernel45 = open_ := rfl

theorem windowPair_open : supersqrtLedger windowPair = open_ := rfl

/-- The `B`-comparison analytic theorem is *paper* research, not kernel-proved. -/
theorem bComparison_analyticBanked :
    supersqrtLedger bComparisonV2Input = analyticBanked := rfl

theorem bComparison_not_kernelProved :
    supersqrtLedger bComparisonV2Input ≠ kernelProved := by decide

/-- The sub-square-root row is a research pass, not a kernel proof. -/
theorem subSqrt_not_kernelProved : supersqrtLedger subSqrtAnalytic ≠ kernelProved := by decide

/-- Superseded rows are not retracted: the older interfaces remain valid theorems. -/
theorem superseded_rows_not_retracted :
    supersqrtLedger bareIndicatorBridge ≠ retracted ∧
      supersqrtLedger repeatedPrimeZeroRouting ≠ retracted ∧
      supersqrtLedger oldBNormalisation ≠ retracted := by decide

/-- No analytic node of this layer is recorded as kernel-proved. -/
theorem analytic_nodes_not_kernelProved :
    supersqrtLedger bComparisonV2Input ≠ kernelProved ∧
      supersqrtLedger subSqrtAnalytic ≠ kernelProved ∧
      supersqrtLedger supersqrt45 ≠ kernelProved ∧
      supersqrtLedger fullSourceLocalAnalyticKernel45 ≠ kernelProved ∧
      supersqrtLedger erdos287 ≠ kernelProved := by decide

/-! ## §3  Backing theorems for the `kernelProved` rows -/

/-- Backing: `hStar` is by definition a combinatorial surrogate, and equals `−20`. -/
theorem backing_hStar_surrogate (U : Finset (Fin 7)) :
    hStar U = -((depthSubsets U).card : ℤ) ∧ hStar U = -20 ∧
      hStarSemantics ≠ ObjectSemantics.physicalSource :=
  ⟨combinatorial_hStar_is_surrogate U, hStar_eq_neg_twenty U, hStar_not_physicalSource⟩

/-- Backing: the surrogate does not construct the physical Ford-`H` binding. -/
theorem backing_hStar_firewall :
    (∀ U : Finset (Fin 7), hStar U = -20) ∧
      ∃ (Pset : Finset ℕ) (Hphys : ℕ → ℤ) (gammaStar : ℝ) (cut : ℕ → ℕ),
        (∀ n, Hphys n = -20) ∧ ¬ FordHPhysicalBinding Pset Hphys gammaStar cut :=
  combinatorial_hStar_does_not_construct_FordHPhysicalBinding

/-- Backing: conditionally on the physical binding — and on nothing else — the literal Ford
functional of the seven physical primes is `−20`. -/
theorem backing_fordH_conditional {Pset : Finset ℕ} {Hphys : ℕ → ℤ} {gammaStar : ℝ}
    {cut : ℕ → ℕ} (h : FordHPhysicalBinding Pset Hphys gammaStar cut) :
    Hphys (∏ p ∈ Pset, p) = -20 :=
  fordH_physical_eq_neg_twenty h

/-- Backing: the physical collapse binding gives the abstract certificate, but not
conversely. -/
theorem backing_collapse_split :
    (∀ (C : SP2FixedCertificateData) (srcK : ℕ) (srcJ : Finset ℕ),
        PhysicalCollapseBinding C srcK srcJ → C.k + C.J.card = 0) ∧
      ∃ (C : SP2FixedCertificateData) (U : Finset (Fin 7)) (srcK : ℕ) (srcJ : Finset ℕ),
        StrictCellHypotheses C U ∧ ¬ PhysicalCollapseBinding C srcK srcJ :=
  ⟨fun _ _ _ h => strict_collapse_of_physicalCollapse h,
    abstract_collapse_does_not_give_physicalCollapse⟩

/-- Backing: the weighted slot source is bounded, has the exact support identity under the
source profile condition, and is **not** the bare indicator. -/
theorem backing_weighted_slot_source :
    (∀ (C : SP2FixedCertificateData) (S : PhysicalSlotData) (i : Fin 7) (p : ℕ),
        ‖omegaPhysical C S i p‖ ≤ 1) ∧
      ∃ (C : SP2FixedCertificateData) (S : PhysicalSlotData) (i : Fin 7) (p : ℕ),
        p ∈ C.lam i ∧ omegaPhysical C S i p ≠ Erdos287.SP2PrimeBox.sp2Omega C i p :=
  ⟨norm_omegaPhysical_le_one, weighted_omega_ne_bare_indicator⟩

/-- Backing: the exact weighted integer pushforward. -/
theorem backing_omegaSharpPhysical (C : SP2FixedCertificateData) (S : PhysicalSlotData)
    (F : ℕ → ℂ) :
    ∑ v ∈ cellVectors C, (∏ i, omegaPhysical C S i (v i)) * F (pushforward v)
      = ∑ n ∈ (cellVectors C).image pushforward, OmegaSharpPhysical C S n * F n :=
  omegaSharpPhysical_pushforward C S F

/-- Backing: the repeated-prime finite algebra, exactly. -/
theorem backing_repeated_prime :
    (∀ r : ℕ, 1 ≤ r → Hrepeat r = -(((r - 1).choose 3 : ℕ) : ℤ)) ∧
      Hrepeat 7 = -20 ∧ Hrepeat 6 = -10 ∧ Hrepeat 5 = -4 ∧ Hrepeat 4 = -1 :=
  ⟨fun _ hr => Hrepeat_eq_neg_choose hr, Hrepeat_seven, Hrepeat_six, Hrepeat_five,
    Hrepeat_four⟩

/-- Backing: the old weight-zero routing is a different source. -/
theorem backing_repeated_prime_routing_superseded :
    (∑ v ∈ cellVectors countermodelCert, unitWeight v) = 128 ∧
      (∑ v ∈ cellVectors countermodelCert, zeroRepeatedRouting unitWeight v) = 0 :=
  repeatedPrimeZero_changes_total_mass

/-- Backing: the finite `Bsrc` bounds. -/
theorem backing_Bsrc {S2 : ℝ} (hS2 : 0 < S2) (hS2' : S2 < 1) {P : ℕ}
    (hP : P.primeFactors.card ≤ 7) : 0 < Bsrc S2 P ∧ Bsrc S2 P < 128 :=
  ⟨Bsrc_pos hS2 P, Bsrc_lt_128 hS2' hP⟩

/-- Backing: the normalisation firewall — old ⇒ V2, but not conversely. -/
theorem backing_normalisation_firewall :
    (∀ (E : ℝ → ℝ) (A : ℝ), OldErrShape E A → V2ErrShape E A 1 2) ∧
      ∃ (E : ℝ → ℝ) (A Cerr z0 : ℝ), V2ErrShape E A Cerr z0 ∧ ¬ OldErrShape E A :=
  ⟨fun _ _ h => v2_shape_of_old_shape h, v2_shape_does_not_imply_old_shape⟩

/-- Backing: the centered `q`-cell character algebra. -/
theorem backing_centered_qCell {q : ℕ} [NeZero q] (hq : ¬ 2 ∣ q)
    (s : Erdos287.Vaughan.AffineSign) {n : ZMod q} (hn : IsUnit n) (hphi : 0 < q.totient) :
    (if n = Erdos287.V23QCell.aCoeff s q then (1 : ℂ) else 0) - ((q.totient : ℂ))⁻¹
      = ((q.totient : ℂ))⁻¹ *
          ∑ chi ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)),
            (starRingEnd ℂ) (chi (Erdos287.V23QCell.aCoeff s q)) * chi n :=
  centeredQCell_character_expansion hq s hn hphi

/-- Backing: the seven-slot character product, repeats included. -/
theorem backing_sevenSlot_product (C : SP2FixedCertificateData) (S : PhysicalSlotData)
    (q : ℕ) (chi : DirichletCharacter ℂ q) :
    ∑ v ∈ cellVectors C,
        (∏ j, omegaPhysical C S j (v j)) * chi ((pushforward v : ℕ) : ZMod q)
      = ∏ j, slotTransform C S q chi j :=
  sevenSlot_character_product C S q chi

/-- Backing: the literal `2 + 5` split and the inverse-sampled dictionary. -/
theorem backing_two_plus_five (v : Fin 7 → ℕ) :
    outerPart v * innerPart v = pushforward v :=
  outer_mul_inner_eq_pushforward v

/-- Backing: the inverse-sampled `3221` physical dictionary. -/
theorem backing_inverseSampled (D : Erdos287.HighCond3221.InverseSampledHighCond3221Data)
    {q m : ℕ} (hq : q ∈ D.Qbox) (hm : m ∈ D.Mbox) (w : ℤ) :
    ((q : ℤ) ∣ 2 * (m : ℤ) * w + D.sign) ↔ ((w : ZMod q) = D.samplePoint q m) :=
  supersqrt_inverseSampled_dictionary D hq hm w

/-- Backing: the exact centered source identity. -/
theorem backing_centered_source_identity {s : Erdos287.Vaughan.AffineSign} {Q : Finset ℕ}
    {P : ℤ} {N : ℕ} (hN0 : N ≠ 0) (hN : (N : ℤ) = 2 * P + s.val)
    (hsub : N.divisors ⊆ Q) :
    ArithmeticFunction.vonMangoldt N - principalSum Q N = centeredSum s Q P N :=
  centered_source_identity hN0 hN hsub

/-! ## §4  Scope guards -/

/-- The super-sqrt analytic input is refuted at explicit data and is not constructed. -/
theorem guard_supersqrt_uninhabited :
    ∃ (D : SP2LabelledSingletonCenteredQCellSupersqrtData) (bound : ℝ),
      ¬ SP2LabelledSingletonCenteredQCellSupersqrtInput D bound :=
  supersqrt_input_not_automatic

/-- The sub-square-root large-sieve interface is not constructed either. -/
theorem guard_subSqrt_uninhabited :
    ∃ (Qbox : Finset ℕ) (coeff : ℕ → ℂ) (X L Csrc Cbound : ℝ),
      ¬ SP2SubSqrtCharacterLargeSieveInput Qbox coeff X L Csrc Cbound :=
  subSqrt_input_not_automatic

/-- The current super-sqrt route is sign-blind: no linear `μ(q)` cancellation downstream. -/
theorem guard_sign_blind : supersqrtRoutePolicy ≠ SignPolicy.signAware :=
  supersqrt_route_not_sign_aware

/-- No claim about Erdős #287 is made anywhere in this layer. -/
theorem guard_erdos287_still_open : supersqrtLedger erdos287 = open_ := rfl

/-! ## §5  Addendum — the corrected physical bridge `V2`

`OLD bare-indicator physical bridge : SUPERSEDED AS PHYSICAL DICTIONARY` is realised by the
corrected interface `BalancedSevenSP2PhysicalBridgeV2`, which is **uninhabited**. -/

/-- Backing: the corrected bridge is a genuine source obligation, and the old slot field is
not the corrected one. -/
theorem backing_bridgeV2_uninhabited :
    (∃ (C : SP2FixedCertificateData) (U : Finset (Fin 7))
        (S : Erdos287.WeightedSP2.PhysicalSlotData) (Dat : Erdos287.V21PrimeBox.PrimeBoxData)
        (w : (Fin 7 → ℕ) → ℤ) (Pset : Finset ℕ) (Hphys : ℕ → ℤ) (gammaStar : ℝ)
        (cut : ℕ → ℕ) (S2 : ℝ),
        ¬ Erdos287.PhysicalBridgeV2.BalancedSevenSP2PhysicalBridgeV2 C U S Dat w Pset Hphys
            gammaStar cut S2) ∧
      ∃ (C : SP2FixedCertificateData) (S : Erdos287.WeightedSP2.PhysicalSlotData)
        (Dat : Erdos287.V21PrimeBox.PrimeBoxData),
        (∀ (i : Fin 7) (p : ℕ), Dat.omega i p = Erdos287.SP2PrimeBox.sp2Omega C i p) ∧
          ¬ (∀ (i : Fin 7) (p : ℕ), Dat.omega i p = omegaPhysical C S i p) :=
  ⟨Erdos287.PhysicalBridgeV2.bridgeV2_not_automatic,
    Erdos287.PhysicalBridgeV2.oldBridge_slotWeight_is_not_v2_slotWeight⟩

/-! ## §6  Addendum — `V20` / `V21` route status

```
V20 HHH Gram object              : VALID HISTORICAL FINITE/ANALYTIC SOCKET
V20 HHH inclusion-exclusion
      closure argument           : RETRACTED AS A CLOSURE PROOF
V21 two-high-projector route     : CONTROLLING REPAIRED ROUTE
```

The authoritative status is **not** reverted to `V20`. -/

/-- The three route rows of this layer. -/
inductive RouteNode
  /-- The `V20` `HHH` Gram object. -/
  | v20GramObject
  /-- The `V20` `HHH` inclusion-exclusion closure argument. -/
  | v20ClosureArgument
  /-- The `V21` two-high-projector route. -/
  | v21TwoHighProjector
  deriving DecidableEq, Fintype, Repr

open RouteNode

/-- The route ledger. -/
def routeLedger : RouteNode → ResearchStatus
  | v20GramObject => analyticBanked
  | v20ClosureArgument => retracted
  | v21TwoHighProjector => conditionalSourcePin

/-- The `V20` Gram object survives as a valid historical socket. -/
theorem v20_gram_object_valid : routeLedger v20GramObject = analyticBanked := rfl

/-- The `V20` closure argument is retracted as a closure proof. -/
theorem v20_closure_retracted : routeLedger v20ClosureArgument = retracted := rfl

/-- The `V21` two-high-projector route is the controlling repaired route; it is not
retracted and not kernel-closed. -/
theorem v21_is_controlling :
    routeLedger v21TwoHighProjector ≠ retracted ∧
      routeLedger v21TwoHighProjector ≠ kernelProved := by decide

/-- The authoritative route is not reverted to `V20`. -/
theorem authoritative_route_is_not_v20 :
    routeLedger v20ClosureArgument ≠ routeLedger v21TwoHighProjector := by decide

end SupersqrtFrontierStatus
end Erdos287
