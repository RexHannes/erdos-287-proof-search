import Mathlib
import RequestProject.Status.CurrentStatusErdos287CommonXFrontier
import RequestProject.CurrentProgramme.Erdos287A0C0SourceLift
import RequestProject.CurrentProgramme.Erdos287ReducedProjectivePair
import RequestProject.CurrentProgramme.Erdos287BPrimeH0Energy
import RequestProject.CurrentProgramme.Erdos287ConditionedInverseConvInterface

/-!
# Append-only status layer — Erdős #287, C0 source-lift bank

This module is **append-only**.  The COMMON-x ledger (`CurrentStatusErdos287CommonXFrontier`)
and everything it imports are re-checked, not edited; `commonX_ledger_still_preserved` records
that its rows are unchanged.

Freeze recorded by this layer.

```
BANKED (this delta):
  A0C0-PRIMITIVE-SOURCEFORM45
  A0C0-SOURCELIFT45
  A0C0-BPRIME-ABSORPTION45
  BPRIME-H0-GLOBALENERGY45
  PROJECTIVE-RAW-TO-REDUCED45

OPEN ANALYTIC OWNER:
  EXACTPRODUCT-CONDITIONED-INVERSECONV-LEVELLS45

OPEN FORMAL SOURCE PIN:
  SHAREDGCD-OMEGAH-NORMALISATION-SOURCEPIN45

GLOBAL:
  EXACT PRODUCT COLLISION : PARTIAL
  DOUBLE TYPE II          : PARTIAL
  C0                      : PARTIAL
  ERDOS287                : OPEN
```

“Banked” here means: an unconditional, kernel-checked arithmetic theorem of this repository.
It does **not** mean that any analytic branch is closed.  The three global branch rows and the
Erdős #287 row are deliberately not `bankedUnconditional`, and the theorems below prove that
they are not.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace C0SourceLiftStatus

/-! ## §1  Nodes and labels -/

/-- Nodes of the C0 source-lift ledger. -/
inductive SourceLiftNode
  /-- Literal `Γ₁, Γ₂, A0row, C0` expansions. -/
  | a0c0PrimitiveSourceForm45
  /-- Pre-completion row representative modulo `x`. -/
  | a0c0SourceLift45
  /-- `b'`-absorption into the reduced numerator slot list. -/
  | a0c0BPrimeAbsorption45
  /-- Finite product-fibre `L²` energy lemma. -/
  | bprimeH0GlobalEnergy45
  /-- Raw → reduced projective pair and the collision equivalence. -/
  | projectiveRawToReduced45
  /-- Fixed factorisation depth `(8, 8)`; arithmetic record only. -/
  | fixedFactorisationDepth88
  /-- The conditioned inverse-convolution estimate at moving levels.  Open. -/
  | exactProductConditionedInverseConvLevelLS45
  /-- The `Ω_H` normalisation source pin.  Open. -/
  | sharedGcdOmegaHNormalisationSourcePin45
  /-- Divisor-moment bound `d₁' ≤ L^K`: not formalised as an arithmetic fact. -/
  | depthBoundD1PrimeLePowL
  /-- The exact-product collision branch. -/
  | exactProductCollisionBranch
  /-- The double Type-II branch. -/
  | doubleTypeIIBranch
  /-- The C0 branch. -/
  | c0Branch
  /-- Erdős problem #287 itself. -/
  | erdos287
  deriving DecidableEq, Fintype, Repr

/-- Status labels for this layer. -/
inductive SourceLiftLabel
  /-- A literal kernel-checked theorem of this repository, no analytic hypothesis. -/
  | bankedUnconditional
  /-- Stated only as an explicit named hypothesis; open. -/
  | openAnalyticHypothesis
  /-- Open formal source pin; never assumed. -/
  | openSourcePin
  /-- Absent from this repository: neither proved nor assumed. -/
  | notFormalised
  /-- Reduction has advanced; the branch is partial and open. -/
  | partialOpen
  /-- Open. -/
  | open_
  deriving DecidableEq, Fintype, Repr

open SourceLiftNode SourceLiftLabel

/-- The C0 source-lift ledger. -/
def sourceLiftLedger : SourceLiftNode → SourceLiftLabel
  | a0c0PrimitiveSourceForm45 => bankedUnconditional
  | a0c0SourceLift45 => bankedUnconditional
  | a0c0BPrimeAbsorption45 => bankedUnconditional
  | bprimeH0GlobalEnergy45 => bankedUnconditional
  | projectiveRawToReduced45 => bankedUnconditional
  | fixedFactorisationDepth88 => bankedUnconditional
  | exactProductConditionedInverseConvLevelLS45 => openAnalyticHypothesis
  | sharedGcdOmegaHNormalisationSourcePin45 => openSourcePin
  | depthBoundD1PrimeLePowL => notFormalised
  | exactProductCollisionBranch => partialOpen
  | doubleTypeIIBranch => partialOpen
  | c0Branch => partialOpen
  | erdos287 => open_

/-! ## §2  Ledger facts -/

/-- **`banked_children_are_unconditional`.**  `LEAN_PROVED`.  Exactly the five banked children
of this delta (plus the arithmetic depth record) carry `bankedUnconditional`. -/
theorem banked_children_are_unconditional :
    sourceLiftLedger a0c0PrimitiveSourceForm45 = bankedUnconditional ∧
    sourceLiftLedger a0c0SourceLift45 = bankedUnconditional ∧
    sourceLiftLedger a0c0BPrimeAbsorption45 = bankedUnconditional ∧
    sourceLiftLedger bprimeH0GlobalEnergy45 = bankedUnconditional ∧
    sourceLiftLedger projectiveRawToReduced45 = bankedUnconditional ∧
    sourceLiftLedger fixedFactorisationDepth88 = bankedUnconditional := by
  decide +kernel

/-- **`open_owners`.**  `LEAN_PROVED`.  The next analytic owner and the first formal owner are
open, and neither is banked. -/
theorem open_owners :
    sourceLiftLedger exactProductConditionedInverseConvLevelLS45 = openAnalyticHypothesis ∧
    sourceLiftLedger sharedGcdOmegaHNormalisationSourcePin45 = openSourcePin ∧
    sourceLiftLedger exactProductConditionedInverseConvLevelLS45 ≠ bankedUnconditional ∧
    sourceLiftLedger sharedGcdOmegaHNormalisationSourcePin45 ≠ bankedUnconditional := by
  decide +kernel

/-- **`global_rows_not_closed`.**  `LEAN_PROVED`.  Exact product collision, double Type II and
C0 are partial; Erdős #287 is open.  None of them is banked. -/
theorem global_rows_not_closed :
    sourceLiftLedger exactProductCollisionBranch = partialOpen ∧
    sourceLiftLedger doubleTypeIIBranch = partialOpen ∧
    sourceLiftLedger c0Branch = partialOpen ∧
    sourceLiftLedger erdos287 = open_ ∧
    sourceLiftLedger c0Branch ≠ bankedUnconditional ∧
    sourceLiftLedger erdos287 ≠ bankedUnconditional := by
  decide +kernel

/-- **`no_analytic_row_is_banked`.**  `LEAN_PROVED`.  No node carrying an analytic hypothesis,
a source pin or a non-formalised estimate is labelled `bankedUnconditional`. -/
theorem no_analytic_row_is_banked :
    ∀ n : SourceLiftNode,
      sourceLiftLedger n = bankedUnconditional →
        n = a0c0PrimitiveSourceForm45 ∨ n = a0c0SourceLift45 ∨ n = a0c0BPrimeAbsorption45 ∨
        n = bprimeH0GlobalEnergy45 ∨ n = projectiveRawToReduced45 ∨
        n = fixedFactorisationDepth88 := by
  decide +kernel

/-- **`depth_bound_not_formalised`.**  `LEAN_PROVED`.  `d₁' ≤ L^K` is recorded as *not*
formalised: it appears only as an explicit hypothesis of a transfer lemma. -/
theorem depth_bound_not_formalised :
    sourceLiftLedger depthBoundD1PrimeLePowL = notFormalised := by decide +kernel

/-- **`sourcelift_pass_does_not_imply_c0_closure`.**  `LEAN_PROVED`.  The banked arithmetic of
this delta does not promote the C0 branch. -/
theorem sourcelift_pass_does_not_imply_c0_closure :
    sourceLiftLedger projectiveRawToReduced45 = bankedUnconditional ∧
    sourceLiftLedger c0Branch = partialOpen ∧
    sourceLiftLedger c0Branch ≠ bankedUnconditional := by
  decide +kernel

/-! ## §3  Preservation of earlier ledgers -/

open Erdos287.CommonXFrontierStatus in
/-- **`commonX_ledger_still_preserved`.**  `LEAN_PROVED`.  The earlier COMMON-x rows are
unchanged by this append-only delta. -/
theorem commonX_ledger_still_preserved :
    commonXLedger CommonXNode.c0Branch = CommonXLabel.researchStrictlyReducedOpen ∧
    commonXLedger CommonXNode.erdos287 = CommonXLabel.open_ ∧
    commonXLedger CommonXNode.sharedGcdOmegaHNormalizationSourcePin = CommonXLabel.sourcePin := by
  decide +kernel

/-! ## §4  The banked theorems this ledger refers to

The rows above are backed by the following literal theorems; the `#print axioms` audit is in
`RequestProject/Status/AxiomAuditErdos287C0SourceLift.lean`.

* `a0c0PrimitiveSourceForm45` — `Erdos287.SourceLift.SourceRow.erdos287_gamma1_primitive`,
  `erdos287_gamma2_primitive`, `erdos287_A0row_primitive`, `erdos287_C0_primitive`.
* `a0c0SourceLift45` — `Erdos287.SourceLift.erdos287_Q2_dvd`,
  `Erdos287.SourceLift.erdos287_A0pre_congr_A0row`.
* `a0c0BPrimeAbsorption45` — `Erdos287.ReducedProjective.erdos287_Pnat_slot_product`,
  `erdos287_Rnat_slot_product`.
* `bprimeH0GlobalEnergy45` — `Erdos287.BPrimeEnergy.product_fibre_l2_bound_of_fibre_card`,
  `product_fibre_l2_bound_of_second_cardinality`, `bprime_h0_global_energy`,
  `bprime_h0_global_energy_congruence_filter`.
* `projectiveRawToReduced45` — `Erdos287.ReducedProjective.erdos287_Praw_factor`,
  `erdos287_Rraw_factor`, `erdos287_raw_projective_collision_iff_reduced`,
  `projective_collision_invariant_under_row_scaling`.
* `fixedFactorisationDepth88` — `Erdos287.ReducedProjective.erdos287_numerator_depth`,
  `erdos287_denominator_depth`, `erdos287_fixed_depth_exponent`.

The two open owners are represented only by the hypothesis shells
`Erdos287.ConditionedInverseConv.ConditionedInverseConvHypothesis` and
`Erdos287.ConditionedInverseConv.OmegaHNormalizationHypothesis`, both of which are proved to be
non-automatic. -/

end C0SourceLiftStatus
end Erdos287
