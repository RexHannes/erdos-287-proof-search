import Mathlib
import RequestProject.Status.CurrentStatusErdos287CaseBFrontier
import RequestProject.CurrentProgramme.Erdos287Hybrid2Arithmetic
import RequestProject.CurrentProgramme.Erdos287Hybrid2AnalyticCompiler
import RequestProject.CurrentProgramme.Erdos287Hybrid2CriticalRectangle
import RequestProject.CurrentProgramme.Erdos287Hybrid2ShortEdgeFirewall
import RequestProject.CurrentProgramme.Erdos287BDiagonalProductMod

/-!
# Append-only status layer — HYBRID-2 / critical-rectangle frontier ledger

This module is **append-only**.  The CASE-B frontier ledger
(`CurrentStatusErdos287CaseBFrontier`) and everything it imports are re-checked, not edited;
`caseB_ledger_still_preserved` records that the earlier rows are unchanged.

The ledger below distinguishes three kinds of row.

* `provedUnconditional` — a literal kernel-checked theorem with no analytic hypothesis and no
  source pin.  Only the Hybrid-2 arithmetic bank qualifies.
* `sourcePin` — the **formal source first residual**: the Ω_H normalisation.  It is *not*
  a theorem of this repository and is not promoted here.
* `conditionalOpen` — a node whose *structural reduction* has been formalised (with explicit
  analytic hypotheses) but which is **not closed**.  All Hybrid-2 short edges, the long-edge
  two-sided rectangle and the b-diagonal Δ product-modulus rectangle are of this kind.

`hybrid2_longEdge_pass_does_not_capture_survivors` is the firewall: `LongEdgeRectangle PASS`
does **not** imply that all Hybrid-2 survivors lie in the rectangle, because the short-edge
nodes are open.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace Hybrid2FrontierStatus

/-! ## §1  The ledger -/

/-- Nodes of the Hybrid-2 / critical-rectangle ledger. -/
inductive Hybrid2Node
  | sharedGcdOmegaHNormalizationSourcePin
  | caseBPrimitiveFractionCritical
  | hybrid2MobiusOpening
  | hybrid2ReciprocalCancellation
  | hybrid2ConductorAlgebra
  | hybrid2G0G0PrimeDivisibility
  | hybrid2ShortD
  | hybrid2ShortM
  | hybrid2ShortQ
  | hybrid2LongEdgeTwoSidedRectangle
  | bDiagonalDeltaProductModRectangle
  | erdos287
  deriving DecidableEq, Fintype, Repr

/-- Status labels. -/
inductive Hybrid2Label
  /-- A literal kernel-checked theorem, no analytic hypothesis, no source pin. -/
  | provedUnconditional
  /-- Not a theorem of this repository; carried as source data. -/
  | sourcePin
  /-- Structural reduction formalised with explicit analytic hypotheses; **not closed**. -/
  | conditionalOpen
  /-- A strictly later reduction exists; this is not the live residual (and not closed). -/
  | passedThrough
  /-- Open. -/
  | open_
  deriving DecidableEq, Fintype, Repr

open Hybrid2Node Hybrid2Label

/-- Linear position along the reduction chain. -/
def stage : Hybrid2Node → ℕ
  | sharedGcdOmegaHNormalizationSourcePin => 0
  | caseBPrimitiveFractionCritical => 1
  | hybrid2MobiusOpening => 2
  | hybrid2ReciprocalCancellation => 3
  | hybrid2ConductorAlgebra => 4
  | hybrid2G0G0PrimeDivisibility => 5
  | hybrid2ShortD => 6
  | hybrid2ShortM => 7
  | hybrid2ShortQ => 8
  | hybrid2LongEdgeTwoSidedRectangle => 9
  | bDiagonalDeltaProductModRectangle => 10
  | erdos287 => 11

/-- The Hybrid-2 ledger. -/
def hybrid2Ledger : Hybrid2Node → Hybrid2Label
  | sharedGcdOmegaHNormalizationSourcePin => sourcePin
  | caseBPrimitiveFractionCritical => passedThrough
  | hybrid2MobiusOpening => provedUnconditional
  | hybrid2ReciprocalCancellation => provedUnconditional
  | hybrid2ConductorAlgebra => provedUnconditional
  | hybrid2G0G0PrimeDivisibility => provedUnconditional
  | hybrid2ShortD => conditionalOpen
  | hybrid2ShortM => conditionalOpen
  | hybrid2ShortQ => conditionalOpen
  | hybrid2LongEdgeTwoSidedRectangle => conditionalOpen
  | bDiagonalDeltaProductModRectangle => conditionalOpen
  | erdos287 => open_

/-! ## §2  Ledger theorems -/

/-- **`caseB_strictly_before_hybrid2_frontier`.**  `LEAN_PROVED`.

The CASE-B primitive-fraction critical node is a strict ancestor of every Hybrid-2 analytic
descendant. -/
theorem caseB_strictly_before_hybrid2_frontier :
    stage caseBPrimitiveFractionCritical < stage hybrid2ShortD ∧
    stage caseBPrimitiveFractionCritical < stage hybrid2ShortM ∧
    stage caseBPrimitiveFractionCritical < stage hybrid2ShortQ ∧
    stage caseBPrimitiveFractionCritical < stage hybrid2LongEdgeTwoSidedRectangle ∧
    stage caseBPrimitiveFractionCritical < stage bDiagonalDeltaProductModRectangle := by
  decide +kernel

/-- **`primitiveFractionCritical_not_frontier`.**  `LEAN_PROVED`.

The primitive-fraction critical node is `passedThrough`: it is neither the source pin nor a
live conditional node, and in particular it is **not closed**. -/
theorem primitiveFractionCritical_not_frontier :
    hybrid2Ledger caseBPrimitiveFractionCritical = passedThrough ∧
    hybrid2Ledger caseBPrimitiveFractionCritical ≠ provedUnconditional := by
  decide +kernel

/-- **`omegaNormalization_is_formal_first_residual`.**  `LEAN_PROVED`.

The Ω_H normalisation is the unique `sourcePin` row and sits strictly before every other node
of the chain: it is the *formal source first residual*. -/
theorem omegaNormalization_is_formal_first_residual :
    (∀ n : Hybrid2Node, hybrid2Ledger n = sourcePin ↔
        n = sharedGcdOmegaHNormalizationSourcePin) ∧
    (∀ n : Hybrid2Node, n ≠ sharedGcdOmegaHNormalizationSourcePin →
        stage sharedGcdOmegaHNormalizationSourcePin < stage n) := by
  decide +kernel

/-- **No analytic descendant is closed.**  `LEAN_PROVED`.

The three short edges, the long-edge two-sided rectangle and the b-diagonal Δ product-modulus
rectangle are all `conditionalOpen`.  Formalising their structural reduction did **not** close
them. -/
theorem hybrid2_analytic_descendants_all_open :
    hybrid2Ledger hybrid2ShortD = conditionalOpen ∧
    hybrid2Ledger hybrid2ShortM = conditionalOpen ∧
    hybrid2Ledger hybrid2ShortQ = conditionalOpen ∧
    hybrid2Ledger hybrid2LongEdgeTwoSidedRectangle = conditionalOpen ∧
    hybrid2Ledger bDiagonalDeltaProductModRectangle = conditionalOpen := by
  decide +kernel

/-- **`hybrid2_longEdge_passedThrough_only_if_appropriate`.**  `LEAN_PROVED`.

The long-edge rectangle node may only be advanced past if **all three** short-edge nodes are
closed.  In the current ledger none of them is, so the rectangle node remains
`conditionalOpen`. -/
theorem hybrid2_longEdge_passedThrough_only_if_appropriate :
    (hybrid2Ledger hybrid2ShortD = conditionalOpen ∨
      hybrid2Ledger hybrid2ShortM = conditionalOpen ∨
      hybrid2Ledger hybrid2ShortQ = conditionalOpen) →
    hybrid2Ledger hybrid2LongEdgeTwoSidedRectangle ≠ provedUnconditional := by
  decide +kernel

/-- **`erdos287_open`.**  `LEAN_PROVED`. -/
theorem erdos287_open : hybrid2Ledger erdos287 = open_ := by decide +kernel

/-- **Nothing in this delta is marked closed by fiat.**  `LEAN_PROVED`.
Only the four unconditional arithmetic rows carry `provedUnconditional`. -/
theorem only_arithmetic_rows_are_unconditional :
    ∀ n : Hybrid2Node, hybrid2Ledger n = provedUnconditional ↔
      (n = hybrid2MobiusOpening ∨ n = hybrid2ReciprocalCancellation ∨
        n = hybrid2ConductorAlgebra ∨ n = hybrid2G0G0PrimeDivisibility) := by
  decide +kernel

/-! ## §3  The mathematical firewall behind the `conditionalOpen` labels -/

/-- **`hybrid2_survivor_union`.**  `LEAN_PROVED` (bookkeeping over a real theorem).

The Hybrid-2 survivor set is contained in the union of the three explicit short-edge predicates
and the long-edge rectangle predicate. -/
theorem hybrid2_survivor_union {C L D M Q : ℝ} (hD : 0 < D) (hM : 0 < M) (hQ : 0 < Q)
    (h : Erdos287.Hybrid2.Hybrid2Survivor C L D M Q) :
    Erdos287.Hybrid2.ShortD C L D ∨ Erdos287.Hybrid2.ShortM C L M ∨
      Erdos287.Hybrid2.ShortQ C L Q ∨ Erdos287.Hybrid2.LongEdgeRectangle C L D M Q :=
  Erdos287.Hybrid2.hybrid2_survivor_union hD hM hQ h

/-- **`hybrid2_longEdge_pass_does_not_capture_survivors`.**  `LEAN_PROVED`.

The strict firewall demanded by the audit: there is a Hybrid-2 survivor **outside** the long-edge
rectangle.  Hence `LongEdgeRectangle PASS` does not imply that all survivors lie in the
rectangle, and the short-edge nodes cannot be labelled closed as a by-product. -/
theorem hybrid2_longEdge_pass_does_not_capture_survivors :
    ∃ C L D M Q : ℝ, 0 < D ∧ 0 < M ∧ 0 < Q ∧
      Erdos287.Hybrid2.Hybrid2Survivor C L D M Q ∧
      ¬ Erdos287.Hybrid2.LongEdgeRectangle C L D M Q :=
  Erdos287.Hybrid2.rectangle_alone_does_not_capture_all_survivors

/-! ## §4  Earlier ledgers preserved -/

/-- **`caseB_ledger_still_preserved`.**  `LEAN_PROVED`.

The CASE-B frontier ledger is unchanged: no row was edited, weakened or promoted. -/
theorem caseB_ledger_still_preserved :
    Erdos287.CaseBFrontierStatus.frontierLedger
        Erdos287.CaseBFrontierStatus.FrontierNode.primitiveFractionCritical45
      = Erdos287.CaseBFrontierStatus.FrontierLabel.passedThrough ∧
    Erdos287.CaseBFrontierStatus.frontierLedger
        Erdos287.CaseBFrontierStatus.FrontierNode.fusedAffineDefectCritical45
      = Erdos287.CaseBFrontierStatus.FrontierLabel.currentFrontier ∧
    Erdos287.CaseBFrontierStatus.frontierLedger
        Erdos287.CaseBFrontierStatus.FrontierNode.erdos287
      = Erdos287.CaseBFrontierStatus.FrontierLabel.open_ ∧
    (∀ n : Erdos287.CaseBFrontierStatus.FrontierNode,
      Erdos287.CaseBFrontierStatus.frontierLedger n
        ≠ Erdos287.CaseBFrontierStatus.FrontierLabel.closed) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  exact Erdos287.CaseBFrontierStatus.frontier_no_closed_rows

/-- **The primitive-fraction ledger is preserved too.**  `LEAN_PROVED`. -/
theorem primitiveFraction_ledger_still_preserved :
    Erdos287.PrimitiveFractionCaseBStatus.ledger
        Erdos287.PrimitiveFractionCaseBStatus.Node.erdos287
      = Erdos287.PrimitiveFractionCaseBStatus.Label.open_ :=
  Erdos287.CaseBFrontierStatus.caseB_ledger_preserved.2

end Hybrid2FrontierStatus
end Erdos287
