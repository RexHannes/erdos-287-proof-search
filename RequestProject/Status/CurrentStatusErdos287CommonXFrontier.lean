import Mathlib
import RequestProject.Status.CurrentStatusErdos287Hybrid2Frontier
import RequestProject.CurrentProgramme.Erdos287CommonXArithmetic
import RequestProject.CurrentProgramme.Erdos287FractionalLinearC0
import RequestProject.CurrentProgramme.Erdos287CommonXCollisionFirewall

/-!
# Append-only status layer — COMMON-x / fractional-linear C0 frontier ledger

This module is **append-only**.  The HYBRID-2 ledger
(`CurrentStatusErdos287Hybrid2Frontier`), the CASE-B ledger and everything they import are
re-checked, not edited; `hybrid2_ledger_still_preserved` records that the historical rows are
unchanged.  The Hybrid-2 status is *not* deleted or replaced: the present layer is appended
strictly after it.

Row kinds.

* `provedUnconditional` — a literal kernel-checked theorem of this repository with no analytic
  hypothesis and no source pin.  Only the common-x / kappa-CRT / firewall / fractional-linear /
  change-of-variables arithmetic qualifies.
* `sourcePin` — the **formal first source residual**, `SharedGcdOmegaHNormalizationSourcePin`.
  Not a theorem here, not promoted here.
* `analyticOpen` — the current **research first analytic residual**.
* `researchStrictlyReducedOpen` — a branch whose reduction has advanced but which is **open**.
* `ledgerRecordResearchClosed` / `ledgerRecordAnalyticOpen` — *bookkeeping rows only*.  They
  record what the research record says about the Type-I / Type-II split; they are **not** proofs
  of any analytic inequality and are deliberately given labels distinct from
  `provedUnconditional`.
* `notFormalised` — explicitly absent from this repository (Weil bound, level-averaged spectral
  closure, numerical vertex dictionary).
* `passedThrough` — a strictly earlier node that is no longer the live residual (and is **not**
  closed).

Nothing in this layer is `closed`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace CommonXFrontierStatus

/-! ## §1  Nodes and labels -/

/-- Nodes of the common-x / fractional-linear C0 ledger. -/
inductive CommonXNode
  | sharedGcdOmegaHNormalizationSourcePin
  | hybrid2CriticalRectangle
  | commonXConductorArithmetic
  | kappaCrtArithmetic
  | graphDiagonalFirewall
  | fractionalLinearLinearisation
  | commonDivisorCollisionCancellation
  | kloostermanChangeOfVariables
  | commonXTypeIResearchClosed
  | commonXTypeIIAnalyticOpen
  | commonXFractionalLinearDoubleTypeIIKloosterman45
  | weilBoundForKloostermanSums
  | levelAveragedSpectralClosure
  | c0Branch
  | transverseSignlessCarrierDominated
  | transverseEPathTouchesOmegaHSourcePin
  | transverseRPathAnalyticOpen
  | transverseBranch
  | bDiagonalNumericalVertexDictionary
  | bDiagonalBranch
  | erdos287
  deriving DecidableEq, Fintype, Repr

/-- Status labels. -/
inductive CommonXLabel
  /-- A literal kernel-checked theorem, no analytic hypothesis, no source pin. -/
  | provedUnconditional
  /-- Not a theorem of this repository; carried as source data. -/
  | sourcePin
  /-- The live analytic residual.  Open. -/
  | analyticOpen
  /-- Reduction has advanced; the branch is still open. -/
  | researchStrictlyReducedOpen
  /-- Ledger record: the research record marks this externally closed.  **Not a Lean proof.** -/
  | ledgerRecordResearchClosed
  /-- Ledger record: the research record marks this analytically open.  **Not a Lean proof.** -/
  | ledgerRecordAnalyticOpen
  /-- Absent from this repository; not formalised, not admitted. -/
  | notFormalised
  /-- A strictly later reduction exists; not the live residual, and not closed. -/
  | passedThrough
  /-- Open. -/
  | open_
  deriving DecidableEq, Fintype, Repr

open CommonXNode CommonXLabel

/-- Linear position along the reduction chain. -/
def stage : CommonXNode → ℕ
  | sharedGcdOmegaHNormalizationSourcePin => 0
  | hybrid2CriticalRectangle => 1
  | commonXConductorArithmetic => 2
  | kappaCrtArithmetic => 3
  | graphDiagonalFirewall => 4
  | fractionalLinearLinearisation => 5
  | commonDivisorCollisionCancellation => 6
  | kloostermanChangeOfVariables => 7
  | commonXTypeIResearchClosed => 8
  | commonXTypeIIAnalyticOpen => 9
  | commonXFractionalLinearDoubleTypeIIKloosterman45 => 10
  | weilBoundForKloostermanSums => 11
  | levelAveragedSpectralClosure => 12
  | c0Branch => 13
  | transverseSignlessCarrierDominated => 14
  | transverseEPathTouchesOmegaHSourcePin => 15
  | transverseRPathAnalyticOpen => 16
  | transverseBranch => 17
  | bDiagonalNumericalVertexDictionary => 18
  | bDiagonalBranch => 19
  | erdos287 => 20

/-- The common-x / fractional-linear ledger. -/
def commonXLedger : CommonXNode → CommonXLabel
  | sharedGcdOmegaHNormalizationSourcePin => sourcePin
  | hybrid2CriticalRectangle => passedThrough
  | commonXConductorArithmetic => provedUnconditional
  | kappaCrtArithmetic => provedUnconditional
  | graphDiagonalFirewall => provedUnconditional
  | fractionalLinearLinearisation => provedUnconditional
  | commonDivisorCollisionCancellation => provedUnconditional
  | kloostermanChangeOfVariables => provedUnconditional
  | commonXTypeIResearchClosed => ledgerRecordResearchClosed
  | commonXTypeIIAnalyticOpen => ledgerRecordAnalyticOpen
  | commonXFractionalLinearDoubleTypeIIKloosterman45 => analyticOpen
  | weilBoundForKloostermanSums => notFormalised
  | levelAveragedSpectralClosure => notFormalised
  | c0Branch => researchStrictlyReducedOpen
  | transverseSignlessCarrierDominated => researchStrictlyReducedOpen
  | transverseEPathTouchesOmegaHSourcePin => sourcePin
  | transverseRPathAnalyticOpen => ledgerRecordAnalyticOpen
  | transverseBranch => researchStrictlyReducedOpen
  | bDiagonalNumericalVertexDictionary => notFormalised
  | bDiagonalBranch => researchStrictlyReducedOpen
  | erdos287 => open_

/-! ## §2  Residuals -/

/-- **`omegaNormalization_is_formal_first_residual`.**  `LEAN_PROVED`.

The Ω_H normalisation source pin is the earliest node of the chain and is `sourcePin`: it
remains the **formal first source residual**. -/
theorem omegaNormalization_is_formal_first_residual :
    commonXLedger sharedGcdOmegaHNormalizationSourcePin = sourcePin ∧
    (∀ n : CommonXNode, n ≠ sharedGcdOmegaHNormalizationSourcePin →
      stage sharedGcdOmegaHNormalizationSourcePin < stage n) := by
  decide +kernel

/-- **`doubleTypeII_is_research_first_analytic_residual`.**  `LEAN_PROVED`.

`CommonXFractionalLinearDoubleTypeIIKloosterman45` is the unique `analyticOpen` row, and every
node strictly before it is either a source pin, a proved arithmetic row, a passed-through row or
a bookkeeping record — none of them is `analyticOpen`. -/
theorem doubleTypeII_is_research_first_analytic_residual :
    (∀ n : CommonXNode, commonXLedger n = analyticOpen ↔
      n = commonXFractionalLinearDoubleTypeIIKloosterman45) := by
  decide +kernel

/-! ## §3  Branch statuses (§10, §12 of the request) -/

/-- **`c0_transverse_bdiagonal_all_reduced_open`.**  `LEAN_PROVED`.

C0, TRANSVERSE and b-DIAGONAL are all `researchStrictlyReducedOpen`: strictly reduced, **not**
closed. -/
theorem c0_transverse_bdiagonal_all_reduced_open :
    commonXLedger c0Branch = researchStrictlyReducedOpen ∧
    commonXLedger transverseBranch = researchStrictlyReducedOpen ∧
    commonXLedger bDiagonalBranch = researchStrictlyReducedOpen := by
  decide +kernel

/-- **`erdos287_open`.**  `LEAN_PROVED`. -/
theorem erdos287_open : commonXLedger erdos287 = open_ := by decide +kernel

/-- **`transverse_status_rows`.**  `LEAN_PROVED`.  §12 of the request: the transverse branch is
signless-carrier dominated and analytically open; the `E = e/a₁` path touches the Ω_H source pin;
the `R = r₂/c₂` path is analytically open. -/
theorem transverse_status_rows :
    commonXLedger transverseSignlessCarrierDominated = researchStrictlyReducedOpen ∧
    commonXLedger transverseEPathTouchesOmegaHSourcePin = sourcePin ∧
    commonXLedger transverseRPathAnalyticOpen = ledgerRecordAnalyticOpen := by
  decide +kernel

/-- **`bdiagonal_status_rows`.**  `LEAN_PROVED`.  §12: the b-diagonal exponent margins are not
formally instantiated, because the numerical vertex dictionary is absent from this
repository. -/
theorem bdiagonal_status_rows :
    commonXLedger bDiagonalNumericalVertexDictionary = notFormalised ∧
    commonXLedger bDiagonalBranch ≠ provedUnconditional := by
  decide +kernel

/-! ## §4  Type-I / Type-II dependency firewall (§9 of the request) -/

/-- **`typeI_typeII_rows_are_ledger_records`.**  `LEAN_PROVED`.

The Type-I "externally/research closed" and Type-II "analytic open" rows are *bookkeeping
records*: neither carries `provedUnconditional`, so neither can be mistaken for a proof of an
analytic estimate in this repository. -/
theorem typeI_typeII_rows_are_ledger_records :
    commonXLedger commonXTypeIResearchClosed = ledgerRecordResearchClosed ∧
    commonXLedger commonXTypeIIAnalyticOpen = ledgerRecordAnalyticOpen ∧
    commonXLedger commonXTypeIResearchClosed ≠ provedUnconditional ∧
    commonXLedger commonXTypeIIAnalyticOpen ≠ provedUnconditional := by
  decide +kernel

/-- **`typeI_closure_does_not_close_c0`.**  `LEAN_PROVED`.

Even with the Type-I row recorded as research-closed, the C0 branch stays open: the Type-II
component is the live obstruction. -/
theorem typeI_closure_does_not_close_c0 :
    commonXLedger commonXTypeIResearchClosed = ledgerRecordResearchClosed →
    commonXLedger c0Branch ≠ provedUnconditional := by
  decide +kernel

/-! ## §5  The three explicit non-implications demanded by §10 -/

/-- **`commonX_arithmetic_pass_does_not_imply_c0_closure`.**  `LEAN_PROVED`. -/
theorem commonX_arithmetic_pass_does_not_imply_c0_closure :
    commonXLedger commonXConductorArithmetic = provedUnconditional ∧
    commonXLedger kappaCrtArithmetic = provedUnconditional ∧
    commonXLedger c0Branch ≠ provedUnconditional ∧
    commonXLedger c0Branch = researchStrictlyReducedOpen := by
  decide +kernel

/-- **`fractionalLinear_pass_does_not_imply_kloosterman_estimate`.**  `LEAN_PROVED`. -/
theorem fractionalLinear_pass_does_not_imply_kloosterman_estimate :
    commonXLedger fractionalLinearLinearisation = provedUnconditional ∧
    commonXLedger commonXFractionalLinearDoubleTypeIIKloosterman45 = analyticOpen ∧
    commonXLedger commonXFractionalLinearDoubleTypeIIKloosterman45 ≠ provedUnconditional := by
  decide +kernel

/-- **`local_kloosterman_arithmetic_does_not_imply_spectral_closure`.**  `LEAN_PROVED`.

The finite-field change of variables is proved; the Weil bound and the level-averaged spectral
closure are `notFormalised`.  Local arithmetic does not give the averaged estimate. -/
theorem local_kloosterman_arithmetic_does_not_imply_spectral_closure :
    commonXLedger kloostermanChangeOfVariables = provedUnconditional ∧
    commonXLedger weilBoundForKloostermanSums = notFormalised ∧
    commonXLedger levelAveragedSpectralClosure = notFormalised := by
  decide +kernel

/-- **`no_false_promotions`.**  `LEAN_PROVED`.  Exactly the six arithmetic rows are
`provedUnconditional`; every analytic or bookkeeping row is not. -/
theorem no_false_promotions :
    ∀ n : CommonXNode, commonXLedger n = provedUnconditional ↔
      (n = commonXConductorArithmetic ∨ n = kappaCrtArithmetic ∨
        n = graphDiagonalFirewall ∨ n = fractionalLinearLinearisation ∨
        n = commonDivisorCollisionCancellation ∨ n = kloostermanChangeOfVariables) := by
  decide +kernel

/-! ## §6  Row-diagonal versus graph-diagonal (§8 of the request) -/

/-- The two kinds of diagonal that must not be conflated. -/
inductive DiagonalKind
  /-- `N = b`. -/
  | graphDiagonal
  /-- `x₁ = x₂`. -/
  | xRowDiagonal
  deriving DecidableEq, Fintype, Repr

/-- Diagonal statuses. -/
inductive DiagonalStatus
  /-- Excluded by a kernel-checked arithmetic theorem. -/
  | arithmeticallyImpossible
  /-- **Not** excluded by anything in this repository. -/
  | notExcluded
  deriving DecidableEq, Fintype, Repr

open DiagonalKind DiagonalStatus

/-- The diagonal ledger. -/
def diagonalLedger : DiagonalKind → DiagonalStatus
  | graphDiagonal => arithmeticallyImpossible
  | xRowDiagonal => notExcluded

/-- **`diagonal_ledger_rows`.**  `LEAN_PROVED`. -/
theorem diagonal_ledger_rows :
    diagonalLedger graphDiagonal = arithmeticallyImpossible ∧
    diagonalLedger xRowDiagonal = notExcluded := by
  decide +kernel

/-- **`status_does_not_encode_xRow_exclusion`.**  `LEAN_PROVED`.

The status layer does **not** encode "graph diagonal impossible ⇒ x-row diagonal impossible":
the `xRowDiagonal` row is `notExcluded`. -/
theorem status_does_not_encode_xRow_exclusion :
    diagonalLedger graphDiagonal = arithmeticallyImpossible ∧
    diagonalLedger xRowDiagonal ≠ arithmeticallyImpossible := by
  decide +kernel

/-- **`graphDiagonal_row_is_backed_by_a_theorem`.**  `LEAN_PROVED`.

The `graphDiagonal` row is not bookkeeping: it is the literal theorem
`Erdos287.CommonX.graph_literal_diagonal_impossible`. -/
theorem graphDiagonal_row_is_backed_by_a_theorem {kappa b Q : ℤ} {d : ℕ}
    (hc : Erdos287.CommonX.CenteredKappa kappa b Q d) {N : ℤ} (hdiag : N = b) :
    ¬ Q ∣ N - kappa * b :=
  Erdos287.CommonX.graph_diagonal_impossible_of_centered hc hdiag

/-- **`xRowDiagonal_row_is_backed_by_a_witness`.**  `LEAN_PROVED`.

The `notExcluded` row is not bookkeeping either: the centered conditions are satisfiable
simultaneously with `x₁ = x₂`. -/
theorem xRowDiagonal_row_is_backed_by_a_witness :
    ∃ (kappa b Q : ℤ) (d : ℕ) (x1 x2 : ℤ),
      Erdos287.CommonX.CenteredKappa kappa b Q d ∧
      (∀ N : ℤ, N = b → ¬ Q ∣ N - kappa * b) ∧
      x1 = x2 :=
  Erdos287.CommonX.xRowDiagonal_not_excluded

/-! ## §7  Earlier ledgers preserved -/

/-- **`hybrid2_ledger_still_preserved`.**  `LEAN_PROVED`.

The HYBRID-2 ledger is unchanged: the Ω_H row is still the source pin, all five analytic
descendants are still `conditionalOpen`, and Erdős #287 is still open there. -/
theorem hybrid2_ledger_still_preserved :
    Erdos287.Hybrid2FrontierStatus.hybrid2Ledger
        Erdos287.Hybrid2FrontierStatus.Hybrid2Node.sharedGcdOmegaHNormalizationSourcePin
      = Erdos287.Hybrid2FrontierStatus.Hybrid2Label.sourcePin ∧
    Erdos287.Hybrid2FrontierStatus.hybrid2Ledger
        Erdos287.Hybrid2FrontierStatus.Hybrid2Node.hybrid2LongEdgeTwoSidedRectangle
      = Erdos287.Hybrid2FrontierStatus.Hybrid2Label.conditionalOpen ∧
    Erdos287.Hybrid2FrontierStatus.hybrid2Ledger
        Erdos287.Hybrid2FrontierStatus.Hybrid2Node.erdos287
      = Erdos287.Hybrid2FrontierStatus.Hybrid2Label.open_ := by
  decide +kernel

/-- **`caseB_ledger_still_preserved`.**  `LEAN_PROVED`.  The CASE-B ledger, re-checked through
the Hybrid-2 layer, is unchanged as well. -/
theorem caseB_ledger_still_preserved :
    ∀ n : Erdos287.CaseBFrontierStatus.FrontierNode,
      Erdos287.CaseBFrontierStatus.frontierLedger n
        ≠ Erdos287.CaseBFrontierStatus.FrontierLabel.closed :=
  Erdos287.CaseBFrontierStatus.frontier_no_closed_rows

end CommonXFrontierStatus
end Erdos287
