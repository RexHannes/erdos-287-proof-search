import Mathlib
import RequestProject.Erdos287.CurrentStatusEffectivityBoundedConductor
import RequestProject.Erdos287.FixedConductorCharacterRepair
import RequestProject.Erdos287.BoundedConductorTargetAudit
import RequestProject.Erdos287.CentredFrontierTriviality
import RequestProject.CurrentProgramme.Erdos287September3FiniteExtension24Window

/-!
# Erdős #287 effectivity — status after the frontier audit (§63)

INTERNAL #287 EFFECTIVITY PROGRAMME ONLY.
**No public Erdős problem number is claimed here; public-problem-id provenance is `PENDING`.**

This module **extends** `CurrentStatusEffectivityBoundedConductor`.  Nothing earlier is
rewritten or deleted; the whole historical bank (EARLY_4490, long-fibre, multiplicity,
bounded-conductor) is preserved, and every ancestor theorem keeps its statement.

What changed at this checkpoint is the status of two *targets* — not of any proved theorem:

```
FixedConductorCharacterBound (unnormalised) : REFUTED  (fixedConductorCharacterBound_unsatisfiable)
FixedConductorCharacterMeanBound (normalised): REFUTED (characterMeanBound_unsatisfiable)
BoundedConductorK1Target (pointwise)        : REFUTED  (boundedConductorK1Target_unsatisfiable)
CentredBoundedConductorK1Target             : OPEN — new live k = 1 coordinate
```

The obstruction is a *density* obstruction, not a cancellation failure: the returned
finite-conductor kernel has aggregate complete-period mean

    meanSum = ∑_{1000 < ℓ ≤ 5000} meanK ℓ ≠ 0     (`meanSum_ne_zero`, 4999-adic valuation −1)

so over `n` full periods it equals `P·n·meanSum`, which is unbounded.  Subtracting the exact
density term gives the replacement target `CentredBoundedConductorK1Target`, on which the
long-window witness vanishes identically (`centred_kernel_vanishes_on_full_periods`).  This
matches the already-banked firewall `DX_term_not_removable`.

All other open owners are unchanged: `Ω(k) = 2`, `Ω(k) = 1`, EARLY_4490 residual, proper
gamma, `S_live`, `R_012`, signed floor, final splice, and Erdős #287 itself.

The finite side of the bank is recorded here too: the kernel-verified finite exclusion
currently reaches `M ≤ 67108856338751594` (`no_Erdos287Counterexample_of_max_le_extendedCeiling`).
A `10^60` ceiling is **not** present in this repository, and the `U2` certified-factor
extension is **pending** (its inputs are not supplied here); both facts are recorded below as
data, and `finite_ceiling_below_ten_pow_sixty` proves the recorded ceiling is strictly below
`10^60`, so no `10^60` claim is implied.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace Effectivity

/-! ## §63.1  Checkpoint -/

/-- The checkpoint of the frontier audit. -/
def frontierAuditCheckpoint : Checkpoint :=
  { date := "2026-09-10", version := "FRONTIER_AUDIT_v1" }

/-- **`frontierAudit_checkpoint_tag`.** -/
theorem frontierAudit_checkpoint_tag :
    frontierAuditCheckpoint.date = "2026-09-10" ∧
      frontierAuditCheckpoint.version = "FRONTIER_AUDIT_v1" :=
  ⟨rfl, rfl⟩

/-! ## §63.2  The audited nodes -/

/-- The nodes whose status this audit determines. -/
inductive FrontierAuditNode
  /-- the unnormalised fixed-conductor character interface -/
  | characterBoundUnnormalised
  /-- the normalised (mean) character interface -/
  | characterBoundNormalised
  /-- the pointwise bounded-conductor `k = 1` target -/
  | boundedConductorK1Target
  /-- the long-window period law for the returned kernel -/
  | longWindowPeriodLaw
  /-- non-vanishing of the aggregate complete-period mean -/
  | aggregateMeanNonzero
  /-- the density-centred replacement target, qualitatively -/
  | centredK1TargetQualitative
  /-- a *quantitative* ledger-admissible budget for the centred target -/
  | centredK1TargetQuantitative
  deriving DecidableEq, Repr

/-- Evidence class of each audited node at this checkpoint. -/
def frontierAuditEvidence : FrontierAuditNode → EvidenceCurrent
  | .characterBoundUnnormalised => .falseClaim
  | .characterBoundNormalised => .falseClaim
  | .boundedConductorK1Target => .falseClaim
  | .longWindowPeriodLaw => .kernelProved
  | .aggregateMeanNonzero => .kernelProved
  | .centredK1TargetQualitative => .kernelProved
  | .centredK1TargetQuantitative => .openNode

/-- **`frontierAudit_refutations_are_backed`.**  `KERNEL-PROVED`.  Every node tagged
`falseClaim` is backed by an actual refutation, for every budget. -/
theorem frontierAudit_refutations_are_backed (b : ℚ) :
    (frontierAuditEvidence .characterBoundUnnormalised = EvidenceCurrent.falseClaim ∧
        ¬ FixedConductorCharacterBound b) ∧
      (frontierAuditEvidence .characterBoundNormalised = EvidenceCurrent.falseClaim ∧
        ¬ FixedConductorCharacterMeanBound b) ∧
      (frontierAuditEvidence .boundedConductorK1Target = EvidenceCurrent.falseClaim ∧
        ¬ BoundedConductorK1Target b) :=
  ⟨⟨rfl, fixedConductorCharacterBound_unsatisfiable b⟩,
    ⟨rfl, characterMeanBound_unsatisfiable b⟩,
    ⟨rfl, boundedConductorK1Target_unsatisfiable b⟩⟩

/-- The audited nodes that remain open. -/
def frontierAuditOpenNodes : List FrontierAuditNode := [.centredK1TargetQuantitative]

/-- **`centred_target_qualitatively_settled`.**  `KERNEL-PROVED`.  Some budget always works
for the centred target, so qualitative boundedness carries no analytic content; the
quantitative budget question is the node that stays open. -/
theorem centred_target_qualitatively_settled :
    (∃ b : ℚ, CentredBoundedConductorK1Target b) ∧
      frontierAuditEvidence .centredK1TargetQuantitative = EvidenceCurrent.openNode :=
  ⟨centred_target_exists_budget, rfl⟩

/-- **`frontierAudit_open_frontier`.**  `KERNEL-PROVED`.  No open node is tagged closed, and
no refuted node is tagged closed either. -/
theorem frontierAudit_open_frontier :
    (∀ n ∈ frontierAuditOpenNodes, (frontierAuditEvidence n).isClosed = false) ∧
      (frontierAuditEvidence .characterBoundUnnormalised).isClosed = false ∧
      (frontierAuditEvidence .characterBoundNormalised).isClosed = false ∧
      (frontierAuditEvidence .boundedConductorK1Target).isClosed = false := by
  refine ⟨?_, rfl, rfl, rfl⟩
  intro n hn
  fin_cases hn
  rfl

/-- **`early4490_and_bank_preserved`.**  `KERNEL-PROVED`.  This audit changes the status of
*targets* only: the ancestor banks keep their evidence classes. -/
theorem early4490_and_bank_preserved :
    boundedConductorEvidence .early4490BankAncestor = EvidenceCurrent.certificateBacked ∧
      boundedConductorEvidence .smallEllLocalMean = EvidenceCurrent.kernelProved ∧
      boundedConductorEvidence .crtAtomBound = EvidenceCurrent.kernelProved ∧
      boundedConductorEvidence .loopCancellationSmallEll = EvidenceCurrent.kernelProved :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## §63.3  The finite side of the bank -/

/-- Status of a finite-range exclusion claim. -/
inductive FiniteStatus
  /-- verified in the Lean kernel in this repository -/
  | kernelProved
  /-- not present in this repository -/
  | notPresent
  /-- announced but with inputs not supplied here -/
  | pending
  deriving DecidableEq, Repr

/-- Recorded status of the three finite ceilings discussed in the programme. -/
def finiteStatus : ℕ → FiniteStatus
  | 0 => .kernelProved  -- `M ≤ 67108856338751594`
  | 1 => .notPresent    -- `M ≤ 10^60`
  | _ => .pending       -- the `U2` certified-factor extension

/-- **`finite_bank_status_recorded`.**  `KERNEL-PROVED` bookkeeping. -/
theorem finite_bank_status_recorded :
    finiteStatus 0 = FiniteStatus.kernelProved ∧ finiteStatus 1 = FiniteStatus.notPresent ∧
      finiteStatus 2 = FiniteStatus.pending :=
  ⟨rfl, rfl, rfl⟩

/-- **`finite_ceiling_kernel_proved`.**  `KERNEL-PROVED`.  The finite exclusion actually
available in this repository, restated at this checkpoint. -/
theorem finite_ceiling_kernel_proved {A : Finset ℕ} (h : Erdos287Counterexample A)
    (hM : A.max' h.nonempty ≤ extendedCeiling) : False :=
  no_Erdos287Counterexample_of_max_le_extendedCeiling' h hM

/-- **`finite_ceiling_below_ten_pow_sixty`.**  `KERNEL-PROVED`.  The available ceiling is far
below `10^60`: no `10^60` finite result is claimed by this bank. -/
theorem finite_ceiling_below_ten_pow_sixty : extendedCeiling < 10 ^ 60 := by
  rw [extendedCeiling]
  norm_num

/-! ## §63.4  Axiom audit -/

#print axioms Erdos287.Effectivity.fixedConductorCharacterBound_unsatisfiable
#print axioms Erdos287.Effectivity.characterMeanBound_iff_boundedConductorTarget
#print axioms Erdos287.Effectivity.returnedKernel_one_point_window
#print axioms Erdos287.Effectivity.returnedKernel_long_window
#print axioms Erdos287.Effectivity.meanSum_ne_zero
#print axioms Erdos287.Effectivity.boundedConductorK1Target_unsatisfiable
#print axioms Erdos287.Effectivity.characterMeanBound_unsatisfiable
#print axioms Erdos287.Effectivity.centred_kernel_vanishes_on_full_periods
#print axioms Erdos287.Effectivity.frontier_repair_summary
#print axioms Erdos287.Effectivity.frontierAudit_refutations_are_backed
#print axioms Erdos287.Effectivity.frontierAudit_open_frontier
#print axioms Erdos287.Effectivity.abs_Kell_le
#print axioms Erdos287.Effectivity.periodBlock_base_independent
#print axioms Erdos287.Effectivity.windowSum_centred_bound
#print axioms Erdos287.Effectivity.centred_target_satisfiable
#print axioms Erdos287.Effectivity.qualitative_boundedness_has_no_analytic_content
#print axioms Erdos287.Effectivity.centred_target_qualitatively_settled
#print axioms Erdos287.Effectivity.finite_ceiling_kernel_proved

end Effectivity
end Erdos287
