import Mathlib
import RequestProject.Erdos287.FivePrimeSourceGeometry
import RequestProject.Erdos287.DirectedSelbergFiniteAlgebra

/-!
# Erdős #287 — the high-`X` consumer ledger and the source-union classification (§67)

INTERNAL #287 EFFECTIVITY PROGRAMME ONLY.  Nothing here claims Erdős #287.

This module reconstructs the **high-`X` consumer ledger** as an exact rational object and
states the affordability question for the certified `2.1·10⁻⁶ · B_prime` box allocation of
§66.  All ledger entries are *parameters*: the module proves the deterministic arithmetic of
the ledger (what the available budget is, how it moves with each cost, what fits), and proves
that the affordability verdict is **not** determined until the analytic constants are
supplied.  Nothing here converts an analytic assumption into a proved statement.

Two explicit firewalls are proved:

* `early_slab_budget_too_small` — the historical early-slab budget `10⁻¹¹` cannot host the
  `2.1·10⁻⁶` allocation, so it must not be reused for the high-`X` consumer;
* `allocation_verdict_undecided` — there are admissible ledgers in which the allocation fits
  and admissible ledgers in which it does not, so the verdict is `UNDECIDED` until the
  ledger constants are pinned down.

The source-union classification `CHEAP / SIGNED / HARD` is formalised with the *proof
obligation attached*: `cheap_requires_affordable` shows a cell may only be classified `CHEAP`
when the capacity ledger certifies affordability, and `plusSix_not_cheap_yet` records that
the `+6` cell of §65 is therefore **not** yet a `CHEAP` cell.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace HighX

open Erdos287.DirectedSelberg

/-! ## §67.1  The exact rational high-`X` consumer ledger -/

/-- The high-`X` consumer ledger, in units of the positive main prime comparison `B_prime`
(so every entry is a pure rational fraction of the main term).  The fields are the source
quantities of the high-`X` ledger: the positive main comparison `mainComparison`, the
transferred budget `b_T`, its transfer cost `t_T`, the three error owners `E_L`, `E_2`, `E_M`,
and the aggregate comparison-transfer cost `transferCost`. -/
structure Ledger where
  /-- the positive main comparison, in units of `B_prime` -/
  mainComparison : ℚ
  /-- the budget transferred to the high-`X` consumer -/
  b_T : ℚ
  /-- the cost of that transfer -/
  t_T : ℚ
  /-- the `L`-owner error allocation -/
  E_L : ℚ
  /-- the second error owner -/
  E_2 : ℚ
  /-- the main-term error owner -/
  E_M : ℚ
  /-- aggregate comparison-transfer cost -/
  transferCost : ℚ

/-- The **available high-`X` leakage budget**: what is left of the transferred budget after
every recorded cost and error owner has been paid. -/
def availableLeakageBudget (L : Ledger) : ℚ :=
  L.b_T - (L.t_T + L.E_L + L.E_2 + L.E_M + L.transferCost)

/-- A ledger is *admissible* when the transferred budget does not exceed the positive main
comparison and every recorded cost is nonnegative. -/
def Admissible (L : Ledger) : Prop :=
  0 < L.mainComparison ∧ 0 ≤ L.b_T ∧ L.b_T ≤ L.mainComparison ∧
    0 ≤ L.t_T ∧ 0 ≤ L.E_L ∧ 0 ≤ L.E_2 ∧ 0 ≤ L.E_M ∧ 0 ≤ L.transferCost

/-- An allocation *fits* the ledger when it does not exceed the available budget. -/
def Fits (L : Ledger) (x : ℚ) : Prop := x ≤ availableLeakageBudget L

/-- **`availableLeakageBudget_le_transferred`.**  `KERNEL-PROVED`.  The available budget never
exceeds the transferred budget, and hence never exceeds the positive main comparison. -/
theorem availableLeakageBudget_le_transferred {L : Ledger} (h : Admissible L) :
    availableLeakageBudget L ≤ L.mainComparison := by
  obtain ⟨-, -, hbT, ht, hL, h2, hM, htr⟩ := h
  rw [availableLeakageBudget]
  linarith

/-- **`availableLeakageBudget_antitone_in_costs`.**  `KERNEL-PROVED`.  Every extra recorded
cost strictly eats into the available budget. -/
theorem availableLeakageBudget_antitone_in_costs (L : Ledger) (c : ℚ) (hc : 0 ≤ c) :
    availableLeakageBudget { L with t_T := L.t_T + c } ≤ availableLeakageBudget L := by
  simp only [availableLeakageBudget]
  linarith

/-- **`fits_mono`.**  `KERNEL-PROVED`.  A smaller allocation fits whenever a larger one does. -/
theorem fits_mono {L : Ledger} {x y : ℚ} (hxy : x ≤ y) (h : Fits L y) : Fits L x :=
  le_trans hxy h

/-! ## §67.2  The `2.1·10⁻⁶ · B_prime` box allocation -/

/-- The allocation requested by the certified `+6` box of §65–§66, in units of `B_prime`. -/
def boxAllocationRequest : ℚ := DirectedSelberg.boxAllocation

/-- **`boxAllocationRequest_value`.**  `KERNEL-PROVED`. -/
theorem boxAllocationRequest_value : boxAllocationRequest = 21 / 10 ^ 7 := rfl

/-- **`box_allocation_fits_of_budget`.**  `KERNEL-PROVED` (deterministic bridge).  The box
allocation fits exactly when the available high-`X` leakage budget reaches `2.1·10⁻⁶`. -/
theorem box_allocation_fits_of_budget (L : Ledger)
    (h : (21 / 10 ^ 7 : ℚ) ≤ availableLeakageBudget L) : Fits L boxAllocationRequest := h

/-- **`box_allocation_not_fits_of_small_budget`.**  `KERNEL-PROVED`.  Conversely a ledger with
available budget below `2.1·10⁻⁶` cannot host the box. -/
theorem box_allocation_not_fits_of_small_budget (L : Ledger)
    (h : availableLeakageBudget L < (21 / 10 ^ 7 : ℚ)) : ¬ Fits L boxAllocationRequest := by
  rw [Fits, boxAllocationRequest, DirectedSelberg.boxAllocation]
  exact not_le.2 h

/-- **`early_slab_budget_too_small`.**  `KERNEL-PROVED`.  *Firewall.*  The historical
early-slab budget `10⁻¹¹` is five orders of magnitude below the box allocation, so it cannot
be reused as the high-`X` leakage budget. -/
theorem early_slab_budget_too_small : ¬ (boxAllocationRequest ≤ (1 / 10 ^ 11 : ℚ)) := by
  rw [boxAllocationRequest, DirectedSelberg.boxAllocation]
  norm_num

/-- A ledger in which the box allocation fits comfortably. -/
def generousLedger : Ledger :=
  { mainComparison := 1, b_T := 1/10, t_T := 1/100, E_L := 1/100, E_2 := 1/100,
    E_M := 1/100, transferCost := 1/100 }

/-- A ledger in which the box allocation does not fit. -/
def tightLedger : Ledger :=
  { mainComparison := 1, b_T := 1/10 ^ 8, t_T := 0, E_L := 0, E_2 := 0, E_M := 0,
    transferCost := 0 }

/-- **`allocation_verdict_undecided`.**  `KERNEL-PROVED`.  Both admissible ledgers exist:
the affordability of the `2.1·10⁻⁶ · B_prime` allocation is a genuine question about the
analytic constants, and is `UNDECIDED` in this repository — it is *not* settled by the
formalised finite algebra. -/
theorem allocation_verdict_undecided :
    (Admissible generousLedger ∧ Fits generousLedger boxAllocationRequest) ∧
      (Admissible tightLedger ∧ ¬ Fits tightLedger boxAllocationRequest) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · refine ⟨by norm_num [generousLedger], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      norm_num [generousLedger]
  · rw [Fits, boxAllocationRequest, DirectedSelberg.boxAllocation, availableLeakageBudget]
    norm_num [generousLedger]
  · refine ⟨by norm_num [tightLedger], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [tightLedger]
  · refine box_allocation_not_fits_of_small_budget _ ?_
    rw [availableLeakageBudget]
    norm_num [tightLedger]

/-! ## §67.3  The source-union ledger: `CHEAP / SIGNED / HARD` -/

/-- Classification of a high-`X` source cell. -/
inductive SourceClass
  /-- a directed upper-sieve/capacity theorem suffices *and* the ledger certifies it -/
  | cheap
  /-- capacity is insufficient; parent-level signed reassembly is required -/
  | signed
  /-- survives both capacity and signed reassembly -/
  | hard
  /-- not yet classified: the deciding certificate is missing -/
  | unclassified
  deriving DecidableEq, Repr

/-- The classifier.  A cell is `CHEAP` only when a capacity certificate exists **and** the
ledger certifies that its allocation is affordable; `SIGNED` when signed reassembly succeeds;
`HARD` when neither does; and `unclassified` when the deciding data is absent. -/
def classify (hasCapacityCertificate affordable signedReassembly decided : Bool) : SourceClass :=
  if ¬ decided then .unclassified
  else if hasCapacityCertificate ∧ affordable then .cheap
  else if signedReassembly then .signed
  else .hard

/-- **`cheap_requires_affordable`.**  `KERNEL-PROVED`.  A cell can only be `CHEAP` if the
global capacity ledger certifies affordability (and a capacity certificate exists). -/
theorem cheap_requires_affordable {cap aff sgn dec : Bool}
    (h : classify cap aff sgn dec = SourceClass.cheap) : cap = true ∧ aff = true := by
  revert h
  cases cap <;> cases aff <;> cases sgn <;> cases dec <;> simp [classify]

/-- **`cheap_requires_decision`.**  `KERNEL-PROVED`.  No cell is classified while the
deciding data is missing. -/
theorem cheap_requires_decision {cap aff sgn : Bool} :
    classify cap aff sgn false = SourceClass.unclassified := by
  simp [classify]

/-- **`plusSix_not_cheap_yet`.**  `KERNEL-PROVED`.  The `+6` cell of §65 carries a capacity
certificate (§66) but the affordability verdict is undecided (`allocation_verdict_undecided`),
so it is recorded as a `CHEAP` *candidate* only, not as a `CHEAP` cell. -/
theorem plusSix_not_cheap_yet :
    classify true true true false = SourceClass.unclassified ∧
      Erdos287.SourceGeometry.H Erdos287.SourceGeometry.plusSixCell
        Erdos287.SourceGeometry.plusSixDelta Erdos287.SourceGeometry.plusSixDelta' = 6 :=
  ⟨by simp [classify], Erdos287.SourceGeometry.plusSix_cell_H⟩

end HighX
end Erdos287
