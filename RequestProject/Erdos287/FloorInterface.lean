import Mathlib
import RequestProject.Erdos287.DirectedLedger

/-!
# Erdős #287 — conditional floor-closure interface and open-node firewall

```
CONDITIONAL BUDGET THEOREM        : KERNEL-PROVED (mediumK_gap_budget_implies_boundary_target)
LEDGER-INSTANTIATED BUDGET        : KERNEL-PROVED (boundary_target_of_ledger_budget)
q=3 CERTIFICATE RECORD / INTERFACE: DEFINED (EXTERNAL MACHINE-CERTIFICATE RESULT)
OPEN NODES                        : DEFINED AS PREDICATES ONLY — NOT PROVED
```

## Firewall

Nothing in this file proves, or postulates, any of

* the medium-`k` joint Bernoulli large-sieve closure,
* the two-high `a ≤ 180` nonlinear Mellin closure,
* the signed `B_src` floor closure,
* Maynard effectivity,
* Erdős #287.

They appear only as *predicates* on supplied data, so that downstream statements can be
made explicitly conditional on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace FloorInterface

/-! ## §12  The `q = 3` prefix certificate interface -/

/-- The record format of the `q = 3` segmented-sieve prefix certificate: a range
`[lo, hi]` and a declared constant. -/
structure Q3PrefixCertificate where
  lo : ℕ
  hi : ℕ
  constant : ℚ
  deriving Repr, DecidableEq

/-- The declared summary of a `q = 3` prefix certificate, relative to a supplied character
sum `A`:  `|A(x)| ≤ constant · √x` throughout the declared range. -/
def Q3PrefixCertificate.Claim (cert : Q3PrefixCertificate) (A : ℕ → ℝ) : Prop :=
  ∀ x : ℕ, cert.lo ≤ x → x ≤ cert.hi → |A x| ≤ (cert.constant : ℝ) * Real.sqrt x

/-- The certificate actually reported by the research bank:
`|A_χ₃(x)| ≤ (2/5)·√x` for `x ∈ [10⁶, 4.5·10⁹]`.

`EXTERNAL MACHINE-CERTIFICATE INPUT`: the underlying 4.5·10⁹-term segmented sieve is **not**
replayed inside Lean, and the claim is **not** asserted here.  Only the format and the exact
downstream consequences are formalised. -/
def q3Certificate : Q3PrefixCertificate :=
  { lo := 10 ^ 6, hi := 4500000000, constant := 2 / 5 }

/-- A downstream consequence of the `q = 3` prefix claim, stated conditionally: inside the
certified range the normalised character sum is bounded by the declared constant. -/
theorem q3_normalised_bound {A : ℕ → ℝ} (h : q3Certificate.Claim A) {x : ℕ}
    (hlo : 10 ^ 6 ≤ x) (hhi : x ≤ 4500000000) :
    |A x| ≤ (2 / 5 : ℝ) * Real.sqrt x := by
  have := h x hlo hhi
  simpa [q3Certificate] using this

/-- The recorded `q = 3` physical directed charge, `< 2.17e-8 · B_X`. -/
def q3PhysicalCharge : ℚ := DirectedLedger.certQ3Row

/-! ## §14  The conditional floor-closure theorem -/

/-- **`mediumK_gap_budget_implies_boundary_target`.** `KERNEL-PROVED`.  A pure ordered-field
statement: if the two open consumers together fit strictly inside the remaining capacity,
the total boundary charge is strictly below target. -/
theorem mediumK_gap_budget_implies_boundary_target
    {certifiedSubtotal target MediumK GapA180 totalBoundaryCharge : ℝ}
    (hdecomp : totalBoundaryCharge ≤ certifiedSubtotal + (|MediumK| + |GapA180|))
    (hbudget : |MediumK| + |GapA180| < target - certifiedSubtotal) :
    totalBoundaryCharge < target := by
  linarith

/-- **`boundary_target_of_ledger_budget`.** `KERNEL-PROVED`.  The same statement with the
kernel-verified ledger numbers substituted: the usable budget for the two open consumers is
the **corrected** remaining capacity `3.6417761249e-7`, not the printed `3.641776128e-7`. -/
theorem boundary_target_of_ledger_budget {MediumK GapA180 totalBoundaryCharge : ℝ}
    (hdecomp : totalBoundaryCharge ≤
      ((DirectedLedger.certifiedSubtotal : ℚ) : ℝ) + (|MediumK| + |GapA180|))
    (hbudget : |MediumK| + |GapA180| < (36417761249 : ℝ) / 10 ^ 17) :
    totalBoundaryCharge < ((DirectedLedger.target : ℚ) : ℝ) := by
  refine mediumK_gap_budget_implies_boundary_target hdecomp ?_
  have hrem : ((DirectedLedger.remainingCapacity : ℚ) : ℝ) = (36417761249 : ℝ) / 10 ^ 17 := by
    rw [DirectedLedger.remainingCapacity_correct]; norm_num
  have hdef : ((DirectedLedger.remainingCapacity : ℚ) : ℝ)
      = ((DirectedLedger.target : ℚ) : ℝ) - ((DirectedLedger.certifiedSubtotal : ℚ) : ℝ) := by
    rw [DirectedLedger.remainingCapacity]; push_cast; ring
  rw [← hdef, hrem]
  exact hbudget

/-- The already-banked empty-`J` interface value `|R_∅|/B_X < 8.56e-8`, carried as a
**conditional** hypothesis only. -/
def RemptyBound : ℚ := 856 / 10 ^ 10

/-- Conditional combination with the banked empty-`J` bound. -/
theorem boundary_target_with_Rempty {Rempty MediumK GapA180 totalBoundaryCharge : ℝ}
    (hEmpty : |Rempty| < ((RemptyBound : ℚ) : ℝ))
    (hdecomp : totalBoundaryCharge ≤
      ((DirectedLedger.certifiedSubtotal : ℚ) : ℝ) + (|MediumK| + |GapA180|))
    (hbudget : |MediumK| + |GapA180| < (36417761249 : ℝ) / 10 ^ 17) :
    totalBoundaryCharge < ((DirectedLedger.target : ℚ) : ℝ) ∧ |Rempty| < ((RemptyBound : ℚ) : ℝ) :=
  ⟨boundary_target_of_ledger_budget hdecomp hbudget, hEmpty⟩

/-! ## §15  Open-node firewall -/

/-- **OPEN.** The medium-`k` joint Bernoulli large-sieve closure, as a predicate on a
supplied value and budget.  Not proved anywhere in this project. -/
def MediumKJointBernoulliClosed (MediumK budget : ℝ) : Prop := |MediumK| < budget

/-- **OPEN.** The two-high `a ≤ 180` nonlinear Mellin closure. Not proved. -/
def TwoHighA180Closed (GapA180 budget : ℝ) : Prop := |GapA180| < budget

/-- **OPEN.** The signed `B_src` floor closure: the signed floor dominates the boundary
charge.  Not proved. -/
def SignedBsrcFloorClosed (signedFloor totalBoundaryCharge : ℝ) : Prop :=
  totalBoundaryCharge < signedFloor

-- **MAYNARD: NOT ENTERED.**  No Maynard-effectivity statement is defined or used anywhere
-- in this development; there is deliberately no placeholder predicate for it here.

/-- **`open_nodes_imply_boundary_target`.** `KERNEL-PROVED`.  The exact shape of what the
two open nodes would buy: nothing more, nothing less. -/
theorem open_nodes_imply_boundary_target
    {MediumK GapA180 bM bG totalBoundaryCharge : ℝ}
    (hM : MediumKJointBernoulliClosed MediumK bM)
    (hG : TwoHighA180Closed GapA180 bG)
    (hsum : bM + bG ≤ (36417761249 : ℝ) / 10 ^ 17)
    (hdecomp : totalBoundaryCharge ≤
      ((DirectedLedger.certifiedSubtotal : ℚ) : ℝ) + (|MediumK| + |GapA180|)) :
    totalBoundaryCharge < ((DirectedLedger.target : ℚ) : ℝ) := by
  refine boundary_target_of_ledger_budget hdecomp ?_
  have := add_lt_add hM hG
  linarith

end FloorInterface
end Erdos287
