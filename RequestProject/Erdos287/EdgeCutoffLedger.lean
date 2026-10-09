import Mathlib
import RequestProject.Erdos287.IncrementalDirectedLedger

/-!
# Erdős #287 effectivity — the V<1000 edge replacement and the new numerical ledger (§26)

```
UPDATED SUBTOTAL           : KERNEL-PROVED
UPDATED CAPACITY           : KERNEL-PROVED
EDGE REPLACEMENT SEMANTICS : KERNEL-PROVED
V<50 / V<1000 FIREWALL     : KERNEL-PROVED
NEW EDGE NUMERICAL BOUND   : CERTIFICATE (explicit hypothesis object, not proved here)
```

The §21 ledger values are **superseded** by the long-fibre run.  Exact rationals:

    target                 = 8.86065e-7      = 886065/10^12
    new certified subtotal = 5.257263872e-7  = 5257263872/10^16
    new remaining capacity = 3.603386128e-7  = 3603386128/10^16

and `8.86065e-7 − 5.257263872e-7 = 3.603386128e-7` is proved by exact rational arithmetic.

The increment over the §21 subtotal is exactly the newly charged edge contribution
`7.22e-10 = 722/10^12`.  The replacement semantics are typed: a replacement edge estimate
updates the subtotal by `old − oldEdgeCharge + newEdgeCharge`, and charging *both* the old
`V<50` edge and the new `V<1000` edge is strictly larger, hence illegal
(`edge_double_charge_illegal`).

The analytic correctness of the new edge estimate is **not** an axiom and **not** proved:
it is carried as an explicit certificate object (`EdgeEstimateCertificate`), which must be
supplied from outside.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace Effectivity

/-! ## §26.1  The new authoritative numerical ledger -/

/-- The new certified subtotal, as an exact rational: `5.257263872e-7`. -/
def certifiedSubtotalV1000 : ℚ := 5257263872 / 10 ^ 16

/-- The new remaining capacity, as an exact rational: `3.603386128e-7`. -/
def remainingCapacityV1000 : ℚ := 3603386128 / 10 ^ 16

/-- **`ledger_difference_exact_v1000`.**  `KERNEL-PROVED`.

    8.86065e-7 − 5.257263872e-7 = 3.603386128e-7. -/
theorem ledger_difference_exact_v1000 :
    ledgerTarget - certifiedSubtotalV1000 = remainingCapacityV1000 := by
  rw [ledgerTarget, certifiedSubtotalV1000, remainingCapacityV1000]
  norm_num

/-- **`remaining_capacity_v1000_gt`.**  `KERNEL-PROVED`.  Under the strict subtotal
hypothesis `certifiedSubtotal < 5.257263872e-7` the remaining capacity exceeds
`3.603386128e-7`. -/
theorem remaining_capacity_v1000_gt {certifiedSubtotal : ℚ}
    (h : certifiedSubtotal < certifiedSubtotalV1000) :
    remainingCapacityV1000 < ledgerTarget - certifiedSubtotal := by
  rw [← ledger_difference_exact_v1000]
  linarith

/-- **`ledgerV1000_supersedes`.**  `KERNEL-PROVED`.  The new ledger genuinely supersedes the
§21 one: the certified subtotal has strictly increased and the remaining capacity has
strictly decreased. -/
theorem ledgerV1000_supersedes :
    certifiedSubtotalBound < certifiedSubtotalV1000 ∧
      remainingCapacityV1000 < remainingCapacityBound := by
  constructor
  · rw [certifiedSubtotalBound, certifiedSubtotalV1000]; norm_num
  · rw [remainingCapacityV1000, remainingCapacityBound]; norm_num

/-! ## §26.2  The edge-cutoff type and replacement semantics -/

/-- The status of the edge cutoff: the previously replayed cutoff, the currently replayed
cutoff, and the two edge charges involved in the replacement. -/
structure EdgeCutoffStatus where
  /-- The previously replayed edge cutoff (here `50`). -/
  previousCutoff : ℕ
  /-- The currently replayed edge cutoff (here `1000`). -/
  currentCutoff : ℕ
  /-- The edge charge previously carried by the subtotal. -/
  oldEdgeCharge : ℚ
  /-- The edge charge carried by the replacement estimate. -/
  newEdgeCharge : ℚ
  /-- A replacement genuinely extends the replayed range. -/
  cutoff_increases : previousCutoff < currentCutoff

/-- The subtotal after a replacement: `old − oldEdgeCharge + newEdgeCharge`. -/
def updatedSubtotal (old : ℚ) (E : EdgeCutoffStatus) : ℚ :=
  old - E.oldEdgeCharge + E.newEdgeCharge

/-- The (illegal) subtotal that would result from charging *both* edge estimates. -/
def doubleChargedSubtotal (old : ℚ) (E : EdgeCutoffStatus) : ℚ :=
  old + E.oldEdgeCharge + E.newEdgeCharge

/-- **`updatedSubtotal_eq`.**  `KERNEL-PROVED`.  The replacement update law at the
arithmetic level. -/
theorem updatedSubtotal_eq (old : ℚ) (E : EdgeCutoffStatus) :
    updatedSubtotal old E = old - E.oldEdgeCharge + E.newEdgeCharge := rfl

/-- **`edge_double_charge_illegal`.**  `KERNEL-PROVED`.  Charging both the old and the new
edge estimate strictly overcharges the ledger whenever the old edge charge is positive: the
two bookkeeping conventions coincide only when the old edge charge is zero. -/
theorem edge_double_charge_illegal (old : ℚ) (E : EdgeCutoffStatus) :
    (updatedSubtotal old E = doubleChargedSubtotal old E ↔ E.oldEdgeCharge = 0) ∧
      (0 < E.oldEdgeCharge → updatedSubtotal old E < doubleChargedSubtotal old E) := by
  constructor
  · constructor
    · intro h
      rw [updatedSubtotal, doubleChargedSubtotal] at h
      linarith
    · intro h
      rw [updatedSubtotal, doubleChargedSubtotal, h]
      ring
  · intro h
    rw [updatedSubtotal, doubleChargedSubtotal]
    linarith

/-- The concrete `V<50 → V<1000` replacement, for supplied edge charges. -/
def v50ToV1000 (oldEdgeCharge newEdgeCharge : ℚ) : EdgeCutoffStatus where
  previousCutoff := 50
  currentCutoff := 1000
  oldEdgeCharge := oldEdgeCharge
  newEdgeCharge := newEdgeCharge
  cutoff_increases := by norm_num

@[simp] theorem v50ToV1000_previousCutoff (o n : ℚ) : (v50ToV1000 o n).previousCutoff = 50 := rfl

@[simp] theorem v50ToV1000_currentCutoff (o n : ℚ) : (v50ToV1000 o n).currentCutoff = 1000 := rfl

/-- The charged value of the new `V<1000` edge contribution: `7.22e-10`. -/
def edgeChargeV1000 : ℚ := 722 / 10 ^ 12

/-- **`subtotal_update_v1000`.**  `KERNEL-PROVED`.  A replacement whose net effect is
`+7.22e-10` takes the §21 subtotal bound to the new certified subtotal:

    5.250043872e-7 − oldEdge + newEdge = 5.257263872e-7   whenever  newEdge − oldEdge = 7.22e-10. -/
theorem subtotal_update_v1000 (E : EdgeCutoffStatus)
    (hnet : E.newEdgeCharge - E.oldEdgeCharge = edgeChargeV1000) :
    updatedSubtotal certifiedSubtotalBound E = certifiedSubtotalV1000 := by
  have h : E.newEdgeCharge = E.oldEdgeCharge + edgeChargeV1000 := by linarith [hnet]
  rw [updatedSubtotal, h, certifiedSubtotalBound, certifiedSubtotalV1000, edgeChargeV1000]
  ring_nf

/-- **`certifiedSubtotalV1000_eq`.**  `KERNEL-PROVED`.  The new subtotal is exactly the §21
subtotal plus the charged `V<1000` edge value. -/
theorem certifiedSubtotalV1000_eq :
    certifiedSubtotalV1000 = certifiedSubtotalBound + edgeChargeV1000 := by
  rw [certifiedSubtotalV1000, certifiedSubtotalBound, edgeChargeV1000]
  norm_num

/-! ## §26.3  The edge numerical certificate -/

/-- A numerical certificate for an edge estimate: the replayed cutoff, the claimed value and
a strict upper bound for it.  Inhabiting this structure *is* the certificate; nothing in this
package proves the analytic edge bound, and no axiom is introduced for it. -/
structure EdgeEstimateCertificate where
  /-- The replayed cutoff. -/
  cutoff : ℕ
  /-- The true edge contribution. -/
  value : ℚ
  /-- The certified strict upper bound. -/
  bound : ℚ
  /-- The certificate hypothesis. -/
  value_lt : value < bound

/-- **`edgeCertificate_v1000`.**  `KERNEL-PROVED` (conditional on the supplied certificate).
A `V<1000` certificate with bound `7.22e-10` bounds the true edge contribution by the
charged value. -/
theorem edgeCertificate_v1000 (C : EdgeEstimateCertificate) (hc : C.cutoff = 1000)
    (hb : C.bound = edgeChargeV1000) : C.cutoff = 1000 ∧ C.value < edgeChargeV1000 :=
  ⟨hc, hb ▸ C.value_lt⟩

/-- **`edgeCertificate_not_proved`.**  `KERNEL-PROVED`.  A firewall: the certificate type is
inhabited for *every* bound, so possessing an `EdgeEstimateCertificate` proves nothing about
the physical edge contribution — the analytic content must come from outside. -/
theorem edgeCertificate_not_proved (bound : ℚ) :
    ∃ C : EdgeEstimateCertificate, C.cutoff = 1000 ∧ C.bound = bound :=
  ⟨⟨1000, bound - 1, bound, by linarith⟩, rfl, rfl⟩

end Effectivity
end Erdos287
