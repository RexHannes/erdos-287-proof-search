import Mathlib
import RequestProject.Erdos287.MediumLedger

/-!
# Erdős #287 effectivity — the incremental directed ledger (§21)

```
INCREMENTAL LEDGER ARITHMETIC : KERNEL-PROVED
```

Exact rationals only:

    target             = 8.86065e-7        = 886065/10^12
    certifiedSubtotal  < 5.250043872e-7    = 5250043872/10^16
    target − 5.250043872e-7 = 3.610606128e-7

Under the strict subtotal hypothesis the remaining capacity is `> 3.610606128e-7`.
No full-replacement allowance is formalised: none is legal without an explicit removal
list (see `Erdos287.Effectivity.no_naive_full_insertion` in `MediumLedger`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace Effectivity

/-- The directed target, as an exact rational: `8.86065e-7`. -/
def ledgerTarget : ℚ := 886065 / 10 ^ 12

/-- The strict certified-subtotal bound, as an exact rational: `5.250043872e-7`. -/
def certifiedSubtotalBound : ℚ := 5250043872 / 10 ^ 16

/-- The remaining capacity figure, as an exact rational: `3.610606128e-7`. -/
def remainingCapacityBound : ℚ := 3610606128 / 10 ^ 16

/-- **`ledger_difference_exact`.**  `KERNEL-PROVED`.

    8.86065e-7 − 5.250043872e-7 = 3.610606128e-7. -/
theorem ledger_difference_exact :
    ledgerTarget - certifiedSubtotalBound = remainingCapacityBound := by
  rw [ledgerTarget, certifiedSubtotalBound, remainingCapacityBound]
  norm_num

/-- **`remaining_capacity_gt`.**  `KERNEL-PROVED`.  Under the strict subtotal hypothesis
`certifiedSubtotal < 5.250043872e-7`, the remaining capacity exceeds `3.610606128e-7`. -/
theorem remaining_capacity_gt {certifiedSubtotal : ℚ}
    (h : certifiedSubtotal < certifiedSubtotalBound) :
    remainingCapacityBound < ledgerTarget - certifiedSubtotal := by
  rw [← ledger_difference_exact]
  linarith

/-- The audited incremental ledger, as an `IncrementalLedger`: the existing charges are
retained and the single new entry is a medium-only residual. -/
def auditedIncrementalLedger (existing : List ℚ) (residual : ℚ) : IncrementalLedger where
  existing := existing
  residual := residual
  residualSource := ChargeSource.medium
  residualIsMedium := rfl
  total := existing.sum + residual
  total_eq := rfl

/-- **`auditedLedger_retains`.**  `KERNEL-PROVED`.  The audited ledger retains its existing
charges. -/
theorem auditedLedger_retains (existing : List ℚ) (residual : ℚ) :
    (auditedIncrementalLedger existing residual).total - residual = existing.sum :=
  incrementalLedger_retains (auditedIncrementalLedger existing residual)

end Effectivity
end Erdos287
