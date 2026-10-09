import Mathlib
import RequestProject.Erdos287.EdgeCutoffLedger
import RequestProject.Erdos287.ProperGammaShellSix

/-!
# Erdős #287 effectivity — the proper-γ ownership ledger and the parent/child firewall (§40)

```
OWNERSHIP ARITHMETIC              : KERNEL-PROVED (exact rationals)
CHILD REMAINING 3.7976032e-10     : KERNEL-PROVED ARITHMETIC
PARENT AVAILABLE 8.14976032e-9    : KERNEL-PROVED ARITHMETIC
PARENT/CHILD DOUBLE-CHARGE LAW    : KERNEL-PROVED
NUMERICAL OWNER VALUES            : CERTIFICATE-BACKED INPUTS
GLOBAL LEDGER                     : UNCHANGED PENDING RECONCILIATION
ERDŐS #287                        : OPEN
```

Directed proper-γ owners (all values are *certificate-backed inputs*; only the arithmetic
below is kernel content):

    q ≤ 200 : 1.83e-8,   N = 1 : 2.4e-8,   N = 2..5 : 2.16e-8,   N = 6 : 7.77e-9,

with exact allocated total `7.167e-8`, exact proper-γ target `7.204976032e-8`, hence exact
child remaining capacity `3.7976032e-10`.

Two continuation charts are legal:

* **child chart** — `N = 6` charged separately, survivor `N ≥ 7`, remaining `3.7976032e-10`;
* **parent chart** — `N = 6` not charged, survivor `N ≥ 6`, available `8.14976032e-9`.

Both are legal *separately*; charging shell `6` **and** using the parent allowance
simultaneously overspends the target (`shell6_double_charge_illegal`).

The global ledger of §26/§30 (`certifiedSubtotalV1000`, `remainingCapacityV1000`) is
**not** altered here: the new internal owners are not yet reconciled against the older global
owners (`global_ledger_unchanged`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace Effectivity

/-! ## §40.1  The directed proper-γ owners -/

/-- Owner: the `q ≤ 200` numerical closure, `1.83e-8`. -/
def ownerQ200 : ℚ := 183 / 10 ^ 10

/-- Owner: the `N = 1` numerical closure, `2.4e-8`. -/
def ownerN1 : ℚ := 24 / 10 ^ 9

/-- Owner: the `N = 2..5` numerical closure, `2.16e-8`. -/
def ownerN2to5 : ℚ := 216 / 10 ^ 10

/-- Owner: the `N = 6` numerical closure, `7.77e-9`. -/
def ownerN6 : ℚ := 777 / 10 ^ 11

/-- The exact allocated total of the four banked owners: `7.167e-8`. -/
def allocatedTotal : ℚ := 7167 / 10 ^ 11

/-- The exact proper-γ target: `7.204976032e-8`. -/
def properGammaTarget : ℚ := 7204976032 / 10 ^ 17

/-- The exact child remaining capacity: `3.7976032e-10`. -/
def childRemaining : ℚ := 37976032 / 10 ^ 17

/-- The exact parent (`N ≥ 6`) available allocation: `8.14976032e-9`. -/
def parentAvailable : ℚ := 814976032 / 10 ^ 17

/-- **`allocatedTotal_eq`.**  `KERNEL-PROVED`.  The four owners sum exactly to `7.167e-8`. -/
theorem allocatedTotal_eq : ownerQ200 + ownerN1 + ownerN2to5 + ownerN6 = allocatedTotal := by
  unfold ownerQ200 ownerN1 ownerN2to5 ownerN6 allocatedTotal; norm_num

/-- **`childRemaining_eq`.**  `KERNEL-PROVED ARITHMETIC`.  `7.204976032e-8 − 7.167e-8 =
3.7976032e-10`. -/
theorem childRemaining_eq : properGammaTarget - allocatedTotal = childRemaining := by
  unfold properGammaTarget allocatedTotal childRemaining; norm_num

/-- **`parentAvailable_eq`.**  `KERNEL-PROVED ARITHMETIC`.  Not charging shell `6` leaves
exactly `8.14976032e-9`. -/
theorem parentAvailable_eq :
    properGammaTarget - (ownerQ200 + ownerN1 + ownerN2to5) = parentAvailable := by
  unfold properGammaTarget ownerQ200 ownerN1 ownerN2to5 parentAvailable; norm_num

/-- **`shell6_parent_recombine_legal`.**  `KERNEL-PROVED`.  The parent allowance is exactly
the child remaining capacity *plus* the shell-6 charge: recombining is legal. -/
theorem shell6_parent_recombine_legal : parentAvailable = childRemaining + ownerN6 := by
  unfold parentAvailable childRemaining ownerN6; norm_num

/-! ## §40.2  The two legal charts -/

/-- The two legal continuation charts. -/
inductive MultiplicityChart
  | child
  | parent
  deriving DecidableEq, Repr

/-- Is the shell `N = 6` charged separately in this chart? -/
def chargesShellSix : MultiplicityChart → Bool
  | .child => true
  | .parent => false

/-- The least multiplicity of the surviving region of a chart. -/
def survivorFloor : MultiplicityChart → ℕ
  | .child => 7
  | .parent => 6

/-- The total charge of a chart's banked owners. -/
def chartAllocated : MultiplicityChart → ℚ
  | .child => ownerQ200 + ownerN1 + ownerN2to5 + ownerN6
  | .parent => ownerQ200 + ownerN1 + ownerN2to5

/-- The remaining capacity of a chart. -/
def chartRemaining (c : MultiplicityChart) : ℚ := properGammaTarget - chartAllocated c

/-- **`chart_remaining_values`.**  `KERNEL-PROVED ARITHMETIC`.  The two chart capacities. -/
theorem chart_remaining_values :
    chartRemaining .child = childRemaining ∧ chartRemaining .parent = parentAvailable := by
  constructor
  · rw [chartRemaining, chartAllocated, allocatedTotal_eq, childRemaining_eq]
  · rw [chartRemaining, chartAllocated, parentAvailable_eq]

/-- **`chart_budget_exact`.**  `KERNEL-PROVED`.  Each chart's allocation plus its remaining
capacity is exactly the proper-γ target: neither chart overspends. -/
theorem chart_budget_exact (c : MultiplicityChart) :
    chartAllocated c + chartRemaining c = properGammaTarget := by
  rw [chartRemaining]; ring

/-- **`parent_child_owner_disjoint`.**  `KERNEL-PROVED`.  In each chart the surviving region
is disjoint from the separately charged owners: the child charges shell `6` and survives from
`7`, the parent does not charge shell `6` and survives from `6`. -/
theorem parent_child_owner_disjoint (c : MultiplicityChart) :
    (chargesShellSix c = true → 6 < survivorFloor c) ∧
      (chargesShellSix c = false → survivorFloor c ≤ 6) := by
  cases c <;> exact ⟨by decide, by decide⟩

/-- The (illegal) total obtained by using the parent allowance *and* charging shell `6`. -/
def doubleChargedTotal : ℚ := chartAllocated .parent + ownerN6 + parentAvailable

/-- **`shell6_double_charge_illegal`.**  `KERNEL-PROVED`.  Using the parent `N ≥ 6` allowance
while also charging shell `N = 6` strictly overspends the proper-γ target — whereas each chart
separately closes it exactly. -/
theorem shell6_double_charge_illegal :
    properGammaTarget < doubleChargedTotal ∧
      chartAllocated .child + chartRemaining .child = properGammaTarget ∧
      chartAllocated .parent + chartRemaining .parent = properGammaTarget := by
  refine ⟨?_, chart_budget_exact _, chart_budget_exact _⟩
  unfold doubleChargedTotal chartAllocated ownerQ200 ownerN1 ownerN2to5 ownerN6
    parentAvailable properGammaTarget
  norm_num

/-- **`chart_choice_exclusive`.**  `KERNEL-PROVED`.  The bookkeeping law: a legal continuation
picks exactly one chart; the two charts differ precisely in the shell-6 charge. -/
theorem chart_choice_exclusive :
    chargesShellSix .child ≠ chargesShellSix .parent ∧
      chartAllocated .child - chartAllocated .parent = ownerN6 := by
  refine ⟨by decide, ?_⟩
  rw [chartAllocated, chartAllocated]; ring

/-! ## §40.3  The owner numerical values are certificate-backed inputs -/

/-- **`owner_values_exact`.**  `KERNEL-PROVED`.  Only the exact rational values are kernel
content; the analytic closures behind them are certificate-backed. -/
theorem owner_values_exact :
    ownerQ200 = 183 / 10 ^ 10 ∧ ownerN1 = 24 / 10 ^ 9 ∧ ownerN2to5 = 216 / 10 ^ 10 ∧
      ownerN6 = 777 / 10 ^ 11 := ⟨rfl, rfl, rfl, rfl⟩

/-- **`ownerN6_is_shellSixCharge`.**  `KERNEL-PROVED`.  The ledger's `N = 6` owner is exactly
the certificate-backed shell-6 charge of §34. -/
theorem ownerN6_is_shellSixCharge : ownerN6 = shellSixCharge := rfl

/-! ## §40.4  The global ledger firewall -/

/-- **`global_ledger_unchanged`.**  `KERNEL-PROVED`.  The global certified subtotal and the
global remaining capacity of §26/§30 are **unchanged** by this proper-γ internal
reallocation: the new owners are not yet reconciled against the older global owners. -/
theorem global_ledger_unchanged :
    certifiedSubtotalV1000 = 5257263872 / 10 ^ 16 ∧
      remainingCapacityV1000 = 3603386128 / 10 ^ 16 ∧
      ledgerTarget - certifiedSubtotalV1000 = remainingCapacityV1000 :=
  ⟨rfl, rfl, ledger_difference_exact_v1000⟩

/-- **`properGamma_internal_only`.**  `KERNEL-PROVED`.  The proper-γ target is an *internal*
budget: it is strictly smaller than the global remaining capacity, so the internal
reallocation cannot by itself close the global ledger. -/
theorem properGamma_internal_only : properGammaTarget < remainingCapacityV1000 := by
  unfold properGammaTarget remainingCapacityV1000; norm_num

end Effectivity
end Erdos287
