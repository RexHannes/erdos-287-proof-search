import Mathlib

/-!
# Erdős #287 — directed rational certificate ledger and subtotal audit

```
CERTIFICATE COMPONENTS (exact rationals) : DEFINED
certifiedSubtotal_correct                : KERNEL-PROVED
PRINTED 5.218873872e-7 CONSISTENT        : NO   (printed_subtotal_is_not_an_upper_bound)
remainingCapacity_correct                : KERNEL-PROVED
PRINTED 3.641776128e-7 CONSISTENT        : NO   (printed_remaining_overstates_capacity)
SAWTOOTH L² MASS  (q²+2)/(12q²)          : KERNEL-PROVED
SAWTOOTH L² MASS ≤ 11/108  (q ≥ 3)       : KERNEL-PROVED
```

## Status of the numerical inputs

The five closed consumers A–E are recorded here as **exact outward rationals** transcribed
from the decimal bounds of the research bank.  No compact machine certificate accompanies
this project, so the *provenance* of each decimal is an
`EXTERNAL MACHINE-CERTIFICATE RESULT`: what is kernel-checked below is the **arithmetic**
performed on them (the subtotal, the remaining capacity, and the comparison with the
printed figures), not the analytic estimates themselves.  Nothing here is asserted as an
axiom.

## Audit outcome

The exact outward sum of A–E is

    5.2188738751e-7   =  52188738751 / 10^17,

which is **strictly larger** than the printed subtotal `5.218873872e-7`; consequently the
printed remaining capacity `3.641776128e-7` is **too large**.  The corrected figures are

    certifiedSubtotal   = 52188738751 / 10^17
    remainingCapacity   = 36417761249 / 10^17  =  3.6417761249e-7.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace DirectedLedger

/-! ## §10  The five certified numerical inputs, as exact rationals -/

/-- A. squarefree gamma, small `k ≤ 31`: `< 1.913023635e-7 · B_X`. -/
def certSmallK : ℚ := 1913023635 / 10 ^ 16

/-- B. joint no-lattice tail (includes no-lattice `p²`, `p³`): `< 1.641148117e-7 · B_X`. -/
def certNoLatticeTail : ℚ := 1641148117 / 10 ^ 16

/-- C. lattice-bearing repeated `p²`: `< 1.663866835e-7 · B_X`. -/
def certRepeatedP2 : ℚ := 1663866835 / 10 ^ 16

/-- D. lattice-bearing repeated `p³`: `< 8.3528e-11 · B_X`. -/
def certRepeatedP3 : ℚ := 83528 / 10 ^ 15

/-- E. nonlinear gamma drift: `< 8.1e-16 · B_X`. -/
def certDrift : ℚ := 81 / 10 ^ 17

/-- The `q = 3` physical directed row, `< 2.17e-8 · B_X`.  It is a **sub-item of A**
(the `k ≤ 31` squarefree gamma total) and is therefore *not* added again to the subtotal. -/
def certQ3Row : ℚ := 217 / 10 ^ 10

theorem certQ3Row_le_certSmallK : certQ3Row ≤ certSmallK := by
  unfold certQ3Row certSmallK; norm_num

/-- The target boundary budget `8.86065e-7`. -/
def target : ℚ := 886065 / 10 ^ 12

/-- The kernel-verified total of the already closed consumers. -/
def certifiedSubtotal : ℚ :=
  certSmallK + certNoLatticeTail + certRepeatedP2 + certRepeatedP3 + certDrift

/-- The remaining capacity available to the two open consumers. -/
def remainingCapacity : ℚ := target - certifiedSubtotal

/-! ## §11  The subtotal audit -/

/-- **`certifiedSubtotal_correct`.** `KERNEL-PROVED`.  The exact rational subtotal. -/
theorem certifiedSubtotal_correct : certifiedSubtotal = 52188738751 / 10 ^ 17 := by
  unfold certifiedSubtotal certSmallK certNoLatticeTail certRepeatedP2 certRepeatedP3 certDrift
  norm_num

/-- The subtotal in decimal form: `5.2188738751e-7`. -/
theorem certifiedSubtotal_decimal : certifiedSubtotal = 5.2188738751 / 10 ^ 7 := by
  rw [certifiedSubtotal_correct]; norm_num

/-- **`printed_subtotal_is_not_an_upper_bound`.** `KERNEL-PROVED`.  The printed research
subtotal `5.218873872e-7` is **strictly smaller** than the exact outward sum of the five
components, so it is not a valid outward subtotal. -/
theorem printed_subtotal_is_not_an_upper_bound :
    (5218873872 : ℚ) / 10 ^ 16 < certifiedSubtotal := by
  rw [certifiedSubtotal_correct]; norm_num

/-- The exact size of the discrepancy: `3.1e-16`. -/
theorem printed_subtotal_gap :
    certifiedSubtotal - (5218873872 : ℚ) / 10 ^ 16 = 31 / 10 ^ 17 := by
  rw [certifiedSubtotal_correct]; norm_num

/-- **`remainingCapacity_correct`.** `KERNEL-PROVED`.  The corrected remaining capacity. -/
theorem remainingCapacity_correct : remainingCapacity = 36417761249 / 10 ^ 17 := by
  unfold remainingCapacity target
  rw [certifiedSubtotal_correct]
  norm_num

/-- The remaining capacity in decimal form: `3.6417761249e-7`. -/
theorem remainingCapacity_decimal : remainingCapacity = 3.6417761249 / 10 ^ 7 := by
  rw [remainingCapacity_correct]; norm_num

/-- **`printed_remaining_overstates_capacity`.** `KERNEL-PROVED`.  The printed remaining
capacity `3.641776128e-7` is **strictly larger** than the true remaining capacity, hence not
usable as a budget. -/
theorem printed_remaining_overstates_capacity :
    remainingCapacity < (3641776128 : ℚ) / 10 ^ 16 := by
  rw [remainingCapacity_correct]; norm_num

/-- A safe (outward, strict) lower bound for the remaining capacity. -/
theorem remainingCapacity_lower_bound : (3641776124 : ℚ) / 10 ^ 16 < remainingCapacity := by
  rw [remainingCapacity_correct]; norm_num

theorem remainingCapacity_pos : 0 < remainingCapacity := by
  rw [remainingCapacity_correct]; norm_num

/-- The subtotal really is below the target. -/
theorem certifiedSubtotal_lt_target : certifiedSubtotal < target := by
  rw [certifiedSubtotal_correct, target]; norm_num

/-! ## §13  Large-sieve input constants -/

/-- Large-sieve input: `∑_b λ(b)/√b < 7/2`.
`EXTERNAL MACHINE-CERTIFICATE INPUT` — an infinite Euler-product bound; no compact
certificate accompanies this project, so it is **recorded, not kernel-checked**. -/
def lambdaSqrtSumBound : ℚ := 7 / 2

/-- Large-sieve input: `∑_q β(q)² < 241/100`.
`EXTERNAL MACHINE-CERTIFICATE INPUT` — recorded, not kernel-checked. -/
def betaSqSumBound : ℚ := 241 / 100

/-- Large-sieve input: the sawtooth DFT `L²` mass bound `11/108`.  Unlike the two constants
above, this one **is** kernel-checked below (`sawtooth_l2_mass_le`). -/
def sawtoothL2MassBound : ℚ := 11 / 108

/-! ### The sawtooth `L²` mass -/

theorem sum_range_cast_id (n : ℕ) :
    (∑ a ∈ Finset.range n, (a : ℚ)) * 2 = (n : ℚ) * ((n : ℚ) - 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      push_cast
      linear_combination ih

theorem sum_range_cast_sq (n : ℕ) :
    (∑ a ∈ Finset.range n, (a : ℚ) ^ 2) * 6 = (n : ℚ) * ((n : ℚ) - 1) * (2 * (n : ℚ) - 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      push_cast
      linear_combination ih

/-- **`sawtooth_sq_mean`.** `KERNEL-PROVED`.  With the strict-endpoint convention
`ψ(a/q) = a/q − 1/2` (so `ψ(0) = −1/2`),

    (1/q) · ∑_{a=0}^{q-1} ψ(a/q)²  =  (q² + 2) / (12 q²).

By finite Parseval this is exactly the `L²` mass `∑_{h mod q} |ψ̂_q(h)|²` of the sawtooth
DFT under the same convention. -/
theorem sawtooth_sq_mean {q : ℕ} (hq : 0 < q) :
    (∑ a ∈ Finset.range q, ((a : ℚ) / q - 1 / 2) ^ 2) / q = ((q : ℚ) ^ 2 + 2) / (12 * q ^ 2) := by
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have h1 := sum_range_cast_id q
  have h2 := sum_range_cast_sq q
  have hexp : ∀ a : ℕ, ((a : ℚ) / q - 1 / 2) ^ 2
      = (a : ℚ) ^ 2 * (1 / q ^ 2) - (a : ℚ) * (1 / q) + 1 / 4 := by
    intro a; field_simp; ring
  rw [Finset.sum_congr rfl (fun a _ => hexp a), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  linear_combination 8 * h2 - 24 * (q : ℚ) * h1

/-- **`sawtooth_l2_mass_le`.** `KERNEL-PROVED`.  For `q ≥ 3` the sawtooth `L²` mass is at
most `11/108`. -/
theorem sawtooth_l2_mass_le {q : ℕ} (hq : 3 ≤ q) :
    ((q : ℚ) ^ 2 + 2) / (12 * q ^ 2) ≤ 11 / 108 := by
  have hq3 : (3 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hqpos : (0 : ℚ) < (q : ℚ) := by linarith
  rw [div_le_iff₀ (by positivity : (0 : ℚ) < 12 * (q : ℚ) ^ 2)]
  nlinarith [hq3, hqpos]

/-- The kernel-checked large-sieve input constant. -/
theorem sawtooth_l2_mass_le_bound {q : ℕ} (hq : 3 ≤ q) :
    ((q : ℚ) ^ 2 + 2) / (12 * q ^ 2) ≤ sawtoothL2MassBound :=
  sawtooth_l2_mass_le hq

end DirectedLedger
end Erdos287
