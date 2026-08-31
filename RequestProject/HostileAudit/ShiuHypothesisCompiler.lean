import Mathlib
import RequestProject.HostileAudit.ShortTResidueGeometry

/-!
# Hostile-audit safe bank §9 — the Shiu hypothesis compiler

Only the **source / rational hypothesis map** of the Shiu divisor-average application is
formalised:

```
modulus exponent          = 5/7,
admissible upper exponent = 3/4,
3/4 − 5/7                 = 1/28  (the margin).
```

together with the coprimality bookkeeping `gcd(±1, 2w') = 1` for the shift, and the transport
of the rational inequality to the physical scales (`shiu_modulus_within_admissible_range`).

Shiu's theorem itself is **not** formalised and **not** axiomatised: the divisor-average
estimate remains the banked uninhabited interface
`Erdos287.CurrentProgramme.BalancedSevenShiuInput`, and the consumer below is conditional
on it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace HostileAudit

open Erdos287.CurrentProgramme

/-! ## §9.1  The rational hypothesis map -/

/-- The modulus exponent of the Balanced7 Shiu application: `q = X^{5/7}`. -/
def shiuModulusExponent : ℚ := 5 / 7

/-- The admissible upper exponent in Shiu's theorem: `X^{3/4}`. -/
def shiuAdmissibleExponent : ℚ := 3 / 4

/-- **`shiu_exponent_margin`.**  `LEAN_PROVED` (rational arithmetic).

`3/4 − 5/7 = 1/28 > 0`: the Balanced7 modulus is admissible with margin `1/28`. -/
theorem shiu_exponent_margin :
    shiuAdmissibleExponent - shiuModulusExponent = 1 / 28 ∧
      shiuModulusExponent < shiuAdmissibleExponent := by
  unfold shiuAdmissibleExponent shiuModulusExponent
  norm_num

/-- **`shiu_modulus_within_admissible_range`.**  `LEAN_PROVED`.

The rational margin transported to the physical scales: for `X ≥ 1`,
`X^{5/7} ≤ X^{3/4}`. -/
theorem shiu_modulus_within_admissible_range {X : ℝ} (hX : 1 ≤ X) :
    X ^ ((5 : ℝ) / 7) ≤ X ^ ((3 : ℝ) / 4) :=
  Real.rpow_le_rpow_of_exponent_le hX (by norm_num)

/-- **`shiu_margin_is_strict`.**  `LEAN_PROVED`.

For `X > 1` the admissibility is strict, so the application is not on the boundary. -/
theorem shiu_margin_is_strict {X : ℝ} (hX : 1 < X) :
    X ^ ((5 : ℝ) / 7) < X ^ ((3 : ℝ) / 4) :=
  Real.rpow_lt_rpow_of_exponent_lt hX (by norm_num)

/-! ## §9.2  The shift coprimality `gcd(±1, 2w') = 1` -/

/-- **`shiu_shift_coprime`.**  `LEAN_PROVED`.

Both admissible shifts `s = ±1` are coprime to the modulus `2w'`, for every `w'`. -/
theorem shiu_shift_coprime (w' : ℕ) :
    Int.gcd 1 (2 * (w' : ℤ)) = 1 ∧ Int.gcd (-1) (2 * (w' : ℤ)) = 1 := by
  constructor
  · simp [Int.gcd]
  · simp [Int.gcd]

/-- **`shiu_shift_coprime_nat`.**  `LEAN_PROVED`.  The natural-number form used by the
banked socket: `gcd(2w', 1) = 1`. -/
theorem shiu_shift_coprime_nat (w' : ℕ) : Nat.Coprime (2 * w') 1 :=
  Nat.coprime_one_right _

/-! ## §9.3  The conditional consumer -/

/-- The exact divisor-average target of the Shiu application. -/
def ShiuDivisorAverageTarget (Wprime s : ℕ) (Mbox : Finset ℕ) (Mlen : ℕ) (Cshiu : ℝ) : Prop :=
  (∑ m ∈ Mbox, ((affineSeq Wprime s m).divisors.card : ℝ))
    ≤ Cshiu * (Mlen : ℝ) * Real.log (Mlen : ℝ)

/-- **`shiu_target_of_input`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

From the uninhabited Shiu interface to the exact divisor-average target.  Nothing analytic is
proved: this is the consumer, and the interface is the obligation. -/
theorem shiu_target_of_input {Wprime s : ℕ} {Mbox : Finset ℕ} {Mlen : ℕ} {Cshiu : ℝ}
    (h : BalancedSevenShiuInput Wprime s Mbox Mlen Cshiu) :
    ShiuDivisorAverageTarget Wprime s Mbox Mlen Cshiu :=
  h.divisor_average

/-- **`shiu_input_still_uninhabited`.**  `LEAN_PROVED`.

Shiu's theorem is not an axiom of this repository and not a Lean theorem: the interface has
no inhabitant. -/
theorem shiu_input_still_uninhabited :
    ∃ (Wprime s : ℕ) (Mbox : Finset ℕ) (Mlen : ℕ) (Cshiu : ℝ),
      ¬ BalancedSevenShiuInput Wprime s Mbox Mlen Cshiu :=
  shiu_not_automatic

end HostileAudit
end Erdos287
