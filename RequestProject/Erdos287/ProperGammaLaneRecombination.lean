import Mathlib
import RequestProject.Erdos287.BsrcWeights

/-!
# Erdős #287 effectivity — the `c = 1 / c = 2` lane recombination (§32)

```
LANE RECOMBINATION      : KERNEL-PROVED
SIGN-TRANSFER FIREWALL  : KERNEL-PROVED
SAME-d CANCELLATION     : NOT ENCODED (explicitly refuted as a source identity)
ERDŐS #287              : OPEN
```

The two γ-entry lanes `c = 1` and `c = 2` are recombined into the single squarefree
`z`-variable `z = c d` (`d` odd).  With the physical parity convention

    σ₁ = +1,   σ₂ = −1,

the exact algebraic recombination law is

    σ_c · μ(d) · B(d) = μ(z) · B(z),      z = c d,  d odd.

**Firewall.**  The lane signs do *not* disappear: they are transferred into `μ(z)`
(`lane_sign_transfer`: `μ(2d) = −μ(d)` for odd `d`).  The formally tempting *same-`d`*
cancellation `μ(d)B(d) + μ(2d)B(2d) = 0` is **not** a legal source simplification, because the
two γ-entry ranges are disjoint: a range that admits only one of `z = d`, `z = 2d` has a
nonzero contribution (`lane_range_restricted_no_cancellation`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ArithmeticFunction

namespace Erdos287
namespace Effectivity

/-! ## §32.1  The lane sign -/

/-- The physical lane sign: `σ₁ = +1`, `σ₂ = −1` (and `0` off the two lanes). -/
def laneSign : ℕ → ℚ
  | 1 => 1
  | 2 => -1
  | _ => 0

@[simp] theorem laneSign_one : laneSign 1 = 1 := rfl

@[simp] theorem laneSign_two : laneSign 2 = -1 := rfl

/-- `2` is coprime to every odd number. -/
theorem coprime_two_of_odd {d : ℕ} (hodd : ¬ 2 ∣ d) : Nat.Coprime 2 d :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd

/-! ## §32.2  The two local transfer facts -/

/-- **`B0_two_mul`.**  `KERNEL-PROVED`.  `B0` ignores the prime `2`. -/
theorem B0_two_mul {d : ℕ} (hd : d ≠ 0) : B0 (2 * d) = B0 d := by
  rw [B0, B0, oddPrimeFactors_mul (by norm_num) hd]
  have h2 : oddPrimeFactors 2 = ∅ := by
    rw [oddPrimeFactors, Nat.Prime.primeFactors Nat.prime_two]; decide
  rw [h2, Finset.empty_union]

/-- **`lane_sign_transfer`.**  `KERNEL-PROVED`.  The `c = 2` lane sign is exactly the Möbius
sign: `μ(2d) = −μ(d)` for odd `d`. -/
theorem lane_sign_transfer {d : ℕ} (hodd : ¬ 2 ∣ d) :
    ((moebius (2 * d) : ℤ) : ℚ) = - ((moebius d : ℤ) : ℚ) := by
  have hcop : Nat.Coprime 2 d := coprime_two_of_odd hodd
  have h := isMultiplicative_moebius.map_mul_of_coprime hcop
  have h2 : (moebius 2 : ℤ) = -1 := by
    simpa using ArithmeticFunction.moebius_apply_prime Nat.prime_two
  rw [h, h2]
  push_cast
  ring

/-! ## §32.3  The recombination law -/

/-- **`lane_recombination`.**  `KERNEL-PROVED`.  For `d` odd and `c ∈ {1,2}`, with `z = c d`:

    σ_c · μ(d) · B(d) = μ(z) · B(z). -/
theorem lane_recombination (B1 : ℚ) {c d : ℕ} (hc : c = 1 ∨ c = 2) (hd : d ≠ 0)
    (hodd : ¬ 2 ∣ d) :
    laneSign c * ((moebius d : ℤ) : ℚ) * B B1 d
      = ((moebius (c * d) : ℤ) : ℚ) * B B1 (c * d) := by
  rcases hc with rfl | rfl
  · simp
  · rw [lane_sign_transfer hodd, B, B, B0_two_mul hd, laneSign_two]
    ring

/-- **`lane_recombination_z`.**  `KERNEL-PROVED`.  The same law stated through the recombined
squarefree variable `z`. -/
theorem lane_recombination_z (B1 : ℚ) {c d z : ℕ} (hc : c = 1 ∨ c = 2) (hd : d ≠ 0)
    (hodd : ¬ 2 ∣ d) (hz : z = c * d) :
    laneSign c * ((moebius d : ℤ) : ℚ) * B B1 d = ((moebius z : ℤ) : ℚ) * B B1 z := by
  subst hz; exact lane_recombination B1 hc hd hodd

/-- **`lane_z_distinct`.**  `KERNEL-PROVED`.  The two lanes produce *distinct* `z`-values. -/
theorem lane_z_distinct {d : ℕ} (hd : d ≠ 0) : (1 : ℕ) * d ≠ 2 * d := by
  intro h; omega

/-! ## §32.4  The no-false-cancellation firewall -/

/-- The `z`-source term at a single `z`, restricted to a γ-entry range `R`. -/
def laneTerm (B1 : ℚ) (R : ℕ → Prop) [DecidablePred R] (z : ℕ) : ℚ :=
  if R z then ((moebius z : ℤ) : ℚ) * B B1 z else 0

/-- **`lane_range_restricted_no_cancellation`.**  `KERNEL-PROVED`.  The *same-`d`* odd-lattice
cancellation is **not** a source identity: for the disjoint γ-entry ranges, a range admitting
`z = d` but not `z = 2d` leaves a nonzero contribution.  (Witness `d = 3`, `B1 = 1`.) -/
theorem lane_range_restricted_no_cancellation :
    laneTerm 1 (fun z => z = 3) 3 + laneTerm 1 (fun z => z = 3) 6 ≠ 0 := by
  have hmu : (moebius 3 : ℤ) = -1 := by
    simpa using ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3)
  have hB : B (1 : ℚ) 3 = 2 := by
    rw [B, B0_prime (by norm_num) (by norm_num)]; norm_num
  simp only [laneTerm, show ¬ (6 = 3) from by norm_num, hB, hmu]
  norm_num

/-- **`lane_signs_survive`.**  `KERNEL-PROVED`.  The recombination does not destroy sign
information: the recombined weight at `z = 2d` is the negative of the one at `z = d`
(for odd squarefree `d ≠ 0`), so the signs live in `μ(z)`. -/
theorem lane_signs_survive (B1 : ℚ) {d : ℕ} (hd : d ≠ 0) (hodd : ¬ 2 ∣ d) :
    ((moebius (2 * d) : ℤ) : ℚ) * B B1 (2 * d) = - (((moebius d : ℤ) : ℚ) * B B1 d) := by
  rw [lane_sign_transfer hodd, B, B, B0_two_mul hd]
  ring

end Effectivity
end Erdos287
