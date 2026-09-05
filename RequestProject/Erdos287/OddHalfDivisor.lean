import Mathlib
import RequestProject.Erdos287.BsrcWeights
import RequestProject.Erdos287.AllComplement

/-!
# Erdős #287 effectivity — the odd half-divisor chart (§5, §6)

```
ODD HALF-DIVISOR VARIABLE CHANGE : KERNEL-PROVED
H_1^odd(6) = 1                   : KERNEL-PROVED
w = 6 FIREWALL                   : KERNEL-PROVED
```

    H_c^odd(w) = ∑_{d ∣ w, 2 ∤ d, c·d² < w} μ(d).

The exact variable change behind the chart is

    n > c·d   ↔   w = d·n satisfies c·d² < w        (`halfDivisor_variable_change`)

and the **oddness condition `2 ∤ d` cannot be dropped**: at `w = 6` the odd chart
gives `1` while the unrestricted analogue gives `0` (`w6_firewall`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos287
namespace Effectivity

/-! ## §5.1  The chart -/

/-- The odd half-divisor chart `H_c^odd(w) = ∑_{d ∣ w, 2∤d, c d² < w} μ(d)`. -/
def Hodd (c w : ℕ) : ℤ := ∑ d ∈ w.divisors with (¬ 2 ∣ d ∧ c * d ^ 2 < w), moebius d

/-- The **unrestricted** (false) analogue, kept only as a firewall witness. -/
def Hall (c w : ℕ) : ℤ := ∑ d ∈ w.divisors with (c * d ^ 2 < w), moebius d

/-- **`halfDivisor_variable_change`.**  `KERNEL-PROVED`.  The exact variable change
underlying the chart: for `d > 0`, `n > c·d` iff `w = d·n` satisfies `c·d² < w`. -/
theorem halfDivisor_variable_change {c d n : ℕ} (hd : 0 < d) :
    c * d < n ↔ c * d ^ 2 < d * n := by
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-! ## §6  The `w = 6` regression / firewall -/

private lemma divisors_six : (6 : ℕ).divisors = {1, 2, 3, 6} := by decide

/-- **`Hodd_one_six`.**  `KERNEL-PROVED`.  `H_1^odd(6) = 1`. -/
theorem Hodd_one_six : Hodd 1 6 = 1 := by
  rw [Hodd, divisors_six]
  norm_num [Finset.filter_insert, Finset.filter_singleton]

/-- **`Hall_one_six`.**  `KERNEL-PROVED`.  Dropping the oddness restriction gives `0`:
`∑_{d ∣ 6, d² < 6} μ(d) = 0`. -/
theorem Hall_one_six : Hall 1 6 = 0 := by
  rw [Hall, divisors_six]
  norm_num [Finset.filter_insert, Finset.filter_singleton, moebius_apply_prime Nat.prime_two]

/-- **`w6_firewall`.**  `KERNEL-PROVED`.  The oddness condition `2 ∤ d` cannot be dropped
from the half-divisor chart: the two charts already disagree at `w = 6`. -/
theorem w6_firewall : Hodd 1 6 ≠ Hall 1 6 := by
  rw [Hodd_one_six, Hall_one_six]; norm_num

/-! ## §5.2  The odd radical -/

/-- `rad_odd(w) = ∏_{p ∣ w, p > 2} p`. -/
def radOdd (w : ℕ) : ℕ := ∏ p ∈ oddPrimeFactors w, p

lemma radOdd_pos (w : ℕ) : 0 < radOdd w :=
  Finset.prod_pos fun _ hp => (oddPrimeFactors_prime hp).pos

lemma radOdd_odd (w : ℕ) : ¬ (2 ∣ radOdd w) := by
  intro hdvd
  obtain ⟨q, hq, hpq⟩ := (Nat.prime_two.prime).exists_mem_finset_dvd hdvd
  exact oddPrimeFactors_ne_two hq
    (((oddPrimeFactors_prime hq).dvd_iff_eq Nat.prime_two.ne_one).1 hpq)

lemma radOdd_squarefree (w : ℕ) : Squarefree (radOdd w) :=
  squarefree_prod_primes fun _ hp => oddPrimeFactors_prime hp

lemma radOdd_dvd (w : ℕ) : radOdd w ∣ w :=
  dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.erase_subset _ _))
    (Nat.prod_primeFactors_dvd w)

lemma primeFactors_radOdd (w : ℕ) : (radOdd w).primeFactors = oddPrimeFactors w :=
  Nat.primeFactors_prod fun _ hp => oddPrimeFactors_prime hp

/-- An odd squarefree divisor of `w` divides the odd radical of `w`. -/
lemma dvd_radOdd_of_odd_squarefree {w d : ℕ} (hw : w ≠ 0) (hdvd : d ∣ w) (hsq : Squarefree d)
    (hodd : ¬ (2 ∣ d)) : d ∣ radOdd w := by
  have hsub : d.primeFactors ⊆ oddPrimeFactors w := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
    refine mem_oddPrimeFactors.2 ⟨?_, Nat.mem_primeFactors.2 ⟨hprime, hpd.trans hdvd, hw⟩⟩
    rintro rfl
    exact hodd hpd
  calc d = ∏ p ∈ d.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsq).symm
    _ ∣ ∏ p ∈ oddPrimeFactors w, p := Finset.prod_dvd_prod_of_subset _ _ _ hsub
    _ = radOdd w := rfl

/-- Every divisor of the odd radical is odd. -/
lemma odd_of_dvd_radOdd {w d : ℕ} (hd : d ∣ radOdd w) : ¬ (2 ∣ d) :=
  fun h2 => radOdd_odd w (h2.trans hd)

end Effectivity
end Erdos287
