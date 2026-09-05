import Mathlib
import RequestProject.Erdos287.EulerLocal

/-!
# Erdős #287 effectivity — the two-variable local Euler identity and `Z(s,s) = 0` (§17)

```
TWO-VARIABLE LOCAL EULER IDENTITY : KERNEL-PROVED
FINITE Z(s,s) = 0                 : KERNEL-PROVED
INFINITE Z(s,s) = 0               : BLOCKED BY ANALYTIC CONVERGENCE
```

In the variables `x = p^{-u}`, `y = p^{-v}` the two-variable numerator factorises as

    1 + y/(p−2) − ((p−1)/(p−2))·x  =  (1 − x) + (y − x)/(p−2),

so on the diagonal `u = v` it collapses to `1 − x`.  Consequently the **finite** Euler
difference

    Z_P(u,v) = ∏_{p∈P} [1 + y_p/(p−2) − ((p−1)/(p−2))x_p] − ∏_{p∈P} (1 − x_p)

vanishes identically on the diagonal (`finite_Z_diag_zero`).

The infinite statement is **not** proved: `tprod_diag_congr` below is only a congruence of
formal `tprod`s (equal factors give equal products), and it carries **no** convergence
content.  An honest infinite `Z(s,s) = 0` needs absolute convergence of the Euler product,
which is not available here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-- The two-variable local numerator, in the variables `x = p^{-u}`, `y = p^{-v}`. -/
def eulerNum (p : ℕ) (x y : ℚ) : ℚ := 1 + y / ((p : ℚ) - 2) - (((p : ℚ) - 1) / ((p : ℚ) - 2)) * x

/-- **`eulerNum_split`.**  `KERNEL-PROVED`.  The exact two-variable local identity. -/
theorem eulerNum_split {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (x y : ℚ) :
    eulerNum p x y = (1 - x) + (y - x) / ((p : ℚ) - 2) := by
  have hp2 : ((p : ℚ) - 2) ≠ 0 := sub_two_ne_zero hp h2
  rw [eulerNum]
  field_simp
  ring

/-- **`eulerNum_diag`.**  `KERNEL-PROVED`.  On the diagonal `u = v` the local numerator is
exactly `1 − p^{-u}`. -/
theorem eulerNum_diag {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (x : ℚ) :
    eulerNum p x x = 1 - x := by
  rw [eulerNum_split hp h2]
  simp

/-- The finite Euler difference `Z_P(u,v)`. -/
def ZP (P : Finset ℕ) (x y : ℕ → ℚ) : ℚ :=
  (∏ p ∈ P, eulerNum p (x p) (y p)) - ∏ p ∈ P, (1 - x p)

/-- **`finite_Z_diag_zero`.**  `KERNEL-PROVED`.  `Z_P(s,s) = 0` for every finite set of odd
primes. -/
theorem finite_Z_diag_zero {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (x : ℕ → ℚ) :
    ZP P x x = 0 := by
  rw [ZP, Finset.prod_congr rfl (fun p hp => eulerNum_diag (hP p hp).1 (hP p hp).2 (x p)),
    sub_self]

/-- The `G_p` local factor collapses on the diagonal as well. -/
theorem Gloc_diag {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) {x : ℚ} (hx : x ≠ 1) :
    Gloc p x x = 1 - x / (p : ℚ) := by
  have hx1 : (1 - x) ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have hnum : (1 + x / ((p : ℚ) - 2) - (((p : ℚ) - 1) / ((p : ℚ) - 2)) * x) = 1 - x := by
    have := eulerNum_diag hp h2 x
    rwa [eulerNum] at this
  rw [Gloc, hnum]
  field_simp

/-- **`tprod_diag_congr`.**  A congruence of formal infinite products: equal factors give
equal `tprod`s.  This is **not** an analytic theorem — it asserts nothing about convergence,
and must not be read as an infinite `Z(s,s) = 0`. -/
theorem tprod_diag_congr (S : Set ℕ) (hS : ∀ p ∈ S, Nat.Prime p ∧ p ≠ 2) (x : ℕ → ℚ) :
    (∏' p : S, eulerNum (p : ℕ) (x p) (x p)) = ∏' p : S, (1 - x p) :=
  tprod_congr fun p => eulerNum_diag (hS p p.2).1 (hS p p.2).2 (x p)

end Effectivity
end Erdos287
