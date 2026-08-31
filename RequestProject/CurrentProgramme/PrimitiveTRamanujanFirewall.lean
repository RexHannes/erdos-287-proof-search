import Mathlib
import RequestProject.CurrentProgramme.PrimitiveRamanujanAlgebra

/-!
# Complete primitive-`t` Ramanujan firewall — Erdős #287, ONE-LEVEL MÖBIUS Δ, §12

**Exact finite algebra only.**

For the repository's own Ramanujan sum `c_g(N)` (built from the additive phase `e(x)`), we bank
the two local identities at a prime `p`:

* `ramanujan_prime_not_dvd` — `p ∤ N ⟹ c_p(N) = -1`, hence `μ(p)c_p(N) = 1`;
* `ramanujan_prime_dvd` — `p ∣ N ⟹ c_p(N) = p - 1`, hence `μ(p)c_p(N) = -(p-1)`;
* `moebius_mul_ramanujan_prime` — the two signed forms together.

Together with the banked exact divisor normal form of `μ(m)/m · c_m(N)` (re-exported as
`moebius_ramanujan_normalForm_reexport`) this shows *algebraically* that complete primitive-`t`
reassembly neutralises the remaining Möbius sign at generic primes: at every prime not dividing
`N` the signed local factor is exactly `+1`.

**Firewall.**  The analytic infinite Euler-product claim `ζ(1+w)/ζ(2+2w)` is **not** formalised
anywhere; the repository's analytic library does not support it.

Research status (metadata only, no Lean content):
`ONELEVEL-RAMANUJAN-ZEROFREE45 : REPRESENTATION LOOP / NONCLOSING.`
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset ArithmeticFunction
open scoped BigOperators

namespace Erdos287
namespace PrimitiveTFirewall

open Erdos287.PrimitiveRamanujan

/-- For a prime `p` not dividing `N`, `gcd(p,N) = 1`. -/
theorem int_gcd_prime_eq_one {p : ℕ} (hp : p.Prime) {N : ℤ} (hpN : ¬ (p : ℤ) ∣ N) :
    Int.gcd (p : ℤ) N = 1 := by
  have h : ¬ p ∣ N.natAbs := by
    intro h
    exact hpN ((Int.natAbs_dvd_natAbs (a := (p : ℤ)) (b := N)).1 (by simpa using h))
  simpa [Int.gcd] using (Nat.Prime.coprime_iff_not_dvd hp).2 h

/-- **`c_p(N) = -1` for `p ∤ N`.**  `LEAN_PROVED`. -/
theorem ramanujan_prime_not_dvd {p : ℕ} (hp : p.Prime) {N : ℤ} (hpN : ¬ (p : ℤ) ∣ N) :
    ramanujan p N = -1 := by
  rw [ramanujan_eq_divisor_sum p hp.pos N, int_gcd_prime_eq_one hp hpN]
  simp [moebius_apply_prime hp]

/-- **`c_p(N) = p - 1` for `p ∣ N`.**  `LEAN_PROVED`. -/
theorem ramanujan_prime_dvd {p : ℕ} (hp : p.Prime) {N : ℤ} (hpN : (p : ℤ) ∣ N) :
    ramanujan p N = (p : ℂ) - 1 := by
  have hgcd : Int.gcd (p : ℤ) N = p := by
    have h : p ∣ N.natAbs := (Int.natAbs_dvd_natAbs (a := (p : ℤ)) (b := N)).2 hpN
    simpa [Int.gcd] using Nat.gcd_eq_left h
  rw [ramanujan_eq_divisor_sum p hp.pos N, hgcd, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  simp [Nat.div_self hp.pos, moebius_apply_prime hp]
  ring

/-- **Signed local factors.**  `LEAN_PROVED`.

`μ(p)c_p(N) = 1` at primes `p ∤ N`, and `μ(p)c_p(N) = -(p-1)` at primes `p ∣ N`. -/
theorem moebius_mul_ramanujan_prime {p : ℕ} (hp : p.Prime) (N : ℤ) :
    (¬ (p : ℤ) ∣ N → ((moebius p : ℤ) : ℂ) * ramanujan p N = 1) ∧
      ((p : ℤ) ∣ N → ((moebius p : ℤ) : ℂ) * ramanujan p N = -((p : ℂ) - 1)) := by
  have hmu : ((moebius p : ℤ) : ℂ) = -1 := by
    rw [moebius_apply_prime hp]
    norm_num
  constructor
  · intro h
    rw [ramanujan_prime_not_dvd hp h, hmu]
    ring
  · intro h
    rw [ramanujan_prime_dvd hp h, hmu]
    ring

/-- Re-export of the banked exact divisor normal form of `μ(m)/m · c_m(N)`; nothing is
re-proved here. -/
theorem moebius_ramanujan_normalForm_reexport {g : ℕ} (hg : 0 < g) (hsq : Squarefree g) (N : ℤ) :
    ((moebius g : ℤ) : ℂ) / (g : ℂ) * ramanujan g N
      = ∑ r ∈ (Int.gcd (g : ℤ) N).divisors, ((moebius r : ℤ) : ℂ) / ((g / r : ℕ) : ℂ) :=
  ramanujan_moebius_normalForm hg hsq N

end PrimitiveTFirewall
end Erdos287
