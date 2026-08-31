import Mathlib
import RequestProject.CurrentProgramme.ShortTShiuSockets

/-!
# Hostile-audit safe bank §8 — short-`t` sieve finite residue geometry

The finite geometry underlying the short-`t` upper sieve, proved exactly.  For

```
w = w' + q·t
```

and a sieve prime `ℓ < z`:

* if `ℓ ∤ q`, there is **exactly one** forbidden residue class,
  `t ≡ −w'·q⁻¹ (mod ℓ)`  (`shortT_unique_forbidden_class`);
* if `ℓ ∣ q`, the progression is constant mod `ℓ`: `w' + q·t ≡ w' (mod ℓ)`
  (`shortT_constant_class_of_dvd`), so `ℓ` sieves either everything or nothing.

Together with the physical scale ledger

```
z ≤ X^{2/105},   Y = X^{1/7} = X^{15/105},   2/105 < 15/105,
```

no sieve prime `ℓ < z` can divide a product `w'` all of whose prime factors sit in the
`Y`-scale prime boxes (`smallPrime_not_dividing_YscaleProduct`).

The Selberg upper-sieve estimate itself is **not** proved: it remains the banked uninhabited
interface `Erdos287.CurrentProgramme.BalancedSevenShortTSieveInput`
(`shortTSieve_still_uninhabited`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace HostileAudit

open Erdos287.CurrentProgramme

/-! ## §8.1  The residue geometry of `w = w' + q t` -/

/-- **`shortT_unique_forbidden_class`.**  `LEAN_PROVED`.

If the sieve prime `ℓ` does not divide the modulus `q`, then exactly one residue class of
`t` modulo `ℓ` is forbidden, namely `t ≡ −w'·q⁻¹`. -/
theorem shortT_unique_forbidden_class {ell q w' : ℕ} (hp : ell.Prime) (hq : ¬ (ell ∣ q)) :
    ∃! t : ZMod ell, (w' : ZMod ell) + (q : ZMod ell) * t = 0 := by
  haveI : Fact ell.Prime := ⟨hp⟩
  have hq0 : (q : ZMod ell) ≠ 0 := fun h => hq ((ZMod.natCast_eq_zero_iff q ell).1 h)
  refine ⟨-(w' : ZMod ell) / (q : ZMod ell), ?_, ?_⟩
  · show (w' : ZMod ell) + (q : ZMod ell) * (-(w' : ZMod ell) / (q : ZMod ell)) = 0
    rw [mul_div_cancel₀ _ hq0]
    ring
  · intro y hy
    rw [eq_div_iff hq0]
    linear_combination hy

/-- **`shortT_forbidden_class_formula`.**  `LEAN_PROVED`.

The forbidden class is literally `t = −w'·q⁻¹`. -/
theorem shortT_forbidden_class_formula {ell q w' : ℕ} [Fact ell.Prime] (hq : ¬ (ell ∣ q)) :
    (w' : ZMod ell) + (q : ZMod ell) * (-(w' : ZMod ell) / (q : ZMod ell)) = 0 := by
  have hq0 : (q : ZMod ell) ≠ 0 := fun h => hq ((ZMod.natCast_eq_zero_iff q ell).1 h)
  rw [mul_div_cancel₀ _ hq0]
  ring

/-- **`shortT_constant_class_of_dvd`.**  `LEAN_PROVED`.

If `ℓ ∣ q` then the progression is constant modulo `ℓ`: `w' + q·t ≡ w' (mod ℓ)`. -/
theorem shortT_constant_class_of_dvd {ell q : ℕ} (hq : ell ∣ q) (w' t : ℕ) :
    ((w' + q * t : ℕ) : ZMod ell) = (w' : ZMod ell) := by
  have hq0 : (q : ZMod ell) = 0 := (ZMod.natCast_eq_zero_iff q ell).2 hq
  push_cast
  rw [hq0, zero_mul, add_zero]

/-- **`shortT_dvd_case_is_all_or_nothing`.**  `LEAN_PROVED`.

Consequently, when `ℓ ∣ q` the sieve condition at `ℓ` does not depend on `t` at all. -/
theorem shortT_dvd_case_is_all_or_nothing {ell q : ℕ} (hq : ell ∣ q) (w' : ℕ) :
    ∀ t₁ t₂ : ℕ, ((w' + q * t₁ : ℕ) : ZMod ell) = ((w' + q * t₂ : ℕ) : ZMod ell) := by
  intro t₁ t₂
  rw [shortT_constant_class_of_dvd hq, shortT_constant_class_of_dvd hq]

/-! ## §8.2  The physical scale ledger -/

/-- The short-`t` sieve level exponent `z = X^{2/105}`. -/
def shortTSieveExponent : ℚ := 2 / 105

/-- The prime-box scale exponent `Y = X^{1/7} = X^{15/105}`. -/
def primeBoxScaleExponent : ℚ := 1 / 7

/-- **`shortT_scale_ledger`.**  `LEAN_PROVED` (rational arithmetic).

`1/7 = 15/105` and `2/105 < 15/105`: the sieve scale is far below the prime-box scale. -/
theorem shortT_scale_ledger :
    primeBoxScaleExponent = 15 / 105 ∧
      shortTSieveExponent = 2 / 105 ∧
      shortTSieveExponent < primeBoxScaleExponent := by
  unfold shortTSieveExponent primeBoxScaleExponent
  norm_num

/-- **`shortT_scale_separation_real`.**  `LEAN_PROVED`.

The rational separation transported to the physical scales: for `X ≥ 1`,
`X^{2/105} ≤ X^{1/7}`. -/
theorem shortT_scale_separation_real {X : ℝ} (hX : 1 ≤ X) :
    X ^ ((2 : ℝ) / 105) ≤ X ^ ((1 : ℝ) / 7) :=
  Real.rpow_le_rpow_of_exponent_le hX (by norm_num)

/-! ## §8.3  Sieve primes miss the `Y`-scale boxes -/

/-- **`smallPrime_not_dividing_YscaleProduct`.**  `LEAN_PROVED`.

A sieve prime `ℓ < z ≤ Y` cannot divide an integer `w' > 0` all of whose prime factors are at
least the box scale `Y`.  (The threshold assumptions are explicit: this is the exact finite
content of "the sieve primes are disjoint from the prime boxes".) -/
theorem smallPrime_not_dividing_YscaleProduct {w' ell : ℕ} {Yr zr : ℝ}
    (hw : 0 < w') (hell : ell.Prime) (hlt : (ell : ℝ) < zr) (hz : zr ≤ Yr)
    (hfac : ∀ p ∈ w'.primeFactors, Yr ≤ (p : ℝ)) : ¬ ell ∣ w' := by
  intro hdvd
  have hmem : ell ∈ w'.primeFactors := Nat.mem_primeFactors.2 ⟨hell, hdvd, hw.ne'⟩
  have h1 : Yr ≤ (ell : ℝ) := hfac ell hmem
  linarith

/-- **`shortT_sieve_primes_disjoint_from_boxes`.**  `LEAN_PROVED`.

The physical instance of the previous lemma at the banked exponents: with `z = X^{2/105}`
and box scale `Y = X^{1/7}`, no sieve prime divides a `Y`-scale product. -/
theorem shortT_sieve_primes_disjoint_from_boxes {X : ℝ} (hX : 1 ≤ X) {w' ell : ℕ}
    (hw : 0 < w') (hell : ell.Prime) (hlt : (ell : ℝ) < X ^ ((2 : ℝ) / 105))
    (hfac : ∀ p ∈ w'.primeFactors, X ^ ((1 : ℝ) / 7) ≤ (p : ℝ)) : ¬ ell ∣ w' :=
  smallPrime_not_dividing_YscaleProduct hw hell hlt (shortT_scale_separation_real hX) hfac

/-! ## §8.4  The analytic sieve estimate stays external -/

/-- **`shortTSieve_still_uninhabited`.**  `LEAN_PROVED`.

The Selberg upper-sieve estimate is **not** proved by the finite geometry above: the banked
socket `BalancedSevenShortTSieveInput` remains uninhabited. -/
theorem shortTSieve_still_uninhabited :
    ∃ X theta C R : ℝ, ¬ BalancedSevenShortTSieveInput X theta C R :=
  shortTSieve_not_automatic

end HostileAudit
end Erdos287
