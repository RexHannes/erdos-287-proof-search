import Mathlib

/-!
# RUN1B / d*wp provider — additive characters on a finite cyclic modulus

```
e_r ADDITIVE CHARACTER BASICS      : KERNEL-PROVED
FINITE ORTHOGONALITY               : KERNEL-PROVED
```

This module is **append-only** and project-neutral: it mentions neither the twin-prime
programme nor Erdős #287.  It contains only kernel-proved elementary facts about the
additive character

```
e_r(x) = exp(2 π i x / r),   x : ℤ,  r : ℕ,
```

in the **unnormalised** convention: the orthogonality sum over a full period equals `r`
(not `1`), and no `1/√r` is hidden anywhere.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Run1B
namespace Characters

/-- The additive character `e_r(x) = exp(2 π i x / r)` on `ℤ`, unnormalised. -/
noncomputable def eAdd (r : ℕ) (x : ℤ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) / (r : ℂ))

/-- **`eAdd_zero`.**  `KERNEL-PROVED`. -/
@[simp] theorem eAdd_zero (r : ℕ) : eAdd r 0 = 1 := by
  simp [eAdd]

/-- **`eAdd_add`.**  `KERNEL-PROVED`.  `e_r` is an additive character. -/
theorem eAdd_add (r : ℕ) (x y : ℤ) : eAdd r (x + y) = eAdd r x * eAdd r y := by
  rw [eAdd, eAdd, eAdd, ← Complex.exp_add]
  push_cast
  ring_nf

/-- **`eAdd_ne_zero`.**  `KERNEL-PROVED`. -/
theorem eAdd_ne_zero (r : ℕ) (x : ℤ) : eAdd r x ≠ 0 := Complex.exp_ne_zero _

/-- **`eAdd_eq_one_iff`.**  `KERNEL-PROVED`.  `e_r(x) = 1` exactly on the multiples of `r`. -/
theorem eAdd_eq_one_iff {r : ℕ} (hr : 0 < r) (x : ℤ) : eAdd r x = 1 ↔ (r : ℤ) ∣ x := by
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [eAdd, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hx : (x : ℂ) = (r : ℂ) * (k : ℂ) := by field_simp at hk; exact hk
    exact_mod_cast hx
  · rintro ⟨k, rfl⟩
    exact ⟨k, by push_cast; field_simp⟩

/-- **`eAdd_congr_of_modEq`.**  `KERNEL-PROVED`.  `e_r` depends only on the residue mod `r`. -/
theorem eAdd_congr_of_modEq {r : ℕ} (hr : 0 < r) {x y : ℤ} (h : (r : ℤ) ∣ x - y) :
    eAdd r x = eAdd r y := by
  have h1 : eAdd r (x - y) = 1 := (eAdd_eq_one_iff hr _).2 h
  have h2 : eAdd r ((x - y) + y) = eAdd r (x - y) * eAdd r y := eAdd_add r _ _
  rw [sub_add_cancel, h1, one_mul] at h2
  exact h2

/-- **`eAdd_natMul`.**  `KERNEL-PROVED`.  `e_r(m x) = e_r(x)^m` for `m : ℕ`. -/
theorem eAdd_natMul (r : ℕ) (x : ℤ) (m : ℕ) : eAdd r ((m : ℤ) * x) = eAdd r x ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
      have : ((k : ℤ) + 1) * x = (k : ℤ) * x + x := by ring
      push_cast [this, eAdd_add, ih]
      ring

/-- **`eAdd_period`.**  `KERNEL-PROVED`.  `e_r(x)^r = 1`. -/
theorem eAdd_pow_self {r : ℕ} (hr : 0 < r) (x : ℤ) : eAdd r x ^ r = 1 := by
  rw [← eAdd_natMul r x r]
  exact (eAdd_eq_one_iff hr _).2 ⟨x, rfl⟩

/-- **`eAdd_orthogonality`.**  `KERNEL-PROVED`.  The exact finite orthogonality relation, in
the **unnormalised** convention: the full-period sum is `r`, not `1`. -/
theorem eAdd_orthogonality {r : ℕ} (hr : 0 < r) (a : ℤ) :
    ∑ u ∈ Finset.range r, eAdd r (a * (u : ℤ)) = if (r : ℤ) ∣ a then (r : ℂ) else 0 := by
  have hpow : ∀ u : ℕ, eAdd r (a * (u : ℤ)) = eAdd r a ^ u := by
    intro u
    rw [← eAdd_natMul r a u, mul_comm]
  simp only [hpow]
  by_cases h : (r : ℤ) ∣ a
  · rw [if_pos h, (eAdd_eq_one_iff hr a).2 h]
    simp
  · rw [if_neg h]
    have hne : eAdd r a ≠ 1 := fun hc => h ((eAdd_eq_one_iff hr a).1 hc)
    rw [geom_sum_eq hne, eAdd_pow_self hr a, sub_self, zero_div]

/-- **`eAdd_conj`.**  `KERNEL-PROVED`.  Complex conjugation inverts the character. -/
theorem eAdd_conj (r : ℕ) (x : ℤ) : (starRingEnd ℂ) (eAdd r x) = eAdd r (-x) := by
  rw [eAdd, eAdd, ← Complex.exp_conj]
  congr 1
  have hpi : (starRingEnd ℂ) (Real.pi : ℂ) = (Real.pi : ℂ) := Complex.conj_ofReal _
  have hx : (starRingEnd ℂ) (x : ℂ) = (x : ℂ) := by simp
  have hr : (starRingEnd ℂ) (r : ℂ) = (r : ℂ) := by simp
  simp only [map_div₀, map_mul, hpi, hx, hr, Complex.conj_I, map_ofNat]
  push_cast
  ring

/-- **`eAdd_mul_conj`.**  `KERNEL-PROVED`.  `|e_r(x)| = 1` in the exact algebraic form. -/
theorem eAdd_mul_conj (r : ℕ) (x : ℤ) : eAdd r x * (starRingEnd ℂ) (eAdd r x) = 1 := by
  rw [eAdd_conj, ← eAdd_add]
  simp

/-- **`eAdd_norm_one`.**  `KERNEL-PROVED`. -/
theorem eAdd_norm_one (r : ℕ) (x : ℤ) : ‖eAdd r x‖ = 1 := by
  have h := eAdd_mul_conj r x
  have : ‖eAdd r x * (starRingEnd ℂ) (eAdd r x)‖ = 1 := by rw [h]; simp
  rw [norm_mul, RCLike.norm_conj] at this
  nlinarith [norm_nonneg (eAdd r x), this]

end Characters
end Run1B
