import Mathlib
import RequestProject.CurrentProgramme.Erdos287CommonXArithmetic

/-!
# Fractional-linear opposite-row algebra (C0 branch) — Erdős #287

Append-only module, strictly after `Erdos287CommonXArithmetic`.

All statements here are *pure commutative-ring / `ZMod x` algebra*.  The analytic origin of
`A0`, `C0`, `N` plays no role and is deliberately **not** part of any hypothesis; the results are
therefore reusable.

Contents.

* §1  `fractionalLinear_to_linear`, `oppositeRow_linearized` — the source identity
  `(A0 - d C0 h') h = C0 h' b` together with `N = b + d h` linearises to
  `d C0 N h' = A0 (N - b)`.
* §2  `oppositeRow_unique_residue` — uniqueness of `h'` modulo `x` once `d C0 N` is a unit.
* §3  `kappa_fractionalLinear_of_source`, `denominator_ne_zero_of_unit` — the fractional-linear
  representation `kappa = A0 (A0 - d C0 h')⁻¹`.  Cancellation by `b` genuinely needs `IsUnit b`,
  and that hypothesis is exposed explicitly.
* §4  The finite-field change of variables `h' ↦ y = A0 - d C0 h'` as a bijection, and the
  induced reindexing of a finite sum into Kloosterman shape.  **The Weil bound is not
  formalised** and is not used anywhere.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace FractionalLinear

variable {R : Type*} [CommRing R]

/-! ## §1  Linearisation of the opposite row -/

/-- **`fractionalLinear_to_linear`.**  `LEAN_PROVED`.  Pure ring algebra: from the source
relation `(A0 - d C0 h') h = C0 h' b` and `N = b + d h`,

```
d * C0 * N * h' = A0 * (N - b).
```
-/
theorem fractionalLinear_to_linear {A0 C0 d h h' b N : R}
    (hsrc : (A0 - d * C0 * h') * h = C0 * h' * b) (hN : N = b + d * h) :
    d * C0 * N * h' = A0 * (N - b) := by
  subst hN; linear_combination (-d) * hsrc

/-- **`oppositeRow_linearized`.**  `LEAN_PROVED`.  The same identity, bracketed as a linear
equation in the unknown `h'` with coefficient `d * C0 * N`. -/
theorem oppositeRow_linearized {A0 C0 d h h' b N : R}
    (hsrc : (A0 - d * C0 * h') * h = C0 * h' * b) (hN : N = b + d * h) :
    (d * C0 * N) * h' = A0 * (N - b) :=
  fractionalLinear_to_linear hsrc hN

/-! ## §2  Uniqueness of the opposite-row residue -/

/-- **`oppositeRow_unique_residue`.**  `LEAN_PROVED`.  If the coefficient `d C0 N` is a unit
(e.g. in `ZMod x`), the linearised equation determines `h'` uniquely:

```
h' = A0 * (N - b) * (d * C0 * N)⁻¹.
```
-/
theorem oppositeRow_unique_residue {A0 C0 d h' b N : R}
    (hu : IsUnit (d * C0 * N)) (hlin : (d * C0 * N) * h' = A0 * (N - b)) :
    h' = A0 * (N - b) * Ring.inverse (d * C0 * N) := by
  calc h' = h' * ((d * C0 * N) * Ring.inverse (d * C0 * N)) := by
            rw [Ring.mul_inverse_cancel _ hu, mul_one]
    _ = ((d * C0 * N) * h') * Ring.inverse (d * C0 * N) := by ring
    _ = A0 * (N - b) * Ring.inverse (d * C0 * N) := by rw [hlin]

/-- **`oppositeRow_unique_residue_of_source`.**  `LEAN_PROVED`.  The composition of §1 and §2:
straight from the source relation to the unique residue. -/
theorem oppositeRow_unique_residue_of_source {A0 C0 d h h' b N : R}
    (hsrc : (A0 - d * C0 * h') * h = C0 * h' * b) (hN : N = b + d * h)
    (hu : IsUnit (d * C0 * N)) :
    h' = A0 * (N - b) * Ring.inverse (d * C0 * N) :=
  oppositeRow_unique_residue hu (oppositeRow_linearized hsrc hN)

/-- **`oppositeRow_unique_residue_zmod`.**  `LEAN_PROVED`.  The `ZMod x` instance of §2, which is
the form the C0 branch uses. -/
theorem oppositeRow_unique_residue_zmod (x : ℕ) {A0 C0 d h h' b N : ZMod x}
    (hsrc : (A0 - d * C0 * h') * h = C0 * h' * b) (hN : N = b + d * h)
    (hu : IsUnit (d * C0 * N)) :
    h' = A0 * (N - b) * Ring.inverse (d * C0 * N) :=
  oppositeRow_unique_residue_of_source hsrc hN hu

/-! ## §3  Fractional-linear representation of `kappa` -/

/-- **`denominator_ne_zero_of_unit`.**  `LEAN_PROVED`. -/
theorem denominator_ne_zero_of_unit [Nontrivial R] {y : R} (hy : IsUnit y) : y ≠ 0 :=
  hy.ne_zero

/-- **`kappa_fractionalLinear_of_source`.**  `LEAN_PROVED`.  From the source algebra

```
(A0 - d C0 h') h = C0 h' b,      kappa * b = b + d * h,
```

with `b` a unit (this is exactly what licenses the cancellation, and it is exposed) and the
denominator `A0 - d C0 h'` a unit,

```
kappa = A0 * (A0 - d * C0 * h')⁻¹.
```
-/
theorem kappa_fractionalLinear_of_source {A0 C0 d h h' b kappa : R}
    (hb : IsUnit b) (hy : IsUnit (A0 - d * C0 * h'))
    (hsrc : (A0 - d * C0 * h') * h = C0 * h' * b)
    (hkappa : kappa * b = b + d * h) :
    kappa = A0 * Ring.inverse (A0 - d * C0 * h') := by
  set y := A0 - d * C0 * h' with hydef
  set w := Ring.inverse y with hwdef
  have hyw : y * w = 1 := Ring.mul_inverse_cancel _ hy
  have hh : h = C0 * h' * b * w := by
    calc h = (y * w) * h := by rw [hyw, one_mul]
      _ = (y * h) * w := by ring
      _ = C0 * h' * b * w := by rw [hsrc]
  have key : kappa * b = (A0 * w) * b := by
    rw [hkappa, hh]
    have hrw : (A0 * w) * b = (y + d * C0 * h') * w * b := by rw [hydef]; ring
    rw [hrw]
    calc b + d * (C0 * h' * b * w) = (y * w) * b + d * C0 * h' * w * b := by rw [hyw]; ring
      _ = (y + d * C0 * h') * w * b := by ring
  exact hb.mul_right_cancel key

/-- **`kappa_fractionalLinear_of_source_zmod`.**  `LEAN_PROVED`.  The `ZMod x` instance. -/
theorem kappa_fractionalLinear_of_source_zmod (x : ℕ) {A0 C0 d h h' b kappa : ZMod x}
    (hb : IsUnit b) (hy : IsUnit (A0 - d * C0 * h'))
    (hsrc : (A0 - d * C0 * h') * h = C0 * h' * b)
    (hkappa : kappa * b = b + d * h) :
    kappa = A0 * Ring.inverse (A0 - d * C0 * h') :=
  kappa_fractionalLinear_of_source hb hy hsrc hkappa

/-! ## §4  The change of variables `h' ↦ y = A0 - c h'`

Here `c` plays the role of `d * C0`.  Only the bijection and the resulting reindexing of a
finite sum are formalised.  **No Weil / Kloosterman bound is asserted**: the identity below
merely puts the fractional-linear phase into Kloosterman shape. -/

/-- **`affine_leftInverse`.**  `LEAN_PROVED`. -/
theorem affine_leftInverse {A0 c : R} (hc : IsUnit c) (h' : R) :
    (A0 - (A0 - c * h')) * Ring.inverse c = h' := by
  have hrw : A0 - (A0 - c * h') = c * h' := by ring
  rw [hrw, mul_comm c h', mul_assoc, Ring.mul_inverse_cancel _ hc, mul_one]

/-- **`affine_rightInverse`.**  `LEAN_PROVED`. -/
theorem affine_rightInverse {A0 c : R} (hc : IsUnit c) (y : R) :
    A0 - c * ((A0 - y) * Ring.inverse c) = y := by
  have hrw : c * ((A0 - y) * Ring.inverse c) = (A0 - y) * (c * Ring.inverse c) := by ring
  rw [hrw, Ring.mul_inverse_cancel _ hc, mul_one]; ring

/-- **`affine_bijective`.**  `LEAN_PROVED`.  `h' ↦ A0 - c h'` is a bijection of the ring
whenever `c` is a unit. -/
theorem affine_bijective {A0 c : R} (hc : IsUnit c) :
    Function.Bijective (fun h' : R => A0 - c * h') :=
  Function.bijective_iff_has_inverse.mpr
    ⟨fun y => (A0 - y) * Ring.inverse c, affine_leftInverse hc, affine_rightInverse hc⟩

/-- **`affine_pole_iff`.**  `LEAN_PROVED`.  The unique pole of the fractional-linear map is
`h' = A0 c⁻¹`. -/
theorem affine_pole_iff {A0 c h' : R} (hc : IsUnit c) :
    A0 - c * h' = 0 ↔ h' = A0 * Ring.inverse c := by
  constructor
  · intro h
    have hli := affine_leftInverse (A0 := A0) hc h'
    rw [h] at hli
    rw [← hli]; ring_nf
  · intro h
    rw [h]
    have hrw : c * (A0 * Ring.inverse c) = A0 * (c * Ring.inverse c) := by ring
    rw [hrw, Ring.mul_inverse_cancel _ hc, mul_one, sub_self]

/-- **`sum_affine_reindex`.**  `LEAN_PROVED`.  Change of variables in a finite sum. -/
theorem sum_affine_reindex {M : Type*} [AddCommMonoid M] [Fintype R] {A0 c : R}
    (hc : IsUnit c) (f : R → M) :
    ∑ h' : R, f (A0 - c * h') = ∑ y : R, f y :=
  Fintype.sum_bijective _ (affine_bijective hc) _ _ (fun _ => rfl)

/-- **`sum_affine_reindex_nonzero`.**  `LEAN_PROVED`.  The pole-deleted change of variables:
summing over the `h'` avoiding the pole is the same as summing over the nonzero `y`.  Over
`ZMod p` with `p` prime the right-hand index set is exactly `(ZMod p)ˣ`; this is the identity
that converts a fractional-linear phase into a classical Kloosterman-shaped sum.  **No bound on
that sum is claimed here.** -/
theorem sum_affine_reindex_nonzero {M : Type*} [AddCommMonoid M] [Fintype R] [DecidableEq R]
    {A0 c : R} (hc : IsUnit c) (f : R → M) :
    ∑ h' ∈ Finset.univ.filter (fun h' : R => A0 - c * h' ≠ 0), f (A0 - c * h')
      = ∑ y ∈ Finset.univ.filter (fun y : R => y ≠ 0), f y := by
  refine Finset.sum_nbij' (fun h' => A0 - c * h') (fun y => (A0 - y) * Ring.inverse c)
    ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
    exact ha
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
    rw [affine_rightInverse hc]; exact hy
  · intro a _; exact affine_leftInverse hc a
  · intro y _; exact affine_rightInverse hc y
  · intro a _; rfl

end FractionalLinear
end Erdos287
