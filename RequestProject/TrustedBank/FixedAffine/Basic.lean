import Mathlib

/-!
# Trusted bank — Bank A: fixed-affine integer normal form

Pure (finite) algebra of a pair of affine forms

* `L₁ n = a₁ n + b₁`
* `L₂ n = a₂ n + b₂`

with determinant `Δ = a₁ b₂ - a₂ b₁`.

Everything here is an identity in a commutative ring (or a field), proved by `ring`
style reasoning.  **No analytic or prime-distribution statement occurs in this file.**
-/

namespace TrustedBank
namespace FixedAffine

section CommRingLayer

variable {R : Type*} [CommRing R]

/-- The affine form `n ↦ a * n + b`. -/
def lin (a b : R) : R → R := fun n => a * n + b

@[simp] lemma lin_apply (a b n : R) : lin a b n = a * n + b := rfl

/-- The determinant `Δ = a₁ b₂ - a₂ b₁` of the pair of affine forms. -/
def det (a₁ b₁ a₂ b₂ : R) : R := a₁ * b₂ - a₂ * b₁

@[simp] lemma det_apply (a₁ b₁ a₂ b₂ : R) : det a₁ b₁ a₂ b₂ = a₁ * b₂ - a₂ * b₁ := rfl

/-- **Bank A.1 — the fixed-affine cross identity.**
`a₁ · L₂(n) = a₂ · L₁(n) + Δ` in any commutative ring. -/
theorem affine_cross_identity (a₁ b₁ a₂ b₂ n : R) :
    a₁ * lin a₂ b₂ n = a₂ * lin a₁ b₁ n + det a₁ b₁ a₂ b₂ := by
  simp only [lin_apply, det_apply]; ring

/-- The cross identity over `ℤ`. -/
theorem affine_cross_identity_int (a₁ b₁ a₂ b₂ n : ℤ) :
    a₁ * (a₂ * n + b₂) = a₂ * (a₁ * n + b₁) + (a₁ * b₂ - a₂ * b₁) := by ring

/-- **Bank A.2 — root transport.**  If `m = L₁(n)` then `a₁ · L₂(n) = a₂ · m + Δ`. -/
theorem root_transport {a₁ b₁ a₂ b₂ n m : R} (hm : m = lin a₁ b₁ n) :
    a₁ * lin a₂ b₂ n = a₂ * m + det a₁ b₁ a₂ b₂ := by
  subst hm; exact affine_cross_identity _ _ _ _ _

end CommRingLayer

section FieldLayer

variable {K : Type*} [Field K] {a₁ b₁ a₂ b₂ n m : K}

/-- The first forbidden root, in the `m = L₁(n)` coordinate, is `m = 0`. -/
theorem first_root_iff (hm : m = lin a₁ b₁ n) : lin a₁ b₁ n = 0 ↔ m = 0 := by
  subst hm; rfl

/-- **Bank A.3 — the second forbidden root.**  For nonzero `a₁, a₂` (this is the
"good prime" condition once `K = ZMod p`), in the coordinate `m = L₁(n)` the vanishing
of `L₂` happens exactly at `m = -Δ / a₂`. -/
theorem second_root_iff (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (hm : m = lin a₁ b₁ n) :
    lin a₂ b₂ n = 0 ↔ m = -(det a₁ b₁ a₂ b₂) / a₂ := by
  have h := root_transport (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) hm
  constructor
  · intro h0
    rw [h0, mul_zero] at h
    rw [eq_div_iff ha₂]
    linear_combination -h
  · intro h0
    have : a₂ * m = -(det a₁ b₁ a₂ b₂) := by
      rw [h0]; field_simp
    have : a₁ * lin a₂ b₂ n = 0 := by rw [h, this]; ring
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' ha₁
    · exact h'

/-- The normalising unit `-α = -a₂ / Δ`. -/
def normUnit (a₁ b₁ a₂ b₂ : K) : K := -(a₂ / det a₁ b₁ a₂ b₂)

/-- **Bank A.4a — the first root goes to `0`.** -/
@[simp] theorem normUnit_first_root : normUnit a₁ b₁ a₂ b₂ * (0 : K) = 0 := mul_zero _

/-- **Bank A.4b — the second root goes to `1`.** -/
theorem normUnit_second_root (ha₂ : a₂ ≠ 0) (hΔ : det a₁ b₁ a₂ b₂ ≠ 0) :
    normUnit a₁ b₁ a₂ b₂ * (-(det a₁ b₁ a₂ b₂) / a₂) = 1 := by
  unfold normUnit
  field_simp

/-- **Bank A.4 — canonical normalisation of the forbidden pair.**  Multiplication by the
unit `-α = -a₂/Δ` carries the two forbidden roots `{0, -Δ/a₂}` onto the canonical pair
`{0, 1}`. -/
theorem normUnit_image_roots (ha₂ : a₂ ≠ 0) (hΔ : det a₁ b₁ a₂ b₂ ≠ 0) :
    (fun x : K => normUnit a₁ b₁ a₂ b₂ * x) ''
        ({0, -(det a₁ b₁ a₂ b₂) / a₂} : Set K) = ({0, 1} : Set K) := by
  ext y
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl
    · exact Or.inl (mul_zero _)
    · exact Or.inr (normUnit_second_root ha₂ hΔ)
  · rintro (rfl | rfl)
    · exact ⟨0, Or.inl rfl, mul_zero _⟩
    · exact ⟨-(det a₁ b₁ a₂ b₂) / a₂, Or.inr rfl, normUnit_second_root ha₂ hΔ⟩

/-- The normalising unit is nonzero (hence a unit). -/
theorem normUnit_ne_zero (ha₂ : a₂ ≠ 0) (hΔ : det a₁ b₁ a₂ b₂ ≠ 0) :
    normUnit a₁ b₁ a₂ b₂ ≠ 0 := by
  unfold normUnit
  simpa using div_ne_zero ha₂ hΔ

end FieldLayer

section ZModLayer

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- **Bank A.5 — good-prime instantiation.**  Over `ZMod p` with `a₁, a₂, Δ` nonzero,
the two forbidden residues in the `m = L₁(n)` coordinate are `0` and `-Δ/a₂`, and the
unit `-a₂/Δ` normalises them to `{0, 1}`. -/
theorem zmod_forbidden_pair {a₁ b₁ a₂ b₂ : ZMod p}
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (hΔ : det a₁ b₁ a₂ b₂ ≠ 0) (n : ZMod p) :
    (lin a₁ b₁ n = 0 ↔ lin a₁ b₁ n = 0) ∧
      (lin a₂ b₂ n = 0 ↔ lin a₁ b₁ n = -(det a₁ b₁ a₂ b₂) / a₂) ∧
      (fun x : ZMod p => normUnit a₁ b₁ a₂ b₂ * x) ''
          ({0, -(det a₁ b₁ a₂ b₂) / a₂} : Set (ZMod p)) = ({0, 1} : Set (ZMod p)) :=
  ⟨Iff.rfl, second_root_iff ha₁ ha₂ rfl, normUnit_image_roots ha₂ hΔ⟩

end ZModLayer

end FixedAffine
end TrustedBank
