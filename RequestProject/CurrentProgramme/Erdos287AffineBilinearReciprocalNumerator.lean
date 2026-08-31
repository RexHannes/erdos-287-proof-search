import Mathlib
import RequestProject.CurrentProgramme.Erdos287ReciprocalUnitaryFourier

/-!
# Affine / bilinear moving numerators — Erdős #287 (append-only)

Pure modular algebra, unconditional, kernel-checked.  Nothing analytic and nothing about the
physical source is asserted here.

For units `S₁, S₂` of `ZMod m`:

* `(S₁ S₂)⁻¹ = S₁⁻¹ S₂⁻¹`;
* an **affine** numerator `B = B₀ + B₁ S₁` gives
  `B (S₁ S₂)⁻¹ = B₀ S₁⁻¹ S₂⁻¹ + B₁ S₂⁻¹`;
* a **bilinear** numerator `B = B₀ + B₁ S₁ + B₂ S₂ + B₃ S₁ S₂` gives
  `B (S₁ S₂)⁻¹ = B₀ S₁⁻¹ S₂⁻¹ + B₁ S₂⁻¹ + B₂ S₁⁻¹ + B₃`;
* consequently the additive character of the moving numerator factors into four phases, i.e. a
  moving affine/bilinear numerator preserves finite-rank reciprocal Fourier structure.

This is an algebraic bank only.  It does **not** assert that any physical numerator has this
normal form, nor that a two-carrier transverse pair exists.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace AffineBilinearReciprocalNumerator

open Erdos287.ReciprocalUnitaryFourier

variable {m : ℕ}

/-- **`zmod_inv_mul_of_isUnit`.**  `LEAN_PROVED`.  Inversion is multiplicative on units of
`ZMod m`. -/
theorem zmod_inv_mul_of_isUnit {S₁ S₂ : ZMod m} (h₁ : IsUnit S₁) (h₂ : IsUnit S₂) :
    (S₁ * S₂)⁻¹ = S₁⁻¹ * S₂⁻¹ := by
  have e₁ : S₁ * S₁⁻¹ = 1 := ZMod.mul_inv_of_unit _ h₁
  have e₂ : S₂ * S₂⁻¹ = 1 := ZMod.mul_inv_of_unit _ h₂
  have hu : IsUnit (S₁ * S₂) := h₁.mul h₂
  have e₃ : (S₁ * S₂)⁻¹ * (S₁ * S₂) = 1 := ZMod.inv_mul_of_unit _ hu
  have e₄ : (S₁ * S₂) * (S₁⁻¹ * S₂⁻¹) = 1 := by
    calc (S₁ * S₂) * (S₁⁻¹ * S₂⁻¹) = (S₁ * S₁⁻¹) * (S₂ * S₂⁻¹) := by ring
      _ = 1 := by rw [e₁, e₂, one_mul]
  calc (S₁ * S₂)⁻¹ = (S₁ * S₂)⁻¹ * ((S₁ * S₂) * (S₁⁻¹ * S₂⁻¹)) := by rw [e₄, mul_one]
    _ = ((S₁ * S₂)⁻¹ * (S₁ * S₂)) * (S₁⁻¹ * S₂⁻¹) := by ring
    _ = S₁⁻¹ * S₂⁻¹ := by rw [e₃, one_mul]

/-- **`affineNumerator_reciprocal_decomposition`.**  `LEAN_PROVED`.  An affine numerator in the
first carrier: `(B₀ + B₁ S₁)(S₁ S₂)⁻¹ = B₀ S₁⁻¹ S₂⁻¹ + B₁ S₂⁻¹`. -/
theorem affineNumerator_reciprocal_decomposition {S₁ S₂ : ZMod m}
    (h₁ : IsUnit S₁) (h₂ : IsUnit S₂) (B₀ B₁ : ZMod m) :
    (B₀ + B₁ * S₁) * (S₁ * S₂)⁻¹ = B₀ * S₁⁻¹ * S₂⁻¹ + B₁ * S₂⁻¹ := by
  have e₁ : S₁ * S₁⁻¹ = 1 := ZMod.mul_inv_of_unit _ h₁
  rw [zmod_inv_mul_of_isUnit h₁ h₂]
  linear_combination (B₁ * S₂⁻¹) * e₁

/-- **`affineBilinearNumerator_reciprocal_decomposition`.**  `LEAN_PROVED`.  A bilinear moving
numerator decomposes into exactly four reciprocal terms:

`(B₀ + B₁ S₁ + B₂ S₂ + B₃ S₁ S₂)(S₁ S₂)⁻¹ = B₀ S₁⁻¹ S₂⁻¹ + B₁ S₂⁻¹ + B₂ S₁⁻¹ + B₃`. -/
theorem affineBilinearNumerator_reciprocal_decomposition {S₁ S₂ : ZMod m}
    (h₁ : IsUnit S₁) (h₂ : IsUnit S₂) (B₀ B₁ B₂ B₃ : ZMod m) :
    (B₀ + B₁ * S₁ + B₂ * S₂ + B₃ * S₁ * S₂) * (S₁ * S₂)⁻¹
      = B₀ * S₁⁻¹ * S₂⁻¹ + B₁ * S₂⁻¹ + B₂ * S₁⁻¹ + B₃ := by
  have e₁ : S₁ * S₁⁻¹ = 1 := ZMod.mul_inv_of_unit _ h₁
  have e₂ : S₂ * S₂⁻¹ = 1 := ZMod.mul_inv_of_unit _ h₂
  rw [zmod_inv_mul_of_isUnit h₁ h₂]
  linear_combination (B₁ * S₂⁻¹ + B₃ * S₂ * S₂⁻¹) * e₁ + (B₂ * S₁⁻¹ + B₃) * e₂

/-- **`affineBilinearNumerator_character_factorisation`.**  `LEAN_PROVED`.  The additive
character of a bilinear moving numerator over `S₁ S₂` factors into four phases: a rank-one
reciprocal phase, two single-carrier reciprocal phases and a constant.  This is the exact sense
in which a moving affine/bilinear numerator preserves finite-rank reciprocal Fourier
structure. -/
theorem affineBilinearNumerator_character_factorisation [NeZero m] {S₁ S₂ : ZMod m}
    (h₁ : IsUnit S₁) (h₂ : IsUnit S₂) (B₀ B₁ B₂ B₃ : ZMod m) :
    ZMod.stdAddChar ((B₀ + B₁ * S₁ + B₂ * S₂ + B₃ * S₁ * S₂) * (S₁ * S₂)⁻¹)
      = ZMod.stdAddChar (B₀ * S₁⁻¹ * S₂⁻¹) * ZMod.stdAddChar (B₁ * S₂⁻¹) *
          ZMod.stdAddChar (B₂ * S₁⁻¹) * ZMod.stdAddChar B₃ := by
  rw [affineBilinearNumerator_reciprocal_decomposition h₁ h₂ B₀ B₁ B₂ B₃]
  rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]

/-- **`affineNumerator_character_factorisation`.**  `LEAN_PROVED`.  The affine (single moving
carrier) case of the previous factorisation. -/
theorem affineNumerator_character_factorisation [NeZero m] {S₁ S₂ : ZMod m}
    (h₁ : IsUnit S₁) (h₂ : IsUnit S₂) (B₀ B₁ : ZMod m) :
    ZMod.stdAddChar ((B₀ + B₁ * S₁) * (S₁ * S₂)⁻¹)
      = ZMod.stdAddChar (B₀ * S₁⁻¹ * S₂⁻¹) * ZMod.stdAddChar (B₁ * S₂⁻¹) := by
  rw [affineNumerator_reciprocal_decomposition h₁ h₂ B₀ B₁, AddChar.map_add_eq_mul]

/-- **`affineBilinear_rankOne_reduction`.**  `LEAN_PROVED`.  Consequence for a bilinear form:
after the numerator decomposition, the rank-one reciprocal factor `e_m(B₀ S₁⁻¹ S₂⁻¹)` carries
the whole two-carrier oscillation, while the remaining three phases are absorbed into the
coefficient vectors (they depend on at most one carrier each).

The statement is a pure rewriting identity of finite sums; no estimate is claimed. -/
theorem affineBilinear_rankOne_reduction [NeZero m] (S T : Finset (ZMod m))
    (hS : ∀ r ∈ S, IsUnit r) (hT : ∀ s ∈ T, IsUnit s) (alpha beta : ZMod m → ℂ)
    (B₀ B₁ B₂ B₃ : ZMod m) :
    ∑ r ∈ S, ∑ s ∈ T, alpha r * beta s *
        ZMod.stdAddChar ((B₀ + B₁ * r + B₂ * s + B₃ * r * s) * (r * s)⁻¹)
      = ∑ r ∈ S, ∑ s ∈ T,
          (alpha r * ZMod.stdAddChar (B₂ * r⁻¹)) *
          (beta s * ZMod.stdAddChar (B₁ * s⁻¹) * ZMod.stdAddChar B₃) *
          ZMod.stdAddChar (B₀ * r⁻¹ * s⁻¹) := by
  refine Finset.sum_congr rfl ?_
  intro r hr
  refine Finset.sum_congr rfl ?_
  intro s hs
  rw [affineBilinearNumerator_character_factorisation (hS r hr) (hT s hs) B₀ B₁ B₂ B₃]
  ring

end AffineBilinearReciprocalNumerator
end Erdos287
