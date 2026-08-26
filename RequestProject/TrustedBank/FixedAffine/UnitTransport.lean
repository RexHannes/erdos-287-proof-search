import Mathlib

/-!
# Trusted bank — Bank B: unit / finite-sum transport

Abstract unit-permutation lemmas, and the exact *reindexing* identity for a
Kloosterman-shaped finite sum.  Nothing here is analytic: every statement is a finite
algebraic bijection / reindexing fact.
-/

open scoped BigOperators

namespace TrustedBank
namespace UnitTransport

section Monoid

variable {R : Type*} [Monoid R]

/-- Multiplication by a unit is a bijection of the ambient monoid. -/
theorem unitMul_bijective (u : Rˣ) : Function.Bijective (fun x : R => (u : R) * x) :=
  (Units.mulLeft u).bijective

/-- **Bank B.1 — finite sums are invariant under multiplication by a unit.** -/
theorem sum_unitMul [Fintype R] {M : Type*} [AddCommMonoid M]
    (u : Rˣ) (f : R → M) : ∑ x : R, f ((u : R) * x) = ∑ x : R, f x :=
  Fintype.sum_equiv (Units.mulLeft u) _ _ (fun _ => rfl)

end Monoid

section MonoidWithZero

variable {R : Type*} [MonoidWithZero R]

/-- **Bank B.2 — a unit multiple vanishes iff the original element vanishes.** -/
@[simp] theorem unitMul_eq_zero_iff (u : Rˣ) (x : R) : (u : R) * x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have : ((u⁻¹ : Rˣ) : R) * ((u : R) * x) = 0 := by rw [h, mul_zero]
    rwa [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] at this
  · rintro rfl; exact mul_zero _

end MonoidWithZero

/-- **Bank B.3 — `ℓ²` energy is invariant under a permutation of the index set.** -/
theorem l2_energy_perm {I : Type*} [Fintype I] {E : Type*} [NormedAddCommGroup E]
    (e : Equiv.Perm I) (f : I → E) : ∑ i, ‖f (e i)‖ ^ 2 = ∑ i, ‖f i‖ ^ 2 :=
  Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- **Bank B.3' — any finite sum is invariant under a reindexing bijection. -/
theorem sum_perm {I : Type*} [Fintype I] {M : Type*} [AddCommMonoid M]
    (e : Equiv.Perm I) (f : I → M) : ∑ i, f (e i) = ∑ i, f i :=
  Fintype.sum_equiv e _ _ (fun _ => rfl)

/-! ## The Kloosterman-shaped sum and its exact unit-change identity

We do not build an analytic Kloosterman library.  For an arbitrary "additive-character
shaped" function `ψ : ZMod q → V` we set

`S ψ A B = ∑_{x ∈ (ZMod q)ˣ} ψ (A * x⁻¹ + B * x)`,

which for `ψ = e_q` is the usual `S(A, B; q)`.  The classical identity
`S(A, B; q) = S(A λ, B λ⁻¹; q)` for a unit `λ` is pure reindexing. -/

variable {q : ℕ} [NeZero q] {V : Type*} [AddCommMonoid V]

/-- The Kloosterman-shaped sum `∑_{x unit} ψ (A x⁻¹ + B x)`. -/
def kloostermanLike (ψ : ZMod q → V) (A B : ZMod q) : V :=
  ∑ x : (ZMod q)ˣ, ψ (A * ((x⁻¹ : (ZMod q)ˣ) : ZMod q) + B * (x : ZMod q))

/-- **Bank B.4 — the exact unit-change (reindexing) identity**
`S(A, B; q) = S(A·λ, B·λ⁻¹; q)` for any unit `λ`. -/
theorem kloostermanLike_unit_change (ψ : ZMod q → V) (A B : ZMod q) (lam : (ZMod q)ˣ) :
    kloostermanLike ψ A B
      = kloostermanLike ψ (A * (lam : ZMod q)) (B * ((lam⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
  unfold kloostermanLike
  refine Fintype.sum_equiv (Equiv.mulLeft lam) _ _ ?_
  intro x
  have h1 : (((lam * x)⁻¹ : (ZMod q)ˣ) : ZMod q)
      = ((lam⁻¹ : (ZMod q)ˣ) : ZMod q) * ((x⁻¹ : (ZMod q)ˣ) : ZMod q) := by
    rw [mul_inv_rev, Units.val_mul]; ring
  have h2 : (((lam * x : (ZMod q)ˣ)) : ZMod q) = (lam : ZMod q) * (x : ZMod q) := by
    rw [Units.val_mul]
  have hlam : (lam : ZMod q) * ((lam⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Equiv.coe_mulLeft, h1, h2]
  congr 1
  linear_combination (-(A * ((x⁻¹ : (ZMod q)ˣ) : ZMod q)) - B * ((x : (ZMod q)ˣ) : ZMod q)) * hlam

end UnitTransport
end TrustedBank
