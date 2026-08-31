import Mathlib

/-!
# Reciprocal unitary Fourier bank — Erdős #287 (append-only)

This module is **append-only**.  It edits nothing and weakens nothing; it adds the finite,
unconditional Fourier core behind the C0 / transverse analytic discussion.

Everything here is a kernel-checked finite theorem about the additive character of `ZMod x`:

* §1  a finite Cauchy–Schwarz helper for complex coefficients;
* §2  the kernel `F_C(y,z) = e_x(C y z)` for an arbitrary **unit** `C` and an arbitrary modulus
  `x > 0` (no squarefree, no primality, no `φ(x)/x` density factor);
* §3  the full Fourier Gram identity `∑_z F_C(y,z) conj (F_C(y',z)) = x · [y = y']`,
  i.e. `F_C F_C^* = x I`;
* §4  the exact bilinear (quadratic) bound
  `‖∑_{y,z} A y B z F_C(y,z)‖² ≤ x ‖A‖₂² ‖B‖₂²`, first over all residues, then over arbitrary
  finite index sets (zero extension);
* §5  the inversion permutation of the units of `ZMod x`;
* §6  the reciprocal-kernel corollary
  `‖∑_{r,s unit} A r B s e_x(C r⁻¹ s⁻¹)‖² ≤ x ‖A‖₂² ‖B‖₂²`.

Deliberate conservatism.

* The statements quantify over **arbitrary** `ℓ²` coefficient vectors.  In particular no
  pointwise description of any physical coefficient (`Ω_H` or otherwise) enters the theorem;
  only its `ℓ²` norm can ever be used.
* The modulus is an arbitrary positive natural number `x`; it is never identified with any
  analytic parameter `X`.
* Nothing here asserts that any analytic branch of Erdős #287 is closed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace ReciprocalUnitaryFourier

open Finset

/-! ## §1  Finite Cauchy–Schwarz for complex coefficients -/

/-- **`norm_sum_mul_sq_le`.**  `LEAN_PROVED`.  Finite Cauchy–Schwarz over `ℂ`:
`‖∑ f g‖² ≤ (∑ ‖f‖²)(∑ ‖g‖²)`. -/
theorem norm_sum_mul_sq_le {ι : Type*} (s : Finset ι) (f g : ι → ℂ) :
    ‖∑ i ∈ s, f i * g i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖ ^ 2) * (∑ i ∈ s, ‖g i‖ ^ 2) := by
  have h1 : ‖∑ i ∈ s, f i * g i‖ ≤ ∑ i ∈ s, ‖f i‖ * ‖g i‖ := by
    calc ‖∑ i ∈ s, f i * g i‖ ≤ ∑ i ∈ s, ‖f i * g i‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, ‖f i‖ * ‖g i‖ := by simp
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖f i‖) (fun i => ‖g i‖)
  calc ‖∑ i ∈ s, f i * g i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖ * ‖g i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := by simpa using h2

/-! ## §2  The unitary Fourier kernel -/

variable {x : ℕ}

/-- The finite Fourier kernel `F_C(y,z) = e_x(C y z)`, built from the standard additive
character of `ZMod x`.  `x` is an arbitrary positive modulus, composite allowed. -/
noncomputable def unitaryFourierKernel [NeZero x] (C y z : ZMod x) : ℂ :=
  ZMod.stdAddChar (C * y * z)

/-- **`unitaryFourierKernel_symm`.**  `LEAN_PROVED`.  The kernel is symmetric in its two
arguments. -/
theorem unitaryFourierKernel_symm [NeZero x] (C y z : ZMod x) :
    unitaryFourierKernel C y z = unitaryFourierKernel C z y := by
  simp [unitaryFourierKernel, mul_comm, mul_left_comm]

/-- **`unitaryFourierKernel_norm`.**  `LEAN_PROVED`.  Each kernel entry has modulus one. -/
theorem unitaryFourierKernel_norm [NeZero x] (C y z : ZMod x) :
    ‖unitaryFourierKernel C y z‖ = 1 := by
  simp [unitaryFourierKernel]

/-! ## §3  The full Fourier Gram identity -/

/-- **`unitaryFourier_mulConj_sum`.**  `LEAN_PROVED`.  The exact Gram identity
`∑_z F_C(y,z) · conj (F_C(y',z)) = x · [y = y']`, i.e. `F_C F_C^* = x I`.

No squarefree hypothesis on `x` is used: the modulus is an arbitrary positive natural. -/
theorem unitaryFourier_mulConj_sum [NeZero x] {C : ZMod x} (hC : IsUnit C) (y y' : ZMod x) :
    ∑ z : ZMod x, unitaryFourierKernel C y z * (starRingEnd ℂ) (unitaryFourierKernel C y' z)
      = if y = y' then (x : ℂ) else 0 := by
  have h : ∀ z : ZMod x,
      unitaryFourierKernel C y z * (starRingEnd ℂ) (unitaryFourierKernel C y' z)
        = ZMod.stdAddChar (z * (C * (y - y'))) := by
    intro z
    rw [unitaryFourierKernel, unitaryFourierKernel, ← AddChar.map_neg_eq_conj,
      ← AddChar.map_add_eq_mul]
    ring_nf
  simp only [h]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar x)]
  have hiff : (C * (y - y') = 0) ↔ (y = y') := by
    constructor
    · intro h0
      have h1 : y - y' = 0 := hC.mul_right_eq_zero.mp h0
      exact sub_eq_zero.mp h1
    · intro h0; simp [h0]
  by_cases hyy : y = y' <;> simp [hiff, hyy, ZMod.card]

/-- **`unitaryFourier_column_energy`.**  `LEAN_PROVED`.  Exact `ℓ²` energy of a Fourier
transform: `∑_y ‖∑_z B z F_C(y,z)‖² = x ∑_z ‖B z‖²`. -/
theorem unitaryFourier_column_energy [NeZero x] {C : ZMod x} (hC : IsUnit C) (B : ZMod x → ℂ) :
    ∑ y : ZMod x, ‖∑ z : ZMod x, B z * unitaryFourierKernel C y z‖ ^ 2
      = (x : ℝ) * ∑ z : ZMod x, ‖B z‖ ^ 2 := by
  have key : ((∑ y : ZMod x, ‖∑ z : ZMod x, B z * unitaryFourierKernel C y z‖ ^ 2 : ℝ) : ℂ)
      = (((x : ℝ) * ∑ z : ZMod x, ‖B z‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    have step : ∀ y : ZMod x,
        ((‖∑ z : ZMod x, B z * unitaryFourierKernel C y z‖ : ℝ) : ℂ) ^ 2
          = (∑ z : ZMod x, B z * unitaryFourierKernel C y z) *
              (starRingEnd ℂ) (∑ z : ZMod x, B z * unitaryFourierKernel C y z) :=
      fun y => (Complex.mul_conj' _).symm
    simp only [step]
    rw [Finset.sum_congr rfl (fun y _ => by rw [map_sum, Finset.sum_mul_sum])]
    rw [Finset.sum_comm]
    have h2 : ∀ z : ZMod x, ∑ y : ZMod x, ∑ z' : ZMod x,
        (B z * unitaryFourierKernel C y z) *
          ((starRingEnd ℂ) (B z' * unitaryFourierKernel C y z'))
        = ∑ z' : ZMod x, B z * (starRingEnd ℂ) (B z') *
            (∑ y : ZMod x, unitaryFourierKernel C z y *
              (starRingEnd ℂ) (unitaryFourierKernel C z' y)) := by
      intro z
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro z' _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro y _
      rw [map_mul, unitaryFourierKernel_symm C y z, unitaryFourierKernel_symm C y z']
      ring
    rw [Finset.sum_congr rfl (fun z _ => h2 z)]
    simp only [unitaryFourier_mulConj_sum hC]
    simp [Complex.mul_conj', Finset.mul_sum, mul_comm]
  exact_mod_cast key

/-! ## §4  The bilinear bound -/

/-- **`unitaryFourier_bilinear_bound`.**  `LEAN_PROVED`.  The exact quadratic bound
`‖∑_{y,z} A y B z F_C(y,z)‖² ≤ x (∑_y ‖A y‖²)(∑_z ‖B z‖²)`.

This is finite-dimensional Cauchy–Schwarz plus the exact Gram identity; no operator-theoretic
input is assumed.  The coefficients are arbitrary. -/
theorem unitaryFourier_bilinear_bound [NeZero x] {C : ZMod x} (hC : IsUnit C)
    (A B : ZMod x → ℂ) :
    ‖∑ y : ZMod x, ∑ z : ZMod x, A y * B z * unitaryFourierKernel C y z‖ ^ 2
      ≤ (x : ℝ) * (∑ y : ZMod x, ‖A y‖ ^ 2) * (∑ z : ZMod x, ‖B z‖ ^ 2) := by
  have hrw : ∑ y : ZMod x, ∑ z : ZMod x, A y * B z * unitaryFourierKernel C y z
      = ∑ y : ZMod x, A y * (∑ z : ZMod x, B z * unitaryFourierKernel C y z) := by
    refine Finset.sum_congr rfl ?_
    intro y _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [hrw]
  calc ‖∑ y : ZMod x, A y * (∑ z : ZMod x, B z * unitaryFourierKernel C y z)‖ ^ 2
      ≤ (∑ y : ZMod x, ‖A y‖ ^ 2) *
          (∑ y : ZMod x, ‖∑ z : ZMod x, B z * unitaryFourierKernel C y z‖ ^ 2) :=
        norm_sum_mul_sq_le _ _ _
    _ = (∑ y : ZMod x, ‖A y‖ ^ 2) * ((x : ℝ) * ∑ z : ZMod x, ‖B z‖ ^ 2) := by
        rw [unitaryFourier_column_energy hC]
    _ = (x : ℝ) * (∑ y : ZMod x, ‖A y‖ ^ 2) * (∑ z : ZMod x, ‖B z‖ ^ 2) := by ring

/-- **`unitaryFourier_finset_bilinear_bound`.**  `LEAN_PROVED`.  The same bound for coefficients
supported on arbitrary finite sets of residues, proved by zero extension. -/
theorem unitaryFourier_finset_bilinear_bound [NeZero x] {C : ZMod x} (hC : IsUnit C)
    (S T : Finset (ZMod x)) (A B : ZMod x → ℂ) :
    ‖∑ y ∈ S, ∑ z ∈ T, A y * B z * unitaryFourierKernel C y z‖ ^ 2
      ≤ (x : ℝ) * (∑ y ∈ S, ‖A y‖ ^ 2) * (∑ z ∈ T, ‖B z‖ ^ 2) := by
  classical
  set A' : ZMod x → ℂ := fun y => if y ∈ S then A y else 0 with hA'
  set B' : ZMod x → ℂ := fun z => if z ∈ T then B z else 0 with hB'
  have hsum : ∑ y : ZMod x, ∑ z : ZMod x, A' y * B' z * unitaryFourierKernel C y z
      = ∑ y ∈ S, ∑ z ∈ T, A y * B z * unitaryFourierKernel C y z := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun y => y ∈ S)]
    have h1 : ∑ y ∈ Finset.univ.filter (fun y => ¬ y ∈ S),
        ∑ z : ZMod x, A' y * B' z * unitaryFourierKernel C y z = 0 := by
      refine Finset.sum_eq_zero ?_
      intro y hy
      simp only [Finset.mem_filter] at hy
      refine Finset.sum_eq_zero ?_
      intro z _
      simp [hA', hy.2]
    rw [h1, add_zero]
    have h2 : Finset.univ.filter (fun y => y ∈ S) = S := by
      ext y; simp
    rw [h2]
    refine Finset.sum_congr rfl ?_
    intro y hy
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun z => z ∈ T)]
    have h3 : ∑ z ∈ Finset.univ.filter (fun z => ¬ z ∈ T),
        A' y * B' z * unitaryFourierKernel C y z = 0 := by
      refine Finset.sum_eq_zero ?_
      intro z hz
      simp only [Finset.mem_filter] at hz
      simp [hB', hz.2]
    rw [h3, add_zero]
    have h4 : Finset.univ.filter (fun z => z ∈ T) = T := by ext z; simp
    rw [h4]
    exact Finset.sum_congr rfl fun z hz => by simp [hA', hB', hy, hz]
  have hA2 : ∑ y : ZMod x, ‖A' y‖ ^ 2 = ∑ y ∈ S, ‖A y‖ ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun y => y ∈ S)]
    have h1 : ∑ y ∈ Finset.univ.filter (fun y => ¬ y ∈ S), ‖A' y‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero ?_
      intro y hy
      simp only [Finset.mem_filter] at hy
      simp [hA', hy.2]
    have h2 : Finset.univ.filter (fun y => y ∈ S) = S := by ext y; simp
    rw [h1, add_zero, h2]
    exact Finset.sum_congr rfl fun y hy => by simp [hA', hy]
  have hB2 : ∑ z : ZMod x, ‖B' z‖ ^ 2 = ∑ z ∈ T, ‖B z‖ ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun z => z ∈ T)]
    have h1 : ∑ z ∈ Finset.univ.filter (fun z => ¬ z ∈ T), ‖B' z‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero ?_
      intro z hz
      simp only [Finset.mem_filter] at hz
      simp [hB', hz.2]
    have h2 : Finset.univ.filter (fun z => z ∈ T) = T := by ext z; simp
    rw [h1, add_zero, h2]
    exact Finset.sum_congr rfl fun z hz => by simp [hB', hz]
  have := unitaryFourier_bilinear_bound hC A' B'
  rwa [hsum, hA2, hB2] at this

/-! ## §5  The inversion permutation of the units -/

/-- **`isUnit_zmod_inv`.**  `LEAN_PROVED`.  The inverse of a unit of `ZMod x` is a unit. -/
theorem isUnit_zmod_inv {y : ZMod x} (hy : IsUnit y) : IsUnit y⁻¹ :=
  IsUnit.of_mul_eq_one _ (ZMod.inv_mul_of_unit _ hy)

/-- **`zmod_inv_inv_of_isUnit`.**  `LEAN_PROVED`.  On units, inversion is an involution. -/
theorem zmod_inv_inv_of_isUnit {y : ZMod x} (hy : IsUnit y) : (y⁻¹)⁻¹ = y := by
  have h1 : y⁻¹ * y = 1 := ZMod.inv_mul_of_unit _ hy
  have hu : IsUnit y⁻¹ := IsUnit.of_mul_eq_one _ h1
  have h2 : y⁻¹ * (y⁻¹)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu
  calc (y⁻¹)⁻¹ = (y * y⁻¹) * (y⁻¹)⁻¹ := by rw [ZMod.mul_inv_of_unit _ hy, one_mul]
    _ = y * (y⁻¹ * (y⁻¹)⁻¹) := by ring
    _ = y := by rw [h2, mul_one]

/-- **`zmod_inv_bijOn_units`.**  `LEAN_PROVED`.  Inversion is a bijection of any set of units
of `ZMod x` that is closed under inversion; in particular of the full set of units. -/
theorem zmod_inv_bijOn_units :
    Set.BijOn (fun y : ZMod x => y⁻¹) {y : ZMod x | IsUnit y} {y : ZMod x | IsUnit y} := by
  refine ⟨fun y hy => isUnit_zmod_inv hy, ?_, ?_⟩
  · intro y hy z hz hyz
    have := congrArg (fun w : ZMod x => w⁻¹) hyz
    simpa [zmod_inv_inv_of_isUnit hy, zmod_inv_inv_of_isUnit hz] using this
  · intro y hy
    exact ⟨y⁻¹, isUnit_zmod_inv hy, zmod_inv_inv_of_isUnit hy⟩

/-! ## §6  The reciprocal-kernel bound -/

/-- **`reciprocalUnitaryFourier_bilinear_bound`.**  `LEAN_PROVED`.  The principal new
unconditional finite theorem: for coefficient vectors supported on finite sets of **units**,

`‖∑_{r ∈ S} ∑_{s ∈ T} A r B s e_x(C r⁻¹ s⁻¹)‖² ≤ x (∑_{r ∈ S} ‖A r‖²)(∑_{s ∈ T} ‖B s‖²)`.

The modulus `x` is arbitrary (composite allowed), `C` is an arbitrary unit and the coefficient
vectors are arbitrary; only their `ℓ²` masses appear on the right. -/
theorem reciprocalUnitaryFourier_bilinear_bound [NeZero x] {C : ZMod x} (hC : IsUnit C)
    (S T : Finset (ZMod x)) (hS : ∀ r ∈ S, IsUnit r) (hT : ∀ s ∈ T, IsUnit s)
    (A B : ZMod x → ℂ) :
    ‖∑ r ∈ S, ∑ s ∈ T, A r * B s * ZMod.stdAddChar (C * r⁻¹ * s⁻¹)‖ ^ 2
      ≤ (x : ℝ) * (∑ r ∈ S, ‖A r‖ ^ 2) * (∑ s ∈ T, ‖B s‖ ^ 2) := by
  classical
  set S' : Finset (ZMod x) := S.image (fun r => r⁻¹) with hS'
  set T' : Finset (ZMod x) := T.image (fun s => s⁻¹) with hT'
  have hinjS : Set.InjOn (fun r : ZMod x => r⁻¹) S := by
    intro r hr r' hr' h
    have := congrArg (fun w : ZMod x => w⁻¹) h
    simpa [zmod_inv_inv_of_isUnit (hS r hr), zmod_inv_inv_of_isUnit (hS r' hr')] using this
  have hinjT : Set.InjOn (fun s : ZMod x => s⁻¹) T := by
    intro s hs s' hs' h
    have := congrArg (fun w : ZMod x => w⁻¹) h
    simpa [zmod_inv_inv_of_isUnit (hT s hs), zmod_inv_inv_of_isUnit (hT s' hs')] using this
  have hsum : ∑ y ∈ S', ∑ z ∈ T',
      (fun y => A y⁻¹) y * (fun z => B z⁻¹) z * unitaryFourierKernel C y z
      = ∑ r ∈ S, ∑ s ∈ T, A r * B s * ZMod.stdAddChar (C * r⁻¹ * s⁻¹) := by
    rw [hS', Finset.sum_image (fun r hr r' hr' h => hinjS hr hr' h)]
    refine Finset.sum_congr rfl ?_
    intro r hr
    rw [hT', Finset.sum_image (fun s hs s' hs' h => hinjT hs hs' h)]
    refine Finset.sum_congr rfl ?_
    intro s hs
    show A r⁻¹⁻¹ * B s⁻¹⁻¹ * unitaryFourierKernel C r⁻¹ s⁻¹
        = A r * B s * ZMod.stdAddChar (C * r⁻¹ * s⁻¹)
    rw [zmod_inv_inv_of_isUnit (hS r hr), zmod_inv_inv_of_isUnit (hT s hs)]
    rfl
  have hA2 : ∑ y ∈ S', ‖A y⁻¹‖ ^ 2 = ∑ r ∈ S, ‖A r‖ ^ 2 := by
    rw [hS', Finset.sum_image (fun r hr r' hr' h => hinjS hr hr' h)]
    exact Finset.sum_congr rfl fun r hr => by rw [zmod_inv_inv_of_isUnit (hS r hr)]
  have hB2 : ∑ z ∈ T', ‖B z⁻¹‖ ^ 2 = ∑ s ∈ T, ‖B s‖ ^ 2 := by
    rw [hT', Finset.sum_image (fun s hs s' hs' h => hinjT hs hs' h)]
    exact Finset.sum_congr rfl fun s hs => by rw [zmod_inv_inv_of_isUnit (hT s hs)]
  have := unitaryFourier_finset_bilinear_bound hC S' T' (fun y => A y⁻¹) (fun z => B z⁻¹)
  rwa [hsum, hA2, hB2] at this

/-- **`transverseTwoCarrierUnitaryFourier`.**  `LEAN_PROVED`.  Naming alias: the transverse
two-carrier mechanism is *literally* the reciprocal unitary Fourier bound, for modulus `m` and
unit `Gamma`.  No second proof and no additional mathematical content. -/
theorem transverseTwoCarrierUnitaryFourier {m : ℕ} [NeZero m] {Gamma : ZMod m}
    (hGamma : IsUnit Gamma) (S₁ S₂ : Finset (ZMod m))
    (hS₁ : ∀ r ∈ S₁, IsUnit r) (hS₂ : ∀ s ∈ S₂, IsUnit s) (alpha beta : ZMod m → ℂ) :
    ‖∑ r ∈ S₁, ∑ s ∈ S₂, alpha r * beta s * ZMod.stdAddChar (Gamma * r⁻¹ * s⁻¹)‖ ^ 2
      ≤ (m : ℝ) * (∑ r ∈ S₁, ‖alpha r‖ ^ 2) * (∑ s ∈ S₂, ‖beta s‖ ^ 2) :=
  reciprocalUnitaryFourier_bilinear_bound hGamma S₁ S₂ hS₁ hS₂ alpha beta

/-! ## §7  Composite modulus witness -/

/-- **`unitaryFourier_mulConj_sum_composite`.**  `LEAN_PROVED`.  Explicit instance of the Gram
identity at the composite modulus `x = 12` with the unit `C = 5`: the theorem is not restricted
to primes or squarefree moduli. -/
theorem unitaryFourier_mulConj_sum_composite (y y' : ZMod 12) :
    ∑ z : ZMod 12, unitaryFourierKernel (5 : ZMod 12) y z *
        (starRingEnd ℂ) (unitaryFourierKernel (5 : ZMod 12) y' z)
      = if y = y' then (12 : ℂ) else 0 := by
  have hC : IsUnit (5 : ZMod 12) := by decide +kernel
  simpa using unitaryFourier_mulConj_sum (x := 12) hC y y'

end ReciprocalUnitaryFourier
end Erdos287
