import Mathlib
import RequestProject.CurrentProgramme.Erdos287TransverseGammaReduction
import RequestProject.CurrentProgramme.Erdos287BalancedBUnitaryFourierCompiler
import RequestProject.CurrentProgramme.Erdos287AffineBilinearReciprocalNumerator

/-!
# `q_C` unitary Fourier compiler — Erdős #287 (append-only)

This module is **append-only** and contains **no new Fourier proof**.  It reuses, verbatim:

* `Erdos287.ReciprocalUnitaryFourier.reciprocalUnitaryFourier_bilinear_bound`
  (alias `transverseTwoCarrierUnitaryFourier`);
* `Erdos287.AffineBilinearReciprocalNumerator.zmod_inv_mul_of_isUnit`;
* `Erdos287.BalancedBUnitaryFourier.ProductConvolutionEnergyHypothesis` and
  `threeCarrierReciprocalFourier_of_productEnergy`.

What is new is the *instantiation* at the one-conductor data of
`Erdos287TransverseGammaReduction`: modulus `m_P`, numerator `Γ^red`.  The unit hypothesis
required by the Fourier theorem is discharged by the kernel theorem
`OneConductorData.gammaRed_isUnit`, so the compiler below is **unconditional** in its numerator.

Conservatism.

* Nothing asserts that a given source `q̄` admits a partition `q̄ = S₁ S₂` with any property; the
  partition is a hypothesis (`QBarPartition`), proved neither automatic nor contradictory.
* The product-energy input of the grouped compiler is an explicit hypothesis, reused from the
  existing bank — never discharged here.
* The theorems quantify over arbitrary coefficient vectors: only `ℓ²` masses appear.  In
  particular no pointwise formula for `Ω_H` occurs anywhere ("`Ω_H`-blindness", §4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace TransverseQCUnitary

open Erdos287.ReciprocalUnitaryFourier
open Erdos287.BalancedBUnitaryFourier
open Erdos287.TransverseGammaReduction
open Erdos287.TransverseReducedConductor

/-! ## §1  The `q = S₁ S₂` inverse factorisation -/

/-- **`inv_mul_factorisation_zmod`.**  `LEAN_PROVED`.  If `q = S₁ S₂` with `S₁, S₂` units of
`ZMod n`, then `q⁻¹ = S₁⁻¹ S₂⁻¹`.  This *reuses* the existing bank theorem
`zmod_inv_mul_of_isUnit`; no second proof is given.  (At the level of `ZMod n` the coprimality
`gcd(S₁,S₂) = 1` is not what is needed — the unit conditions are — so it is not assumed.) -/
theorem inv_mul_factorisation_zmod {n : ℕ} {q S₁ S₂ : ZMod n} (hq : q = S₁ * S₂)
    (h₁ : IsUnit S₁) (h₂ : IsUnit S₂) : q⁻¹ = S₁⁻¹ * S₂⁻¹ := by
  rw [hq]
  exact Erdos287.AffineBilinearReciprocalNumerator.zmod_inv_mul_of_isUnit h₁ h₂

/-- **`natCast_isUnit_of_coprime`.**  `LEAN_PROVED`.  A natural number coprime to the modulus is
a unit of `ZMod n`. -/
theorem natCast_isUnit_of_coprime {n s : ℕ} (h : Nat.Coprime s n) : IsUnit ((s : ℕ) : ZMod n) :=
  (ZMod.isUnit_iff_coprime s n).mpr h

/-- **`inv_mul_factorisation_zmod_nat`.**  `LEAN_PROVED`.  The arithmetic form used by the
source: if `q = S₁ S₂` in `ℕ` and both factors are coprime to the modulus `n`, then in `ZMod n`

`(q)⁻¹ = (S₁)⁻¹ (S₂)⁻¹`.

The two coprimality hypotheses are explicit. -/
theorem inv_mul_factorisation_zmod_nat {n S₁ S₂ : ℕ} (h₁ : Nat.Coprime S₁ n)
    (h₂ : Nat.Coprime S₂ n) :
    (((S₁ * S₂ : ℕ) : ZMod n))⁻¹ = ((S₁ : ℕ) : ZMod n)⁻¹ * ((S₂ : ℕ) : ZMod n)⁻¹ :=
  inv_mul_factorisation_zmod (by push_cast; ring) (natCast_isUnit_of_coprime h₁)
    (natCast_isUnit_of_coprime h₂)

/-- **`inv_mul_factorisation_test`.**  `LEAN_PROVED`.  Sanity test at `n = 35`, `S₁ = 3`,
`S₂ = 4`, `q = 12`. -/
theorem inv_mul_factorisation_test :
    ((12 : ZMod 35))⁻¹ = ((3 : ZMod 35))⁻¹ * ((4 : ZMod 35))⁻¹ := by
  decide +kernel

/-! ## §2  The `q_C` unitary Fourier compiler (instantiation, no new proof) -/

/-- **`transverseQCUnitaryFourier_bound`.**  `LEAN_PROVED`.  The banked reciprocal unitary
Fourier bound, instantiated at the one-conductor reduced modulus `m_P` and reduced numerator
`Γ^red`:

`‖∑_{S₁ ∈ S} ∑_{S₂ ∈ T} α(S₁) β(S₂) e_{m_P}(Γ^red S₁⁻¹ S₂⁻¹)‖² ≤ m_P ‖α‖₂² ‖β‖₂²`

for **arbitrary** coefficient vectors supported on units.  The unit hypothesis on the numerator
is *proved*, not assumed (`OneConductorData.gammaRed_isUnit`); the theorem is therefore
unconditional given the packet data. -/
theorem transverseQCUnitaryFourier_bound (D : OneConductorData)
    (S T : Finset (ZMod D.modP)) (hS : ∀ s ∈ S, IsUnit s) (hT : ∀ s ∈ T, IsUnit s)
    (alpha beta : ZMod D.modP → ℂ) :
    ‖∑ s ∈ S, ∑ u ∈ T, alpha s * beta u *
        ZMod.stdAddChar (((D.GammaRed : ℤ) : ZMod D.modP) * s⁻¹ * u⁻¹)‖ ^ 2
      ≤ (D.modP : ℝ) * (∑ s ∈ S, ‖alpha s‖ ^ 2) * (∑ u ∈ T, ‖beta u‖ ^ 2) :=
  reciprocalUnitaryFourier_bilinear_bound D.gammaRed_isUnit S T hS hT alpha beta

/-- **`transverseQCUnitaryFourier_l2_bound`.**  `LEAN_PROVED`.  The same bound with explicit
`ℓ²` budgets substituted on the right. -/
theorem transverseQCUnitaryFourier_l2_bound (D : OneConductorData)
    (S T : Finset (ZMod D.modP)) (hS : ∀ s ∈ S, IsUnit s) (hT : ∀ s ∈ T, IsUnit s)
    (alpha beta : ZMod D.modP → ℂ) (E₁ E₂ : ℝ)
    (hE₁ : ∑ s ∈ S, ‖alpha s‖ ^ 2 ≤ E₁) (hE₂ : ∑ u ∈ T, ‖beta u‖ ^ 2 ≤ E₂) :
    ‖∑ s ∈ S, ∑ u ∈ T, alpha s * beta u *
        ZMod.stdAddChar (((D.GammaRed : ℤ) : ZMod D.modP) * s⁻¹ * u⁻¹)‖ ^ 2
      ≤ (D.modP : ℝ) * E₁ * E₂ := by
  refine (transverseQCUnitaryFourier_bound D S T hS hT alpha beta).trans ?_
  have h1 : (0 : ℝ) ≤ ∑ s ∈ S, ‖alpha s‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have h2 : (0 : ℝ) ≤ ∑ u ∈ T, ‖beta u‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hm : (0 : ℝ) ≤ (D.modP : ℝ) := by positivity
  have hE₂0 : (0 : ℝ) ≤ E₂ := le_trans h2 hE₂
  exact mul_le_mul (mul_le_mul_of_nonneg_left hE₁ hm) hE₂ h2
    (mul_nonneg hm (le_trans h1 hE₁))

/-! ## §3  Product-aggregated (grouped) `q_C` compiler -/

/-- A partition of the reduced `q_C` factor `q̄` of a packet into two groups of atomic factors.
Each group may be a product of several of `2°, E°, R, B°`.  This is a **hypothesis**: nothing
proves that any particular source packet admits a partition with prescribed properties. -/
structure QBarPartition (P : TransversePacket) where
  /-- The first group. -/
  S₁ : ℕ
  /-- The second group. -/
  S₂ : ℕ
  /-- The groups multiply to `q̄`. -/
  split : S₁ * S₂ = P.qBar
  /-- The two groups are coprime. -/
  coprime : Nat.Coprime S₁ S₂

/-- **`qBarPartition_trivial`.**  Every packet has the *trivial* partition
`q̄ = 1 · q̄`; this records that the structure is inhabited and, at the same time, that mere
existence of a partition carries no information — nothing here says that a partition into two
*long* groups exists. -/
def qBarPartition_trivial (P : TransversePacket) : QBarPartition P :=
  { S₁ := 1, S₂ := P.qBar, split := one_mul _, coprime := Nat.coprime_one_left _ }

/-- **`qBarPartition_nontrivial_not_automatic`.**  `LEAN_PROVED`.  A partition into two factors
both `> 1` is *not* automatic: for a packet with `q̄ = 2` no such partition exists. -/
theorem qBarPartition_nontrivial_not_automatic {P : TransversePacket} (hq : P.qBar = 2)
    (Q : QBarPartition P) : Q.S₁ = 1 ∨ Q.S₂ = 1 := by
  have h := Q.split
  rw [hq] at h
  have h1 : Q.S₁ ∣ 2 := ⟨Q.S₂, h.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h₁ | h₁
  · exact Or.inl h₁
  · rw [h₁] at h
    exact Or.inr (by omega)

/-- **`transverseQCGroupedUnitary_of_productEnergy`.**  `LEAN_PROVED (CONDITIONAL)`.

The grouped compiler.  Given

* a partition of the aggregated carrier index set into an `n`-group and an `e`-group, both
  supported on units of `ZMod x`,
* explicit fibre multiplicities `M_N, M_E`,
* an **explicit** product-energy hypothesis for the `n`-coefficient (reused verbatim from the
  existing bank — it is never discharged here),
* an explicit `ℓ²` budget for the `e`-coefficient,

the reciprocal unitary Fourier bound holds with the convolution energy substituted.  Every
analytic input is an explicit named hypothesis; no source partition is claimed to satisfy
them automatically. -/
theorem transverseQCGroupedUnitary_of_productEnergy {x : ℕ} [NeZero x] {C : ZMod x}
    (hC : IsUnit C) (sN sE sa salpha : Finset ℕ) (A beta a alpha : ℕ → ℂ)
    (hNunit : ∀ n ∈ sN, IsUnit ((n : ℕ) : ZMod x))
    (hEunit : ∀ e ∈ sE, IsUnit ((e : ℕ) : ZMod x))
    (MN ME EB Cconv : ℝ)
    (hMN : ∀ r : ZMod x, ((sN.filter (fun n => ((n : ℕ) : ZMod x) = r)).card : ℝ) ≤ MN)
    (hME : ∀ r : ZMod x, ((sE.filter (fun e => ((e : ℕ) : ZMod x) = r)).card : ℝ) ≤ ME)
    (hConv : ProductConvolutionEnergyHypothesis sN sa salpha A a alpha Cconv)
    (hEB : ∑ e ∈ sE, ‖beta e‖ ^ 2 ≤ EB) :
    ‖∑ n ∈ sN, ∑ e ∈ sE,
        A n * beta e *
          ZMod.stdAddChar (C * (((n : ℕ) : ZMod x))⁻¹ * (((e : ℕ) : ZMod x))⁻¹)‖ ^ 2
      ≤ (x : ℝ) * MN * ME *
          (Cconv * (∑ l ∈ sa, ‖a l‖ ^ 2) * (∑ d ∈ salpha, ‖alpha d‖ ^ 2)) * EB :=
  threeCarrierReciprocalFourier_of_productEnergy hC sN sE sa salpha A beta a alpha hNunit hEunit
    MN ME EB Cconv hMN hME hConv hEB

/-! ## §4  `Ω_H`-blindness -/

/-- **`transverseQCUnitary_omegaH_blind`.**  `LEAN_PROVED`.  Structural consequence of the fact
that the finite theorem quantifies over arbitrary coefficient vectors: *any* coefficient family
`omega` — in particular any physical `Ω_H` — with an explicit `ℓ²` bound `E₁` is accepted, and
the resulting bound depends on `omega` **only** through `E₁`.  No pointwise definition of `Ω_H`
occurs, and none is invented: the `ℓ²` bound is a hypothesis supplied by the caller. -/
theorem transverseQCUnitary_omegaH_blind (D : OneConductorData)
    (S T : Finset (ZMod D.modP)) (hS : ∀ s ∈ S, IsUnit s) (hT : ∀ s ∈ T, IsUnit s)
    (E₁ E₂ : ℝ) :
    ∀ omega beta : ZMod D.modP → ℂ,
      (∑ s ∈ S, ‖omega s‖ ^ 2 ≤ E₁) → (∑ u ∈ T, ‖beta u‖ ^ 2 ≤ E₂) →
      ‖∑ s ∈ S, ∑ u ∈ T, omega s * beta u *
          ZMod.stdAddChar (((D.GammaRed : ℤ) : ZMod D.modP) * s⁻¹ * u⁻¹)‖ ^ 2
        ≤ (D.modP : ℝ) * E₁ * E₂ :=
  fun omega beta h₁ h₂ =>
    transverseQCUnitaryFourier_l2_bound D S T hS hT omega beta E₁ E₂ h₁ h₂

end TransverseQCUnitary
end Erdos287
