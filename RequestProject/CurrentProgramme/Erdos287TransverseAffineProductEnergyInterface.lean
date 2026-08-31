import Mathlib
import RequestProject.CurrentProgramme.Erdos287TransverseDualPairwiseFourier

/-!
# Affine-product numerator, collision equation and energy interface — Erdős #287 (append-only)

This module is **append-only**.  It adds:

* the affine-product numerator map `t(Δ,ℓ) = Δ · Ξ'(ℓ) (mod M')`, its pushforward aggregate
  `A_t` and the **exact** identity expressing the dual operator as `∑_{t,r₀} A_t c_{r₀} e_{M'}(t r₀⁻¹)`
  (unconditional finite algebra);
* the exact collision equation `t(Δ₁,ℓ₁) = t(Δ₂,ℓ₂) ↔ Δ₁ Ξ'(ℓ₁) ≡ Δ₂ Ξ'(ℓ₂) (mod M')`;
* an **explicit interface** `AffineProductEnergyBound` for the source-specific modular-hyperbola
  (Cochrane–Shi type) energy, with the constant `K_energy` a parameter.  No such energy theorem is
  proved here and none is assumed: the interface is proved non-automatic;
* the conditional compiler `dualAffineProductFourier_of_energy`, whose conclusion is an explicit
  finite `L²` inequality;
* the weighted `Ω` divisor-moment interface `OmegaWeightedDivisorMomentBound` together with a
  kernel-checked **separation** theorem showing that it is *not* implied by an ordinary `ℓ²`
  normalisation, so the two pins may never be merged;
* the literal residual data type `SimultaneousCriticalPacket`, whose analytic fields are
  unfilled `Prop`s.

Nothing here claims a saving, an energy theorem, or closure of any branch.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace TransverseAffineProduct

open Erdos287.ReciprocalUnitaryFourier
open Erdos287.TransverseBezoutThreeAxis
open Erdos287.TransverseDualPairwise

/-! ## §1  The affine-product numerator map and its pushforward -/

/-- The affine-product numerator `t(Δ,ℓ) = Δ · Ξ'(ℓ)` in `ZMod M'`. -/
noncomputable def numerator (MP : ℕ) (XiP : ℤ → ℤ) (p : ZMod MP × ℤ) : ZMod MP :=
  p.1 * ((XiP p.2 : ℤ) : ZMod MP)

/-- The aggregate `A_t = ∑_{(Δ,ℓ) : t(Δ,ℓ) = t} a_{Δ,ℓ}`. -/
noncomputable def numeratorAggregate (MP : ℕ) (XiP : ℤ → ℤ) (s : Finset (ZMod MP × ℤ))
    (a : ZMod MP × ℤ → ℂ) (t : ZMod MP) : ℂ :=
  fiberAggregate s (numerator MP XiP) a t

/-- **`affineProduct_pushforward`.**  `LEAN_PROVED`.  Unconditional finite algebra: the dual
operator equals its pushforward along the affine-product numerator map,

`∑_{(Δ,ℓ)} ∑_{r₀} a_{Δ,ℓ} c_{r₀} e_{M'}(t(Δ,ℓ) · r₀⁻¹) = ∑_t ∑_{r₀} A_t c_{r₀} e_{M'}(t · r₀⁻¹)`. -/
theorem affineProduct_pushforward {MP : ℕ} [NeZero MP] (XiP : ℤ → ℤ)
    (s : Finset (ZMod MP × ℤ)) (sR : Finset ℕ) (a : ZMod MP × ℤ → ℂ) (c : ℕ → ℂ) :
    ∑ p ∈ s, ∑ r ∈ sR, a p * c r *
        ZMod.stdAddChar (numerator MP XiP p * ((r : ℕ) : ZMod MP)⁻¹)
      = ∑ t : ZMod MP, ∑ r ∈ sR, numeratorAggregate MP XiP s a t * c r *
        ZMod.stdAddChar (t * ((r : ℕ) : ZMod MP)⁻¹) := by
  classical
  rw [Finset.sum_comm]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (ZMod MP)))]
  refine Finset.sum_congr rfl ?_
  intro r _
  have := fiberAggregate_sum (x := MP) s (numerator MP XiP) (fun p => a p * c r)
    (fun v => ZMod.stdAddChar (v * ((r : ℕ) : ZMod MP)⁻¹))
  calc ∑ p ∈ s, a p * c r * ZMod.stdAddChar (numerator MP XiP p * ((r : ℕ) : ZMod MP)⁻¹)
      = ∑ v : ZMod MP, fiberAggregate s (numerator MP XiP) (fun p => a p * c r) v *
          ZMod.stdAddChar (v * ((r : ℕ) : ZMod MP)⁻¹) := this
    _ = ∑ t : ZMod MP, numeratorAggregate MP XiP s a t * c r *
          ZMod.stdAddChar (t * ((r : ℕ) : ZMod MP)⁻¹) := by
        refine Finset.sum_congr rfl ?_
        intro v _
        have hagg : fiberAggregate s (numerator MP XiP) (fun p => a p * c r) v
            = numeratorAggregate MP XiP s a v * c r := by
          unfold fiberAggregate numeratorAggregate
          exact (Finset.sum_mul _ _ _).symm
        rw [hagg]

/-- **`affineProduct_collision_iff`.**  `LEAN_PROVED`.  The exact collision equation: two source
pairs collide in the numerator map iff `Δ₁ Ξ'(ℓ₁) ≡ Δ₂ Ξ'(ℓ₂) (mod M')`.  No energy bound is
asserted. -/
theorem affineProduct_collision_iff (MP : ℕ) (XiP : ℤ → ℤ) (D₁ D₂ : ZMod MP) (e₁ e₂ : ℤ) :
    numerator MP XiP (D₁, e₁) = numerator MP XiP (D₂, e₂)
      ↔ D₁ * ((XiP e₁ : ℤ) : ZMod MP) = D₂ * ((XiP e₂ : ℤ) : ZMod MP) := Iff.rfl

/-! ## §2  The affine-product energy interface -/

/-- Explicit interface for the source-specific modular-hyperbola (Cochrane–Shi type) energy of
the affine-product numerator.  `Kenergy` is an explicit parameter; nothing here evaluates it, and
no divisor/`8^ω(M)`/`log³M` shape is hard-coded. -/
def AffineProductEnergyBound {MP : ℕ} [NeZero MP] (XiP : ℤ → ℤ) (s : Finset (ZMod MP × ℤ))
    (a : ZMod MP × ℤ → ℂ) (Kenergy : ℝ) : Prop :=
  ∑ t : ZMod MP, ‖numeratorAggregate MP XiP s a t‖ ^ 2 ≤ Kenergy * ∑ p ∈ s, ‖a p‖ ^ 2

/-- **`affineProductEnergy_not_automatic`.**  `LEAN_PROVED`.  The energy interface is a genuine
hypothesis: there are finite data violating it.  It is therefore neither vacuous nor derivable by
pure logic, and it is **not** proved anywhere in this repository. -/
theorem affineProductEnergy_not_automatic :
    ∃ (MP : ℕ) (_ : NeZero MP) (XiP : ℤ → ℤ) (s : Finset (ZMod MP × ℤ))
      (a : ZMod MP × ℤ → ℂ) (K : ℝ),
      ¬ AffineProductEnergyBound (MP := MP) XiP s a K := by
  refine ⟨1, ⟨one_ne_zero⟩, fun _ => 0, {(0, 0)}, fun _ => 1, -1, ?_⟩
  intro h
  simp only [AffineProductEnergyBound, numeratorAggregate, fiberAggregate, numerator] at h
  simp at h
  split_ifs at h <;> norm_num at h

/-- **`dualAffineProductFourier_of_energy`.**  `LEAN_PROVED (CONDITIONAL)`.  The conditional dual
compiler.  Given

* an explicit fibre bound `Kr` for `r₀ ↦ r₀⁻¹` on the `r₀`-support, and
* the explicit affine-product energy hypothesis with constant `Kenergy`,

the dual operator obeys the explicit finite inequality

`‖∑_{(Δ,ℓ),r₀} a c e_{M'}(Δ Ξ'(ℓ) r₀⁻¹)‖² ≤ M' (Kenergy ∑‖a‖²)(K_r ∑‖c‖²)`.

Both inputs are explicit named hypotheses; no asymptotic closure statement is made. -/
theorem dualAffineProductFourier_of_energy {MP : ℕ} [NeZero MP] (XiP : ℤ → ℤ)
    (s : Finset (ZMod MP × ℤ)) (sR : Finset ℕ) (a : ZMod MP × ℤ → ℂ) (c : ℕ → ℂ)
    (Kenergy Kr : ℝ)
    (hfibR : ∀ w : ZMod MP, ((sR.filter (fun r => ((r : ℕ) : ZMod MP)⁻¹ = w)).card : ℝ) ≤ Kr)
    (hE : AffineProductEnergyBound (MP := MP) XiP s a Kenergy) :
    ‖∑ p ∈ s, ∑ r ∈ sR, a p * c r *
        ZMod.stdAddChar (numerator MP XiP p * ((r : ℕ) : ZMod MP)⁻¹)‖ ^ 2
      ≤ (MP : ℝ) * (Kenergy * ∑ p ∈ s, ‖a p‖ ^ 2) * (Kr * ∑ r ∈ sR, ‖c r‖ ^ 2) := by
  classical
  rw [affineProduct_pushforward XiP s sR a c]
  have hbound := doubleAggregatedFourier_bound (x := MP) (Finset.univ : Finset (ZMod MP)) sR
    (fun t : ZMod MP => t) (fun r : ℕ => ((r : ℕ) : ZMod MP)⁻¹)
    (fun t => numeratorAggregate MP XiP s a t) c 1 Kr zero_le_one ?_ hfibR
  · refine hbound.trans ?_
    have hR : (0 : ℝ) ≤ Kr * ∑ r ∈ sR, ‖c r‖ ^ 2 := by
      have h0 : (0 : ℝ) ≤ ∑ w : ZMod MP,
          ‖fiberAggregate sR (fun r : ℕ => ((r : ℕ) : ZMod MP)⁻¹) c w‖ ^ 2 :=
        Finset.sum_nonneg fun _ _ => by positivity
      exact le_trans h0 (fiberAggregate_l2_le_maxFiber sR _ c Kr hfibR)
    have hmain : (MP : ℝ) * (1 * ∑ t : ZMod MP, ‖numeratorAggregate MP XiP s a t‖ ^ 2)
        ≤ (MP : ℝ) * (Kenergy * ∑ p ∈ s, ‖a p‖ ^ 2) := by
      have := hE
      simp only [AffineProductEnergyBound] at this
      have hMP : (0 : ℝ) ≤ (MP : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left (by simpa using this) hMP
    exact mul_le_mul_of_nonneg_right hmain hR
  · intro v
    have : ((Finset.univ : Finset (ZMod MP)).filter (fun t : ZMod MP => t = v)).card ≤ 1 := by
      refine Finset.card_le_one.mpr ?_
      intro x hx y hy
      simp only [Finset.mem_filter] at hx hy
      rw [hx.2, hy.2]
    exact_mod_cast this

/-! ## §3  The weighted `Ω` divisor-moment pin -/

/-- The weighted `Ω` divisor-moment norm required by the affine-product energy compiler:

`N_{Ω,C} = ∑_E |Ω_E|² C(E)/E² ≤ K`.

This is a **pin**: no theorem of this repository proves it, and it is *not* the ordinary `ℓ²`
normalisation. -/
def OmegaWeightedDivisorMomentBound (sE : Finset ℕ) (Omega : ℕ → ℂ) (Cw : ℕ → ℝ) (K : ℝ) : Prop :=
  ∑ E ∈ sE, ‖Omega E‖ ^ 2 * Cw E / (E : ℝ) ^ 2 ≤ K

/-- **`omegaWeighted_not_implied_by_l2`.**  `LEAN_PROVED`.  Semantic firewall: an ordinary `ℓ²`
bound on `Ω` does **not** imply the weighted divisor-moment bound.  Explicit witness: one term
with `‖Ω‖² = 1`, weight `C(E) = 8` and `E = 1` satisfies `∑‖Ω‖² ≤ 1` but violates
`N_{Ω,C} ≤ 1`.  Hence the two source pins must stay separate. -/
theorem omegaWeighted_not_implied_by_l2 :
    ∃ (sE : Finset ℕ) (Omega : ℕ → ℂ) (Cw : ℕ → ℝ),
      (∑ E ∈ sE, ‖Omega E‖ ^ 2 ≤ 1) ∧ ¬ OmegaWeightedDivisorMomentBound sE Omega Cw 1 := by
  refine ⟨{1}, fun _ => 1, fun _ => 8, by norm_num, ?_⟩
  intro h
  simp only [OmegaWeightedDivisorMomentBound] at h
  norm_num at h

/-- **`omegaWeighted_satisfiable`.**  `LEAN_PROVED`.  The weighted pin is not contradictory. -/
theorem omegaWeighted_satisfiable :
    OmegaWeightedDivisorMomentBound (∅ : Finset ℕ) (fun _ => 0) (fun _ => 0) 0 := by
  simp [OmegaWeightedDivisorMomentBound]

/-! ## §4  The literal simultaneous-critical residual -/

/-- The literal source-specific residual packet of the current frontier.  The arithmetic slots
are concrete data; the analytic slots are **unfilled `Prop`s** — no field is populated with a
proof, and nothing in this repository provides one. -/
structure SimultaneousCriticalPacket where
  /-- The conductor component `m`. -/
  m : ℕ
  /-- The `q`-component. -/
  q : ℕ
  /-- The reduced `r`-component `r₀`. -/
  r0 : ℕ
  /-- The `Δ₀`-range. -/
  D0range : ℕ
  /-- The `ℓ`-range. -/
  ellRange : ℕ
  /-- The `r₀`-range. -/
  r0Range : ℕ
  /-- The affine constant of `Ξ`. -/
  XiConst : ℤ
  /-- The affine slope of `Ξ`. -/
  XiSlope : ℤ
  /-- The Bézout packet gcd. -/
  g : ℕ
  /-- The variable `Ξ`-gcd of the packet. -/
  dXi : ℕ
  /-- The `(Δ,ℓ)`-coefficient vector. -/
  aCoeff : ℤ × ℤ → ℂ
  /-- The `r₀`-coefficient vector. -/
  cCoeff : ℕ → ℂ
  /-- The outer Möbius level coefficient.  It is **linear** and no cancellation is claimed. -/
  mobiusLevel : ℕ → ℂ
  /-- Source normalisation hypothesis: an unfilled proposition. -/
  sourceNormalisation : Prop
  /-- Old-density critical condition: an unfilled proposition. -/
  oldDensityCritical : Prop
  /-- Dual-density critical condition: an unfilled proposition. -/
  dualDensityCritical : Prop

/-- **`simultaneousCriticalPacket_fields_unfilled`.**  `LEAN_PROVED`.  The three analytic fields
are genuinely unfilled: a packet may carry `False` in each of them, so no theorem can extract a
proof of any of them from the mere existence of a packet. -/
theorem simultaneousCriticalPacket_fields_unfilled :
    ∃ P : SimultaneousCriticalPacket,
      P.sourceNormalisation = False ∧ P.oldDensityCritical = False ∧
        P.dualDensityCritical = False :=
  ⟨{ m := 1, q := 1, r0 := 1, D0range := 1, ellRange := 1, r0Range := 1
     XiConst := 0, XiSlope := 0, g := 1, dXi := 1
     aCoeff := fun _ => 0, cCoeff := fun _ => 0, mobiusLevel := fun _ => 0
     sourceNormalisation := False, oldDensityCritical := False, dualDensityCritical := False },
   rfl, rfl, rfl⟩

end TransverseAffineProduct
end Erdos287
