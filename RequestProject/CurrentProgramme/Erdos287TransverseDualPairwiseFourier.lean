import Mathlib
import RequestProject.CurrentProgramme.Erdos287TransverseDualLevelXiReduction

/-!
# Dual pairwise finite Fourier bounds — Erdős #287 (append-only)

This module is **append-only**.  It adds:

* the dual frequency map `f_dual(ℓ,r₀) = Ξ'(ℓ) · r₀⁻¹ (mod M')` and its two exact
  residue-uniqueness statements (one in `r₀` for fixed `ℓ`, one in `ℓ` for fixed `r₀`), each
  under an explicit unit hypothesis;
* the two exact interval fibre bounds and the resulting `min` form;
* a general **double-aggregated** finite Fourier inequality, and the three pairwise instances
  `Δ × r₀`, `Δ × ℓ`, `ℓ × r₀`, in each of which the third source coordinate is absorbed into a
  coefficient vector;
* the exact normalisation identity `M'(1+D₀/M')(1+R₀/M')/(D₀R₀) = M'/(D₀R₀)+1/D₀+1/R₀+1/M'`;
* the **no-double-spending firewall** `dualPairwise_min_bound`: alternative valid bounds may be
  minimised, never multiplied.

All Fourier content is the already-banked finite Gram machinery; no new Fourier proof and no
asymptotic claim occurs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace TransverseDualPairwise

open Erdos287.ReciprocalUnitaryFourier
open Erdos287.BalancedBUnitaryFourier
open Erdos287.TransverseBezoutThreeAxis
open Erdos287.TransverseBezoutRow

/-! ## §1  The general double-aggregated finite Fourier inequality -/

/-- **`doubleAggregatedFourier_bound`.**  `LEAN_PROVED`.  Both axes are arbitrary finite index
sets carrying arbitrary coefficients, coupled only through two frequency maps `F`, `G`:

`‖∑_{i,j} a_i b_j e_x(F(i) G(j))‖² ≤ x (K₁ ∑‖a‖²)(K₂ ∑‖b‖²)`,

where `K₁`, `K₂` bound the fibres of `F` and `G`.  Proof: fibre aggregation on both axes plus the
banked Fourier Gram identity. -/
theorem doubleAggregatedFourier_bound {ι κ : Type*} {x : ℕ} [NeZero x]
    (s : Finset ι) (t : Finset κ) (F : ι → ZMod x) (G : κ → ZMod x)
    (a : ι → ℂ) (b : κ → ℂ) (K₁ K₂ : ℝ) (hK₁0 : 0 ≤ K₁)
    (hK₁ : ∀ v : ZMod x, ((s.filter (fun i => F i = v)).card : ℝ) ≤ K₁)
    (hK₂ : ∀ w : ZMod x, ((t.filter (fun j => G j = w)).card : ℝ) ≤ K₂) :
    ‖∑ i ∈ s, ∑ j ∈ t, a i * b j * ZMod.stdAddChar (F i * G j)‖ ^ 2
      ≤ (x : ℝ) * (K₁ * ∑ i ∈ s, ‖a i‖ ^ 2) * (K₂ * ∑ j ∈ t, ‖b j‖ ^ 2) := by
  classical
  set A : ZMod x → ℂ := fun v => fiberAggregate s F a v with hA
  set B : ZMod x → ℂ := fun w => fiberAggregate t G b w with hB
  have hinner : ∀ i, ∑ j ∈ t, b j * ZMod.stdAddChar (F i * G j)
      = ∑ w : ZMod x, B w * ZMod.stdAddChar (F i * w) := by
    intro i
    exact fiberAggregate_sum t G b (fun w => ZMod.stdAddChar (F i * w))
  have hrw : ∑ i ∈ s, ∑ j ∈ t, a i * b j * ZMod.stdAddChar (F i * G j)
      = ∑ v : ZMod x, ∑ w : ZMod x, A v * B w * unitaryFourierKernel (1 : ZMod x) v w := by
    have h1 : ∑ i ∈ s, ∑ j ∈ t, a i * b j * ZMod.stdAddChar (F i * G j)
        = ∑ i ∈ s, a i * (∑ w : ZMod x, B w * ZMod.stdAddChar (F i * w)) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← hinner i, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have h2 : ∑ i ∈ s, a i * (∑ w : ZMod x, B w * ZMod.stdAddChar (F i * w))
        = ∑ v : ZMod x, A v * (∑ w : ZMod x, B w * ZMod.stdAddChar (v * w)) :=
      fiberAggregate_sum s F a (fun u => ∑ w : ZMod x, B w * ZMod.stdAddChar (u * w))
    rw [h1, h2]
    refine Finset.sum_congr rfl ?_
    intro v _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro w _
    simp [unitaryFourierKernel]
    ring
  rw [hrw]
  refine (unitaryFourier_bilinear_bound (x := x) isUnit_one A B).trans ?_
  have hA2 : ∑ v : ZMod x, ‖A v‖ ^ 2 ≤ K₁ * ∑ i ∈ s, ‖a i‖ ^ 2 :=
    fiberAggregate_l2_le_maxFiber s F a K₁ hK₁
  have hB2 : ∑ w : ZMod x, ‖B w‖ ^ 2 ≤ K₂ * ∑ j ∈ t, ‖b j‖ ^ 2 :=
    fiberAggregate_l2_le_maxFiber t G b K₂ hK₂
  have hxnn : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hB2nn : (0 : ℝ) ≤ ∑ w : ZMod x, ‖B w‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hK2nn : (0 : ℝ) ≤ K₂ * ∑ j ∈ t, ‖b j‖ ^ 2 := le_trans hB2nn hB2
  have h1 : (x : ℝ) * (∑ v : ZMod x, ‖A v‖ ^ 2) ≤ (x : ℝ) * (K₁ * ∑ i ∈ s, ‖a i‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hA2 hxnn
  exact mul_le_mul h1 hB2 hB2nn (by positivity)

/-! ## §2  The dual frequency map -/

/-- The dual frequency map `f_dual(ℓ, r₀) = Ξ'(ℓ) · r₀⁻¹` in `ZMod M'`. -/
noncomputable def fDual (MP : ℕ) (XiP : ℤ → ℤ) (ell : ℤ) (r : ℕ) : ZMod MP :=
  ((XiP ell : ℤ) : ZMod MP) * ((r : ℕ) : ZMod MP)⁻¹

/-- **`fDual_r_unique`.**  `LEAN_PROVED`.  For a fixed `ℓ` with `Ξ'(ℓ)` invertible mod `M'`, the
`r₀`-fibre of the dual frequency map is a single residue class: two unit values of `r₀` giving
the same frequency are equal in `ZMod M'`. -/
theorem fDual_r_unique {MP : ℕ} {XiP : ℤ → ℤ} {ell : ℤ} {r r' : ℕ}
    (hXi : IsUnit ((XiP ell : ℤ) : ZMod MP))
    (hr : IsUnit ((r : ℕ) : ZMod MP)) (hr' : IsUnit ((r' : ℕ) : ZMod MP))
    (h : fDual MP XiP ell r = fDual MP XiP ell r') :
    ((r : ℕ) : ZMod MP) = ((r' : ℕ) : ZMod MP) := by
  obtain ⟨u, hu⟩ := hXi.exists_left_inv
  have hinv : ((r : ℕ) : ZMod MP)⁻¹ = ((r' : ℕ) : ZMod MP)⁻¹ := by
    have := congrArg (fun z => u * z) h
    simpa [fDual, ← mul_assoc, hu] using this
  calc ((r : ℕ) : ZMod MP) = (((r : ℕ) : ZMod MP)⁻¹)⁻¹ := (zmod_inv_inv_of_isUnit hr).symm
    _ = (((r' : ℕ) : ZMod MP)⁻¹)⁻¹ := by rw [hinv]
    _ = ((r' : ℕ) : ZMod MP) := zmod_inv_inv_of_isUnit hr'

/-- **`fDual_ell_unique`.**  `LEAN_PROVED`.  For a fixed unit `r₀`, and for an affine
`Ξ'(ℓ) = c - s ℓ` whose slope `s` is invertible modulo `M'` (witness supplied), the `ℓ`-fibre is a
single residue class modulo `M'`. -/
theorem fDual_ell_unique {MP : ℕ} {XiP : ℤ → ℤ} {c s : ℤ}
    (haff : ∀ e : ℤ, XiP e = c - s * e) {w : ℤ} (hw : s * w ≡ 1 [ZMOD (MP : ℤ)])
    {r : ℕ} (hr : IsUnit ((r : ℕ) : ZMod MP)) {ell ell' : ℤ}
    (h : fDual MP XiP ell r = fDual MP XiP ell' r) :
    ell ≡ ell' [ZMOD (MP : ℤ)] := by
  have hXi : ((XiP ell : ℤ) : ZMod MP) = ((XiP ell' : ℤ) : ZMod MP) := by
    have := congrArg (fun z => z * ((r : ℕ) : ZMod MP)) h
    simpa [fDual, mul_assoc, ZMod.inv_mul_of_unit _ hr] using this
  have hcong : XiP ell ≡ XiP ell' [ZMOD (MP : ℤ)] := (ZMod.intCast_eq_intCast_iff _ _ _).mp hXi
  have haffc : c + (-s) * ell ≡ c + (-s) * ell' [ZMOD (MP : ℤ)] := by
    have h1 : c + (-s) * ell = XiP ell := by rw [haff]; ring
    have h2 : c + (-s) * ell' = XiP ell' := by rw [haff]; ring
    rw [h1, h2]; exact hcong
  have hwneg : (-s) * (-w) ≡ 1 [ZMOD (MP : ℤ)] := by simpa using hw
  exact affine_residue_unique_of_unit_slope hwneg haffc

/-! ## §3  Exact interval fibre bounds -/

/-- **`card_le_of_fibre_fst`.**  `LEAN_PROVED`.  If every fibre of the first coordinate inside a
finite set of pairs has at most `K` points and the first coordinates lie in `T`, then the set has
at most `K · #T` points. -/
theorem card_le_of_fibre_fst {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset (α × β)) (T : Finset α) (hT : ∀ p ∈ S, p.1 ∈ T) (K : ℕ)
    (hfib : ∀ u : α, (S.filter (fun p => p.1 = u)).card ≤ K) :
    S.card ≤ K * T.card := by
  classical
  have h1 : S.card ≤ K * (S.image Prod.fst).card :=
    Finset.card_le_mul_card_image S K (fun u _ => hfib u)
  have h2 : (S.image Prod.fst).card ≤ T.card := by
    refine Finset.card_le_card ?_
    intro u hu
    simp only [Finset.mem_image] at hu
    obtain ⟨p, hp, rfl⟩ := hu
    exact hT p hp
  exact h1.trans (Nat.mul_le_mul_left _ h2)

/-- **`card_le_of_fibre_snd`.**  `LEAN_PROVED`.  The symmetric statement for the second
coordinate. -/
theorem card_le_of_fibre_snd {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset (α × β)) (T : Finset β) (hT : ∀ p ∈ S, p.2 ∈ T) (K : ℕ)
    (hfib : ∀ u : β, (S.filter (fun p => p.2 = u)).card ≤ K) :
    S.card ≤ K * T.card := by
  classical
  have h1 : S.card ≤ K * (S.image Prod.snd).card :=
    Finset.card_le_mul_card_image S K (fun u _ => hfib u)
  have h2 : (S.image Prod.snd).card ≤ T.card := by
    refine Finset.card_le_card ?_
    intro u hu
    simp only [Finset.mem_image] at hu
    obtain ⟨p, hp, rfl⟩ := hu
    exact hT p hp
  exact h1.trans (Nat.mul_le_mul_left _ h2)

/-- **`dualPairwise_min_of_two_counts`.**  `LEAN_PROVED`.  If a fibre admits the two alternative
counts `H₀ · K_r` and `R₀ · K_ℓ`, it admits their minimum.  This is the exact `min` form used by
the dual level; the two bounds are **alternatives**, never multiplied. -/
theorem dualPairwise_min_of_two_counts {n H0 R0 Kr Kl : ℕ}
    (h₁ : n ≤ H0 * Kr) (h₂ : n ≤ R0 * Kl) : n ≤ min (H0 * Kr) (R0 * Kl) :=
  le_min h₁ h₂

/-- **`fDual_r_fibre_interval_count`.**  `LEAN_PROVED`.  Fixing `ℓ` with `Ξ'(ℓ)` invertible, an
interval of length `R₀` meets a dual-frequency fibre in at most `R₀ / M' + 1` points (exact
`ℕ`-division). -/
theorem fDual_r_fibre_interval_count {MP : ℕ} (hM : 0 < MP) (XiP : ℤ → ℤ) (ell : ℤ)
    (hXi : IsUnit ((XiP ell : ℤ) : ZMod MP)) (aR R0 : ℕ) (v : ZMod MP)
    (hunit : ∀ r ∈ Finset.Ico aR (aR + R0), IsUnit ((r : ℕ) : ZMod MP)) :
    ((Finset.Ico aR (aR + R0)).filter (fun r : ℕ => fDual MP XiP ell r = v)).card
      ≤ R0 / MP + 1 := by
  classical
  rcases Finset.eq_empty_or_nonempty
      ((Finset.Ico aR (aR + R0)).filter (fun r : ℕ => fDual MP XiP ell r = v)) with he | ⟨r₀, hr₀⟩
  · simp [he]
  · have hsub : (Finset.Ico aR (aR + R0)).filter (fun r : ℕ => fDual MP XiP ell r = v) ⊆
        (Finset.Ico aR (aR + R0)).filter
          (fun r : ℕ => ((r : ℕ) : ZMod MP) = ((r₀ : ℕ) : ZMod MP)) := by
      intro r hr
      simp only [Finset.mem_filter] at hr hr₀ ⊢
      exact ⟨hr.1, fDual_r_unique hXi (hunit r hr.1) (hunit r₀ hr₀.1) (by rw [hr.2, hr₀.2])⟩
    exact le_trans (Finset.card_le_card hsub)
      (Erdos287.BalancedBUnitaryFourier.interval_residue_fibre_card_le MP hM aR R0 _)

/-- **`fDual_ell_fibre_interval_count`.**  `LEAN_PROVED`.  Fixing a unit `r₀` and an affine `Ξ'`
with invertible slope, an interval of length `H₀` of `ℓ`-values meets a dual-frequency fibre in at
most `H₀ / M' + 1` points. -/
theorem fDual_ell_fibre_interval_count {MP : ℕ} (hM : 0 < MP) {XiP : ℤ → ℤ} {c s : ℤ}
    (haff : ∀ e : ℤ, XiP e = c - s * e) {w : ℤ} (hw : s * w ≡ 1 [ZMOD (MP : ℤ)])
    {r : ℕ} (hr : IsUnit ((r : ℕ) : ZMod MP)) (aE H0 : ℕ) (v : ZMod MP) :
    ((Finset.Ico aE (aE + H0)).filter (fun e : ℕ => fDual MP XiP (e : ℤ) r = v)).card
      ≤ H0 / MP + 1 := by
  classical
  rcases Finset.eq_empty_or_nonempty
      ((Finset.Ico aE (aE + H0)).filter (fun e : ℕ => fDual MP XiP (e : ℤ) r = v))
    with he | ⟨e₀, he₀⟩
  · simp [he]
  · have hsub : (Finset.Ico aE (aE + H0)).filter (fun e : ℕ => fDual MP XiP (e : ℤ) r = v) ⊆
        (Finset.Ico aE (aE + H0)).filter
          (fun e : ℕ => ((e : ℕ) : ZMod MP) = ((e₀ : ℕ) : ZMod MP)) := by
      intro e he
      simp only [Finset.mem_filter] at he he₀ ⊢
      refine ⟨he.1, ?_⟩
      have hcong : (e : ℤ) ≡ (e₀ : ℤ) [ZMOD (MP : ℤ)] :=
        fDual_ell_unique haff hw hr (by rw [he.2, he₀.2])
      have hz : ((e : ℤ) : ZMod MP) = ((e₀ : ℤ) : ZMod MP) :=
        (ZMod.intCast_eq_intCast_iff _ _ _).mpr hcong
      simpa using hz
    exact le_trans (Finset.card_le_card hsub)
      (Erdos287.BalancedBUnitaryFourier.interval_residue_fibre_card_le MP hM aE H0 _)

/-! ## §4  The three pairwise finite Fourier bounds -/

variable {MP : ℕ}

/-- **`dualPairwise_Delta_r_bound`.**  `LEAN_PROVED`.  Pairing **A** (`Δ` versus `r₀`), with the
`ℓ`-coordinate absorbed into the `r₀`-coefficient vector.  `K_r` bounds the fibres of
`r₀ ↦ t · r₀⁻¹`. -/
theorem dualPairwise_Delta_r_bound [NeZero MP] (sD : Finset (ZMod MP)) (sR : Finset ℕ)
    (t : ZMod MP) (a : ZMod MP → ℂ) (c : ℕ → ℂ) (Kr : ℝ)
    (hfib : ∀ w : ZMod MP,
      ((sR.filter (fun r => t * ((r : ℕ) : ZMod MP)⁻¹ = w)).card : ℝ) ≤ Kr) :
    ‖∑ Δ ∈ sD, ∑ r ∈ sR, a Δ * c r *
        ZMod.stdAddChar (Δ * (t * ((r : ℕ) : ZMod MP)⁻¹))‖ ^ 2
      ≤ (MP : ℝ) * (1 * ∑ Δ ∈ sD, ‖a Δ‖ ^ 2) * (Kr * ∑ r ∈ sR, ‖c r‖ ^ 2) := by
  classical
  refine doubleAggregatedFourier_bound sD sR (fun D => D)
    (fun r => t * ((r : ℕ) : ZMod MP)⁻¹) a c 1 Kr zero_le_one ?_ hfib
  intro v
  have : (sD.filter (fun D : ZMod MP => D = v)).card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro x hx y hy
    simp only [Finset.mem_filter] at hx hy
    rw [hx.2, hy.2]
  exact_mod_cast this

/-- **`dualPairwise_Delta_ell_bound`.**  `LEAN_PROVED`.  Pairing **B** (`Δ` versus `ℓ`), with the
`r₀`-coordinate absorbed into the `ℓ`-coefficient vector; `Kl` bounds the fibres of
`ℓ ↦ Ξ'(ℓ) r₀⁻¹`. -/
theorem dualPairwise_Delta_ell_bound [NeZero MP] (sD : Finset (ZMod MP)) (sL : Finset ℤ)
    (XiP : ℤ → ℤ) (r : ℕ) (a : ZMod MP → ℂ) (b : ℤ → ℂ) (Kl : ℝ)
    (hfib : ∀ w : ZMod MP,
      ((sL.filter (fun ell => fDual MP XiP ell r = w)).card : ℝ) ≤ Kl) :
    ‖∑ Δ ∈ sD, ∑ ell ∈ sL, a Δ * b ell *
        ZMod.stdAddChar (Δ * fDual MP XiP ell r)‖ ^ 2
      ≤ (MP : ℝ) * (1 * ∑ Δ ∈ sD, ‖a Δ‖ ^ 2) * (Kl * ∑ ell ∈ sL, ‖b ell‖ ^ 2) := by
  classical
  refine doubleAggregatedFourier_bound sD sL (fun D => D)
    (fun ell => fDual MP XiP ell r) a b 1 Kl zero_le_one ?_ hfib
  intro v
  have : (sD.filter (fun D : ZMod MP => D = v)).card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro x hx y hy
    simp only [Finset.mem_filter] at hx hy
    rw [hx.2, hy.2]
  exact_mod_cast this

/-- **`dualPairwise_ell_r_bound`.**  `LEAN_PROVED`.  Pairing **C** (`ℓ` versus `r₀`), with the
`Δ`-coordinate absorbed into the frequency of the `ℓ`-axis; `Kl`, `Kr` bound the two fibre
families. -/
theorem dualPairwise_ell_r_bound [NeZero MP] (sL : Finset ℤ) (sR : Finset ℕ)
    (XiP : ℤ → ℤ) (Δ : ZMod MP) (b : ℤ → ℂ) (c : ℕ → ℂ) (Kl Kr : ℝ) (hKl : 0 ≤ Kl)
    (hfibL : ∀ v : ZMod MP,
      ((sL.filter (fun ell => Δ * ((XiP ell : ℤ) : ZMod MP) = v)).card : ℝ) ≤ Kl)
    (hfibR : ∀ w : ZMod MP,
      ((sR.filter (fun r => ((r : ℕ) : ZMod MP)⁻¹ = w)).card : ℝ) ≤ Kr) :
    ‖∑ ell ∈ sL, ∑ r ∈ sR, b ell * c r *
        ZMod.stdAddChar ((Δ * ((XiP ell : ℤ) : ZMod MP)) * ((r : ℕ) : ZMod MP)⁻¹)‖ ^ 2
      ≤ (MP : ℝ) * (Kl * ∑ ell ∈ sL, ‖b ell‖ ^ 2) * (Kr * ∑ r ∈ sR, ‖c r‖ ^ 2) :=
  doubleAggregatedFourier_bound sL sR (fun ell => Δ * ((XiP ell : ℤ) : ZMod MP))
    (fun r => ((r : ℕ) : ZMod MP)⁻¹) b c Kl Kr hKl hfibL hfibR

/-! ## §5  Packetwise minimum: the no-double-spending firewall -/

/-- **`dualPairwise_min_bound`.**  `LEAN_PROVED`.  If three alternative valid bounds are
available for the same quantity, the packet may use their **minimum**.  Recorded as the formal
no-double-spending firewall: the alternatives are never multiplied. -/
theorem dualPairwise_min_bound {X b₁ b₂ b₃ : ℝ} (h₁ : X ≤ b₁) (h₂ : X ≤ b₂) (h₃ : X ≤ b₃) :
    X ≤ min b₁ (min b₂ b₃) :=
  le_min h₁ (le_min h₂ h₃)

/-- **`dualPairwise_min_is_not_product`.**  `LEAN_PROVED`.  Explicit countermodel: the minimum of
two alternative bounds is in general **not** their product, so no theorem may silently replace
the `min` firewall by a multiplicative gain. -/
theorem dualPairwise_min_is_not_product :
    ∃ b₁ b₂ : ℝ, min b₁ b₂ ≠ b₁ * b₂ := by
  refine ⟨2, 2, ?_⟩
  norm_num

/-! ## §6  The exact dual normalisation identity -/

/-- **`dualPairwise_contraction_identity`.**  `LEAN_PROVED`.  The exact identity behind the
requested finite expression:

`M' (1 + D₀/M') (1 + R₀/M') / (D₀ R₀) = M'/(D₀R₀) + 1/D₀ + 1/R₀ + 1/M'`,

for positive reals.  Identity only: no saving is asserted. -/
theorem dualPairwise_contraction_identity (MP' D0 R0 : ℝ) (hM : 0 < MP') (hD : 0 < D0)
    (hR : 0 < R0) :
    MP' * (1 + D0 / MP') * (1 + R0 / MP') / (D0 * R0)
      = MP' / (D0 * R0) + 1 / D0 + 1 / R0 + 1 / MP' := by
  field_simp
  ring

/-- **`dualPairwise_contraction_identity_symmetric`.**  `LEAN_PROVED`.  The symmetric variant
with `H₀` in place of `R₀`. -/
theorem dualPairwise_contraction_identity_symmetric (MP' D0 H0 : ℝ) (hM : 0 < MP') (hD : 0 < D0)
    (hH : 0 < H0) :
    MP' * (1 + D0 / MP') * (1 + H0 / MP') / (D0 * H0)
      = MP' / (D0 * H0) + 1 / D0 + 1 / H0 + 1 / MP' := by
  field_simp
  ring

end TransverseDualPairwise
end Erdos287
