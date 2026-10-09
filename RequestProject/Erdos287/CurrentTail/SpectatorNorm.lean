import RequestProject.Erdos287.CurrentTail.RelativeBDH

/-!
# Erdős #287 — current tail consolidation: spectator reciprocal-density norm and the RBDH
family payment

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

## Finite combinatorics (kernel-proved)

* `CoordState` — the coordinate states `first | second | both`;
* `TensorState K` — a `K`-coordinate tensor state: a coordinate state and a positive
  (root/fixed-local) label per coordinate; its spectator modulus is the product of labels;
* `card_fibre_le` — **divisor-power preimage bound**: at most `3^K τ(F)^K` tensor states have
  spectator modulus `F`;
* `fibre_regroup` — exact regrouping of a packet sum by spectator modulus;
* `spectator_norm_finite` —
  `∑_ξ |Γ_ξ| τ(f_ξ)^D / φ(f_ξ) ≤ G · 3^K · ∑_{F} τ(F)^{D+K} / φ(F)`  when `|Γ_ξ| ≤ G`.

## Analytic estimate (isolated)

* `ReciprocalDivisorMoment E X C` — the *only* analytic input: `∑_{F ≤ X} τ(F)^E/φ(F) ≤ C`
  (classically `C ≍ (log X)^{2^E}`); `spectator_norm_of_moment` combines.

## RBDH family payment (kernel-proved Cauchy routing)

* `family_payment` — `∑_ξ g_ξ M √(R_ξ/φ_ξ) ≤ M √(∑ g_ξ/φ_ξ) √(∑ g_ξ R_ξ)`;
* `fibre_weight_transport` — `∑_ξ g_ξ R(f_ξ) ≤ ∑_F τ(F)^C R(F)` when fibre weights `≤ τ^C`;
* `family_payment_tau` — the combined statement
  `∑_ξ |Γ_ξ| M (R(f_ξ)/φ(f_ξ))^{1/2} ≤ M (∑_ξ |Γ_ξ|/φ(f_ξ))^{1/2} (∑_F τ(F)^C R(F))^{1/2}`.
  No packetwise multiplication by the packet population is used.
-/

open scoped BigOperators
open Finset

namespace Erdos287.CurrentTail

/-- Coordinate states of a tensor packet. -/
inductive CoordState
  | first
  | second
  | both
  deriving DecidableEq, Fintype

theorem card_coordState : Fintype.card CoordState = 3 := rfl

/-- A `K`-coordinate tensor state: coordinate state and label for each coordinate. -/
abbrev TensorState (K : ℕ) := Fin K → CoordState × ℕ

/-- The spectator modulus of a tensor state: the product of its labels. -/
def spectatorModulus {K : ℕ} (ξ : TensorState K) : ℕ := ∏ i, (ξ i).2

/-- `τ(F)`. -/
abbrev tau (F : ℕ) : ℕ := (Nat.divisors F).card

/-- **Divisor-power preimage bound.**  Among tensor states with positive labels, at most
`3^K · τ(F)^K` have spectator modulus `F > 0`. -/
theorem card_fibre_le {K : ℕ} (Xi : Finset (TensorState K)) {F : ℕ} (hF : 0 < F) :
    (Xi.filter (fun ξ => spectatorModulus ξ = F)).card ≤ 3 ^ K * tau F ^ K := by
  classical
  let tgt : Finset ((Fin K → CoordState) × (Fin K → ℕ)) :=
    (Finset.univ : Finset (Fin K → CoordState)) ×ˢ Fintype.piFinset (fun _ => Nat.divisors F)
  have htgt : tgt.card = 3 ^ K * tau F ^ K := by
    simp [tgt, Finset.card_product, Fintype.card_piFinset, Finset.card_univ,
      card_coordState]
  rw [← htgt]
  refine Finset.card_le_card_of_injOn (fun ξ => (fun i => (ξ i).1, fun i => (ξ i).2)) ?_ ?_
  · intro ξ hξ
    have hξ' : spectatorModulus ξ = F := (Finset.mem_filter.1 hξ).2
    simp only [tgt, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ, true_and,
      Fintype.mem_piFinset, Nat.mem_divisors]
    intro i
    refine ⟨?_, hF.ne'⟩
    rw [← hξ']
    exact Finset.dvd_prod_of_mem (fun j => (ξ j).2) (Finset.mem_univ i)
  · intro ξ _ η _ h
    simp only [Prod.mk.injEq] at h
    funext i
    exact Prod.ext (congrFun h.1 i) (congrFun h.2 i)

/-- **Fibre regrouping** of a packet sum by spectator modulus. -/
theorem fibre_regroup {ι : Type*} (Xi : Finset ι) (f : ι → ℕ) (g : ι → ℝ) (H : ℕ → ℝ) :
    ∑ ξ ∈ Xi, g ξ * H (f ξ) =
      ∑ F ∈ Xi.image f, (∑ ξ ∈ Xi.filter (fun ξ => f ξ = F), g ξ) * H F := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := Xi) (t := Xi.image f) (g := f)
    (fun ξ hξ => Finset.mem_image_of_mem f hξ)]
  refine Finset.sum_congr rfl (fun F _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun ξ hξ => ?_)
  rw [(Finset.mem_filter.1 hξ).2]

/-- **Finite spectator reciprocal-density norm.** -/
theorem spectator_norm_finite {K D : ℕ} (Xi : Finset (TensorState K)) (Γ : TensorState K → ℝ)
    {G : ℝ} (hΓ : ∀ ξ ∈ Xi, |Γ ξ| ≤ G) (hpos : ∀ ξ ∈ Xi, 0 < spectatorModulus ξ) :
    ∑ ξ ∈ Xi, |Γ ξ| * ((tau (spectatorModulus ξ) : ℝ) ^ D /
        (Nat.totient (spectatorModulus ξ) : ℝ)) ≤
      G * 3 ^ K * ∑ F ∈ Xi.image spectatorModulus,
        (tau F : ℝ) ^ (D + K) / (Nat.totient F : ℝ) := by
  rw [fibre_regroup Xi spectatorModulus (fun ξ => |Γ ξ|)
    (fun F => (tau F : ℝ) ^ D / (Nat.totient F : ℝ)), Finset.mul_sum]
  refine Finset.sum_le_sum (fun F hF => ?_)
  obtain ⟨ξ0, hξ0, rfl⟩ := Finset.mem_image.1 hF
  have hF0 := hpos ξ0 hξ0
  have hnn : 0 ≤ (tau (spectatorModulus ξ0) : ℝ) ^ D /
      (Nat.totient (spectatorModulus ξ0) : ℝ) := by positivity
  have hfib : ∑ ξ ∈ Xi.filter (fun ξ => spectatorModulus ξ = spectatorModulus ξ0), |Γ ξ| ≤
      G * (3 ^ K * (tau (spectatorModulus ξ0) : ℝ) ^ K) := by
    calc _ ≤ ∑ ξ ∈ Xi.filter (fun ξ => spectatorModulus ξ = spectatorModulus ξ0), G :=
          Finset.sum_le_sum (fun ξ hξ => hΓ ξ (Finset.mem_filter.1 hξ).1)
      _ = (Xi.filter (fun ξ => spectatorModulus ξ = spectatorModulus ξ0)).card * G := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (3 ^ K * (tau (spectatorModulus ξ0) : ℝ) ^ K) * G := by
          have hG : 0 ≤ G := le_trans (abs_nonneg _) (hΓ ξ0 hξ0)
          refine mul_le_mul_of_nonneg_right ?_ hG
          exact_mod_cast card_fibre_le Xi hF0
      _ = G * (3 ^ K * (tau (spectatorModulus ξ0) : ℝ) ^ K) := by ring
  calc _ ≤ G * (3 ^ K * (tau (spectatorModulus ξ0) : ℝ) ^ K) *
        ((tau (spectatorModulus ξ0) : ℝ) ^ D / (Nat.totient (spectatorModulus ξ0) : ℝ)) :=
        mul_le_mul_of_nonneg_right hfib hnn
    _ = _ := by rw [pow_add]; ring

/-- **The isolated analytic estimate**: reciprocal divisor moment up to `X` is at most `C`. -/
def ReciprocalDivisorMoment (E X : ℕ) (C : ℝ) : Prop :=
  ∑ F ∈ Finset.Icc 1 X, (tau F : ℝ) ^ E / (Nat.totient F : ℝ) ≤ C

/-- Spectator norm from the isolated analytic estimate. -/
theorem spectator_norm_of_moment {K D X : ℕ} (Xi : Finset (TensorState K))
    (Γ : TensorState K → ℝ) {G C : ℝ} (hG : 0 ≤ G) (hΓ : ∀ ξ ∈ Xi, |Γ ξ| ≤ G)
    (hpos : ∀ ξ ∈ Xi, 0 < spectatorModulus ξ) (hX : ∀ ξ ∈ Xi, spectatorModulus ξ ≤ X)
    (hmom : ReciprocalDivisorMoment (D + K) X C) :
    ∑ ξ ∈ Xi, |Γ ξ| * ((tau (spectatorModulus ξ) : ℝ) ^ D /
        (Nat.totient (spectatorModulus ξ) : ℝ)) ≤ G * 3 ^ K * C := by
  refine (spectator_norm_finite Xi Γ hΓ hpos).trans ?_
  refine mul_le_mul_of_nonneg_left (le_trans ?_ hmom) (by positivity)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
  intro F hF
  obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.1 hF
  exact Finset.mem_Icc.2 ⟨hpos ξ hξ, hX ξ hξ⟩

/-! ### RBDH family payment -/

/-- **Cauchy routing of the family payment.**  For `g, R ≥ 0`, `φ > 0`, `M ≥ 0`:
`∑_ξ g_ξ M √(R_ξ/φ_ξ) ≤ M √(∑ g_ξ/φ_ξ) √(∑ g_ξ R_ξ)`. -/
theorem family_payment {ι : Type*} (Xi : Finset ι) (g R ph : ι → ℝ) (hg : ∀ ξ, 0 ≤ g ξ)
    (hR : ∀ ξ, 0 ≤ R ξ) (hph : ∀ ξ, 0 < ph ξ) {M : ℝ} (hM : 0 ≤ M) :
    ∑ ξ ∈ Xi, g ξ * M * Real.sqrt (R ξ / ph ξ) ≤
      M * Real.sqrt (∑ ξ ∈ Xi, g ξ / ph ξ) * Real.sqrt (∑ ξ ∈ Xi, g ξ * R ξ) := by
  have key : ∀ ξ, g ξ * M * Real.sqrt (R ξ / ph ξ) =
      M * (Real.sqrt (g ξ / ph ξ) * Real.sqrt (g ξ * R ξ)) := by
    intro ξ
    rw [← Real.sqrt_mul (div_nonneg (hg ξ) (hph ξ).le)]
    have : g ξ / ph ξ * (g ξ * R ξ) = g ξ ^ 2 * (R ξ / ph ξ) := by
      field_simp [(hph ξ).ne']
    rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hg ξ)]
    ring
  simp_rw [key]
  rw [← Finset.mul_sum, mul_assoc]
  exact mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le Xi
    (fun ξ => div_nonneg (hg ξ) (hph ξ).le) (fun ξ => mul_nonneg (hg ξ) (hR ξ))) hM

/-- **Fibre weight transport.**  If the packet weight in each fibre `f_ξ = F` is at most
`τ(F)^C`, then `∑_ξ g_ξ R(f_ξ) ≤ ∑_F τ(F)^C R(F)` for `R ≥ 0`. -/
theorem fibre_weight_transport {ι : Type*} (Xi : Finset ι) (f : ι → ℕ) (g : ι → ℝ)
    (R : ℕ → ℝ) (hR : ∀ F, 0 ≤ R F) {C : ℕ}
    (hfib : ∀ F ∈ Xi.image f, ∑ ξ ∈ Xi.filter (fun ξ => f ξ = F), g ξ ≤ (tau F : ℝ) ^ C) :
    ∑ ξ ∈ Xi, g ξ * R (f ξ) ≤ ∑ F ∈ Xi.image f, (tau F : ℝ) ^ C * R F := by
  rw [fibre_regroup]
  exact Finset.sum_le_sum (fun F hF => mul_le_mul_of_nonneg_right (hfib F hF) (hR F))

/-- **RBDH family payment (combined).**
`∑_ξ |Γ_ξ| M (R(f_ξ)/φ(f_ξ))^{1/2} ≤ M (∑_ξ |Γ_ξ|/φ(f_ξ))^{1/2} (∑_F τ(F)^C R(F))^{1/2}`. -/
theorem family_payment_tau {ι : Type*} (Xi : Finset ι) (f : ι → ℕ) (Γ : ι → ℝ)
    (hf : ∀ ξ, 0 < f ξ) (R : ℕ → ℝ) (hR : ∀ F, 0 ≤ R F) {M : ℝ} (hM : 0 ≤ M) {C : ℕ}
    (hfib : ∀ F ∈ Xi.image f, ∑ ξ ∈ Xi.filter (fun ξ => f ξ = F), |Γ ξ| ≤ (tau F : ℝ) ^ C) :
    ∑ ξ ∈ Xi, |Γ ξ| * M * Real.sqrt (R (f ξ) / (Nat.totient (f ξ) : ℝ)) ≤
      M * Real.sqrt (∑ ξ ∈ Xi, |Γ ξ| / (Nat.totient (f ξ) : ℝ)) *
        Real.sqrt (∑ F ∈ Xi.image f, (tau F : ℝ) ^ C * R F) := by
  refine (family_payment Xi (fun ξ => |Γ ξ|) (fun ξ => R (f ξ))
    (fun ξ => (Nat.totient (f ξ) : ℝ)) (fun _ => abs_nonneg _) (fun ξ => hR _)
    (fun ξ => totient_cast_pos (hf ξ)) hM).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
  exact fibre_weight_transport Xi f (fun ξ => |Γ ξ|) R hR hfib

end Erdos287.CurrentTail
