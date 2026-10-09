import RequestProject.Erdos287.ResearchBankV27.FiniteLabelEnergy

/-!
# Erdős #287 — Research Bank V27 §6.3: CRT colour orbit (character-free)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The colour phase is
`Ω_D(o; v₁, h) = 1_{(v₁, D) = 1} · e_D(h · c(o) · v̄₁)`, with
`c(o) = (b − a₀) · (n₁ q₀ d u₁ u₂ v₂)⁻¹ mod D`.
Write `g_D = gcd(D, b − a₀)` and `E_D = D / g_D`.

**LEAN BANK** (no character theory anywhere):
* `dvd_mul_iff_div_gcd` — `D ∣ c t ↔ D / gcd(D, c) ∣ t`;
* **`orbit_card`** — `#{ (b − a₀) v mod D : v ∈ (ℤ/D)ˣ } = φ(E_D)`;
* `orbit_card_le` — `φ(E_D) ≤ D`;
* `colour_mem_orbit` — every colour value `c(o)` lies in the orbit (inverse of a unit is a unit);
* `colourPhase_norm_le` — `|Ω| ≤ 1`, so every label coefficient `Ψ_j = Ψ₀ · Ω(j; ·)` is
  one-bounded and depends only on the inner variables `(v₁, h)`;
* `coloured_eq_labelled` — the coloured sum is literally the finite-label sum with one label per
  orbit element (`κ(o) = c(o)`, an OUTER function);
* **`colour_sqrt_phi_bound`** — a single-label decorated estimate `mass · V(Ψ) ≤ B²`, valid for
  every one-bounded inner `Ψ`, yields `|P| ≤ √φ(E_D) · B ≤ √D · B`.
-/

namespace Erdos287
namespace ResearchBankV27
namespace CRTColourOrbit

open Finset CommonCauchy FiniteLabelEnergy

/-- `D ∣ c t ↔ D / gcd(D, c) ∣ t` (LEAN BANK). -/
theorem dvd_mul_iff_div_gcd {D c t : ℕ} (hD : 0 < D) :
    D ∣ c * t ↔ D / Nat.gcd D c ∣ t := by
  have hg : 0 < Nat.gcd D c := Nat.gcd_pos_of_pos_left _ hD
  have hcop := Nat.coprime_div_gcd_div_gcd hg (m := D) (n := c)
  obtain ⟨E, hE⟩ := Nat.gcd_dvd_left D c
  obtain ⟨c', hc'⟩ := Nat.gcd_dvd_right D c
  set g := Nat.gcd D c
  have hEq : D / g = E := by rw [hE, Nat.mul_div_cancel_left _ hg]
  have hcq : c / g = c' := by rw [hc', Nat.mul_div_cancel_left _ hg]
  rw [hEq] at hcop ⊢; rw [hcq] at hcop
  constructor
  · intro h
    rw [hE, hc', mul_assoc] at h
    have := Nat.dvd_of_mul_dvd_mul_left hg h
    exact hcop.dvd_of_dvd_mul_left this
  · intro h
    rw [hE, hc', mul_assoc]
    exact Nat.mul_dvd_mul_left g (Dvd.dvd.mul_left h _)

/-- The colour orbit `{ t · v mod D : v unit }` (`t` a representative of `b − a₀`). -/
noncomputable def orbit (D t : ℕ) [NeZero D] : Finset (ZMod D) :=
  univ.image fun v : (ZMod D)ˣ => (t : ZMod D) * v

/-- `E_D = D / gcd(D, b − a₀)`. -/
def ED (D t : ℕ) : ℕ := D / Nat.gcd D t

/-- **Orbit cardinality** (LEAN BANK, character-free): `#orbit = φ(E_D)`. -/
theorem orbit_card (D t : ℕ) [NeZero D] : (orbit D t).card = Nat.totient (ED D t) := by
  have hD : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  unfold orbit ED
  set E := D / Nat.gcd D t
  have hEd : E ∣ D := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left D t)
  have hE0 : 0 < E := Nat.div_pos (Nat.gcd_le_left _ hD) (Nat.gcd_pos_of_pos_left _ hD)
  haveI : NeZero E := ⟨hE0.ne'⟩
  let π := ZMod.castHom hEd (ZMod E)
  have key : ∀ v v' : ZMod D, (t : ZMod D) * v = t * v' ↔ π v = π v' := by
    intro v v'
    rw [← sub_eq_zero, ← mul_sub, ← sub_eq_zero (a := π v), ← map_sub]
    set w := v - v'
    have hw : w = ((w.val : ℕ) : ZMod D) := (ZMod.natCast_zmod_val w).symm
    rw [hw, map_natCast, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff, ZMod.natCast_eq_zero_iff]
    exact dvd_mul_iff_div_gcd hD
  let u : (ZMod D)ˣ → (ZMod E)ˣ := ZMod.unitsMap hEd
  have hu : Function.Surjective u := ZMod.unitsMap_surjective hEd
  have hπu : ∀ v, ((u v : ZMod E)) = π v := fun v => rfl
  let lift : (ZMod E)ˣ → (ZMod D)ˣ := fun e => (hu e).choose
  let F : (ZMod E)ˣ → ZMod D := fun e => (t : ZMod D) * (lift e)
  have himg : (univ.image fun v : (ZMod D)ˣ => (t : ZMod D) * v) = univ.image F := by
    ext y; simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨u v, (key _ _).2 ?_⟩
      rw [← hπu, ← hπu, (hu (u v)).choose_spec]
    · rintro ⟨e, rfl⟩; exact ⟨lift e, rfl⟩
  have hinj : Function.Injective F := by
    intro e e' h
    have := (key _ _).1 h
    rw [← hπu, ← hπu, (hu e).choose_spec, (hu e').choose_spec] at this
    exact Units.ext this
  rw [himg, card_image_of_injective _ hinj, card_univ, ZMod.card_units_eq_totient]

/-- `φ(E_D) ≤ D` (LEAN BANK). -/
theorem orbit_card_le (D t : ℕ) : Nat.totient (ED D t) ≤ D :=
  (Nat.totient_le _).trans (Nat.div_le_self _ _)

/-- The additive character `e_D(y) = exp(2πi ỹ / D)` (`ỹ` the least residue). -/
noncomputable def eD (D : ℕ) (y : ZMod D) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℂ) / D))

theorem eD_norm (D : ℕ) (y : ZMod D) : ‖eD D y‖ = 1 := by
  unfold eD
  rw [Complex.norm_exp]
  have : (2 * Real.pi * Complex.I * ((y.val : ℂ) / D)).re = 0 := by
    simp [Complex.mul_re, Complex.div_re, Complex.natCast_re, Complex.natCast_im]
  rw [this, Real.exp_zero]

/-- The colour phase `Ω(c; v₁, h) = 1_{gcd(v₁, D) = 1} e_D(h c v̄₁)`. -/
noncomputable def colourPhase (D : ℕ) (c v h : ZMod D) : ℂ :=
  if Nat.Coprime v.val D then eD D (h * c * v⁻¹) else 0

theorem colourPhase_norm_le (D : ℕ) (c v h : ZMod D) : ‖colourPhase D c v h‖ ≤ 1 := by
  unfold colourPhase; split_ifs <;> simp [eD_norm]

/-- The colour value `c(o) = (b − a₀) · w(o)⁻¹` for a unit `w(o) = n₁ q₀ d u₁ u₂ v₂ mod D`. -/
def colourValue {D : ℕ} (t : ℕ) (w : (ZMod D)ˣ) : ZMod D := (t : ZMod D) * ↑w⁻¹

/-- Every colour value lies in the orbit (LEAN BANK). -/
theorem colour_mem_orbit {D : ℕ} [NeZero D] (t : ℕ) (w : (ZMod D)ˣ) : colourValue t w ∈ orbit D t :=
  mem_image.2 ⟨w⁻¹, mem_univ _, rfl⟩

section Labelled

variable {O I : Type*} [Fintype O] [Fintype I]

/-- The coloured decorated sum
`P = Σ_o A(o) Σ_i Ψ₀(i) Ω(c(o); v₁(i), h(i)) K(o; i)`. -/
noncomputable def colouredSum (D t : ℕ) (A : O → ℂ) (K : O → I → ℂ) (Ψ0 : I → ℂ)
    (v1 hh : I → ZMod D) (w : O → (ZMod D)ˣ) : ℂ :=
  ∑ o, A o * ∑ i, Ψ0 i * colourPhase D (colourValue t (w o)) (v1 i) (hh i) * K o i

/-- The label coefficients `Ψ_j(i) = Ψ₀(i) Ω(j; v₁(i), h(i))`, one per orbit element; they are
functions of the INNER variable only. -/
noncomputable def labelCoeff (D t : ℕ) [NeZero D] (Ψ0 : I → ℂ) (v1 hh : I → ZMod D) (j : orbit D t)
    (i : I) : ℂ :=
  Ψ0 i * colourPhase D j (v1 i) (hh i)

/-- The outer labelling `κ(o) = c(o)`. -/
def labelOf (D t : ℕ) [NeZero D] (w : O → (ZMod D)ˣ) (o : O) : orbit D t :=
  ⟨colourValue t (w o), colour_mem_orbit t (w o)⟩

omit [Fintype I] in
theorem labelCoeff_norm_le (D t : ℕ) [NeZero D] (Ψ0 : I → ℂ) (hΨ0 : ∀ i, ‖Ψ0 i‖ ≤ 1) (v1 hh : I → ZMod D)
    (j : orbit D t) (i : I) : ‖labelCoeff D t Ψ0 v1 hh j i‖ ≤ 1 := by
  unfold labelCoeff
  rw [norm_mul]
  exact mul_le_one₀ (hΨ0 i) (norm_nonneg _) (colourPhase_norm_le _ _ _ _)

/-- **The coloured sum IS a finite-label sum** (LEAN BANK). -/
theorem coloured_eq_labelled (D t : ℕ) [NeZero D] (A : O → ℂ) (K : O → I → ℂ) (Ψ0 : I → ℂ)
    (v1 hh : I → ZMod D) (w : O → (ZMod D)ˣ) :
    colouredSum D t A K Ψ0 v1 hh w =
      labelSum A K (labelCoeff D t Ψ0 v1 hh) (labelOf D t w) := by
  rfl

/-- **Character-free `√φ(E_D)` colour cost** (LEAN BANK, relative to the single-label estimate):
if every one-bounded inner coefficient obeys `mass · V(Ψ) ≤ B²`, then
`|P| ≤ √φ(E_D) · B` and `|P| ≤ √D · B`. -/
theorem colour_sqrt_phi_bound (D t : ℕ) [NeZero D] (A : O → ℂ) (wt : O → ℝ)
    (hA : ∀ o, ‖A o‖ ^ 2 ≤ wt o) (K : O → I → ℂ) (Ψ0 : I → ℂ) (hΨ0 : ∀ i, ‖Ψ0 i‖ ≤ 1)
    (v1 hh : I → ZMod D) (w : O → (ZMod D)ˣ) {B : ℝ} (hB : 0 ≤ B)
    (hsingle : ∀ Ψ : I → ℂ, (∀ i, ‖Ψ i‖ ≤ 1) → (∑ o, wt o) * energy K Ψ ≤ B ^ 2) :
    ‖colouredSum D t A K Ψ0 v1 hh w‖ ≤ Real.sqrt (Nat.totient (ED D t)) * B ∧
      ‖colouredSum D t A K Ψ0 v1 hh w‖ ≤ Real.sqrt D * B := by
  have h1 : ‖colouredSum D t A K Ψ0 v1 hh w‖ ≤ Real.sqrt (Nat.totient (ED D t)) * B := by
    rw [coloured_eq_labelled]
    have := labelled_sqrt_cost A wt hA K (labelCoeff D t Ψ0 v1 hh) (labelOf D t w) hB
      fun j => hsingle _ fun i => labelCoeff_norm_le D t Ψ0 hΨ0 v1 hh j i
    rwa [Fintype.card_coe, orbit_card] at this
  refine ⟨h1, h1.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) hB)⟩
  exact_mod_cast orbit_card_le D t

end Labelled

end CRTColourOrbit
end ResearchBankV27
end Erdos287
