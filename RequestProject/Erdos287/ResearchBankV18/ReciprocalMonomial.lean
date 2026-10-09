import RequestProject.Erdos287.ResearchBankV18.ColourConductor
import RequestProject.Erdos287.ResearchBankV18.CharacterExpansion

/-!
# Erdős #287 — Research Bank V18 §2: reciprocal-monomial separation

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The reciprocal colour phase

    Ω_D(h, v) = e_D( h c · inverse(∏_j v_j^{e_j}) )

(units `v_j` of `ZMod D`, inverse taken in `(ZMod D)ˣ`, represented by its least residue).

Kernel-proved (LEAN BANK):
* `recipPhase_shift` — for a unit `u`, `recipPhase(val u) = recipPhase(1) ∘ (u⁻¹ · _)`;
* **`reciprocal_monomial_separation`** — the exact finite decomposition

      Ω_D(u, v) = ∑_χ C_χ · f_{0,χ}(u) · ∏_j f_{j,χ}(v_j),
      C_χ = C_χ(recipPhase(1)),  f_{0,χ}(u) = χ(u⁻¹),  f_{j,χ}(v) = χ(v)^{e_j},

  with every `f` of sup-norm `≤ 1`, for every number `m` of variables;
* `reciprocal_bound_by_variation` — `‖Ω_D(u, v)‖ ≤ ∑_χ ‖C_χ‖`, a bound independent of `m`.
-/

namespace Erdos287
namespace ResearchBankV18
namespace ReciprocalMonomial

open ColourConductor CharacterExpansion

variable {D : ℕ} [NeZero D]

/-- The reciprocal phase `x ↦ e_D(h c · rep(x⁻¹))`. -/
noncomputable def recipPhase (D : ℕ) [NeZero D] (c h : ℤ) (x : (ZMod D)ˣ) : ℂ :=
  e D (h * c * (((x⁻¹ : (ZMod D)ˣ) : ZMod D).val : ℤ))

/-- The reciprocal colour phase `Ω_D(h, v)`. -/
noncomputable def Omega (D : ℕ) [NeZero D] (c h : ℤ) {m : ℕ} (v : Fin m → (ZMod D)ˣ)
    (ex : Fin m → ℕ) : ℂ :=
  recipPhase D c h (∏ j, v j ^ ex j)

omit [NeZero D] in
theorem val_mul_modEq (a b : ZMod D) :
    (((a * b).val : ℕ) : ℤ) ≡ (a.val : ℤ) * (b.val : ℤ) [ZMOD D] := by
  rw [ZMod.val_mul]
  push_cast
  exact Int.emod_emod_of_dvd _ (dvd_refl _)

/-- **Unit shift of the reciprocal phase.** -/
theorem recipPhase_shift (c : ℤ) (u x : (ZMod D)ˣ) :
    recipPhase D c ((u : ZMod D).val) x = recipPhase D c 1 (u⁻¹ * x) := by
  unfold recipPhase
  have hD : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  rw [show (u⁻¹ * x)⁻¹ = x⁻¹ * u by group, Units.val_mul]
  apply e_congr hD
  have := val_mul_modEq ((x⁻¹ : (ZMod D)ˣ) : ZMod D) (u : ZMod D)
  calc ((u : ZMod D).val : ℤ) * c * (((x⁻¹ : (ZMod D)ˣ) : ZMod D).val : ℤ)
      = 1 * c * ((((x⁻¹ : (ZMod D)ˣ) : ZMod D).val : ℤ) * ((u : ZMod D).val : ℤ)) := by ring
    _ ≡ 1 * c * (((((x⁻¹ : (ZMod D)ˣ) : ZMod D) * (u : ZMod D)).val : ℕ) : ℤ) [ZMOD D] :=
        Int.ModEq.mul_left _ this.symm

/-- **Reciprocal-monomial separation** (exact finite decomposition, any `m`). -/
theorem reciprocal_monomial_separation (c : ℤ) (u : (ZMod D)ˣ) {m : ℕ}
    (v : Fin m → (ZMod D)ˣ) (ex : Fin m → ℕ) :
    Omega D c ((u : ZMod D).val) v ex =
      ∑ χ : DirichletCharacter ℂ D,
        coef (recipPhase D c 1) χ * χ ((u⁻¹ : (ZMod D)ˣ) : ZMod D) * ∏ j, (χ (v j)) ^ ex j := by
  unfold Omega
  have hfun : recipPhase D c ((u : ZMod D).val) = fun x => recipPhase D c 1 (u⁻¹ * x) := by
    funext x; exact recipPhase_shift c u x
  rw [hfun]
  refine (monomial_separation (fun x => recipPhase D c 1 (u⁻¹ * x)) m v ex).trans ?_
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [coef_shift (recipPhase D c 1) u⁻¹ χ]
  ring

omit [NeZero D] in
/-- The `h`-factor `f_{0,χ}(u) = χ(u⁻¹)` is one-bounded. -/
theorem f0_bounded (χ : DirichletCharacter ℂ D) (u : (ZMod D)ˣ) :
    ‖χ ((u⁻¹ : (ZMod D)ˣ) : ZMod D)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _

/-- **Bound by the scalar variation**, independent of the number `m` of factors. -/
theorem reciprocal_bound_by_variation (c : ℤ) (u : (ZMod D)ˣ) {m : ℕ}
    (v : Fin m → (ZMod D)ˣ) (ex : Fin m → ℕ) :
    ‖Omega D c ((u : ZMod D).val) v ex‖ ≤ variation (recipPhase D c 1) := by
  rw [reciprocal_monomial_separation]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_)
  rw [norm_mul, norm_mul]
  have h1 := f0_bounded χ u
  have h2 : ‖∏ j, (χ (v j)) ^ ex j‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun j _ => char_norm_le_one χ _ _
  have h0 := norm_nonneg (coef (recipPhase D c 1) χ)
  calc ‖coef (recipPhase D c 1) χ‖ * ‖χ ((u⁻¹ : (ZMod D)ˣ) : ZMod D)‖ * ‖∏ j, (χ (v j)) ^ ex j‖
      ≤ ‖coef (recipPhase D c 1) χ‖ * 1 * 1 := by gcongr
    _ = ‖coef (recipPhase D c 1) χ‖ := by ring

end ReciprocalMonomial
end ResearchBankV18
end Erdos287
