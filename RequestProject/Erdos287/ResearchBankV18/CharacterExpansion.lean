import Mathlib

/-!
# Erdős #287 — Research Bank V18 §2: multiplicative-character expansion on `(ZMod n)ˣ`

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

For any function `φ : (ZMod n)ˣ → ℂ` put

    C_χ(φ) = φ(n)⁻¹ · ∑_{a unit} φ(a) χ(a⁻¹)        (χ a Dirichlet character mod n).

Kernel-proved (LEAN BANK), from Mathlib's character orthogonality
(`DirichletCharacter.sum_char_inv_mul_char_eq`):
* `expansion` — `φ(b) = ∑_χ C_χ(φ) χ(b)` for every unit `b`;
* **`monomial_separation`** — for every number `m` of variables, all `v : Fin m → (ZMod n)ˣ` and
  exponents `e`:  `φ(∏_j v_j^{e_j}) = ∑_χ C_χ(φ) ∏_j χ(v_j)^{e_j}`, every factor of norm `≤ 1`;
* **`one_family_for_all_m`** — ONE coefficient family, with total variation
  `variation φ = ∑_χ ‖C_χ(φ)‖`, serves every `m` simultaneously: the number of reciprocal factors
  does not enter the scalar cost;
* `coef_shift` — `C_χ(φ(u · _)) = χ(u) C_χ(φ)` (used to peel off the `h`-dependence).
-/

namespace Erdos287
namespace ResearchBankV18
namespace CharacterExpansion

variable {n : ℕ} [NeZero n]

/-- The character coefficient `C_χ(φ)`. -/
noncomputable def coef (φ : (ZMod n)ˣ → ℂ) (χ : DirichletCharacter ℂ n) : ℂ :=
  (n.totient : ℂ)⁻¹ * ∑ a : (ZMod n)ˣ, φ a * χ ((a : ZMod n)⁻¹)

/-- Total scalar variation `∑_χ ‖C_χ(φ)‖`. -/
noncomputable def variation (φ : (ZMod n)ˣ → ℂ) : ℝ := ∑ χ : DirichletCharacter ℂ n, ‖coef φ χ‖

theorem totient_ne_zero : (n.totient : ℂ) ≠ 0 := by
  have : 0 < n.totient := Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  exact_mod_cast this.ne'

/-- **Character expansion.** -/
theorem expansion (φ : (ZMod n)ˣ → ℂ) (b : (ZMod n)ˣ) :
    ∑ χ : DirichletCharacter ℂ n, coef φ χ * χ b = φ b := by
  unfold coef
  simp_rw [mul_assoc, Finset.sum_mul, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have horth : ∀ a : (ZMod n)ˣ, ∑ χ : DirichletCharacter ℂ n, χ ((a : ZMod n)⁻¹) * χ b =
      if a = b then (n.totient : ℂ) else 0 := by
    intro a
    rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit (b : ZMod n)]
    simp only [Units.val_inj]
  simp_rw [horth, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [mul_comm (φ b), ← mul_assoc, inv_mul_cancel₀ totient_ne_zero, one_mul]

omit [NeZero n] in
/-- Every character value on a unit has norm `≤ 1`. -/
theorem char_norm_le_one (χ : DirichletCharacter ℂ n) (v : (ZMod n)ˣ) (k : ℕ) :
    ‖(χ v) ^ k‖ ≤ 1 := by
  rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)

/-- **Reciprocal-monomial separation** (any number `m` of variables). -/
theorem monomial_separation (φ : (ZMod n)ˣ → ℂ) (m : ℕ) (v : Fin m → (ZMod n)ˣ)
    (e : Fin m → ℕ) :
    φ (∏ j, v j ^ e j) = ∑ χ : DirichletCharacter ℂ n, coef φ χ * ∏ j, (χ (v j)) ^ e j := by
  rw [← expansion φ]
  refine Finset.sum_congr rfl fun χ _ => ?_
  congr 1
  rw [Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Units.val_pow_eq_pow_val, map_pow]

/-- **One coefficient family for all `m`**: the scalar cost `variation φ` does not depend on the
number of reciprocal factors. -/
theorem one_family_for_all_m (φ : (ZMod n)ˣ → ℂ) :
    ∃ C : DirichletCharacter ℂ n → ℂ, ∑ χ, ‖C χ‖ = variation φ ∧
      ∀ (m : ℕ) (v : Fin m → (ZMod n)ˣ) (e : Fin m → ℕ),
        φ (∏ j, v j ^ e j) = ∑ χ, C χ * ∏ j, (χ (v j)) ^ e j ∧
        ∀ χ : DirichletCharacter ℂ n, ∀ j, ‖(χ (v j)) ^ e j‖ ≤ 1 :=
  ⟨coef φ, rfl, fun m v e => ⟨monomial_separation φ m v e, fun χ _ => char_norm_le_one χ _ _⟩⟩

/-- The separated sum is bounded by the variation (one-bounded factors). -/
theorem separated_norm_le (φ : (ZMod n)ˣ → ℂ) (m : ℕ) (v : Fin m → (ZMod n)ˣ) (e : Fin m → ℕ) :
    ‖φ (∏ j, v j ^ e j)‖ ≤ variation φ := by
  rw [monomial_separation φ m v e]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_)
  rw [norm_mul]
  have : ‖∏ j, (χ (v j)) ^ e j‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun j _ => char_norm_le_one χ _ _
  calc ‖coef φ χ‖ * ‖∏ j, (χ (v j)) ^ e j‖ ≤ ‖coef φ χ‖ * 1 :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = ‖coef φ χ‖ := mul_one _

/-- **Shift rule** `C_χ(φ(u · _)) = χ(u) C_χ(φ)`. -/
theorem coef_shift (φ : (ZMod n)ˣ → ℂ) (u : (ZMod n)ˣ) (χ : DirichletCharacter ℂ n) :
    coef (fun a => φ (u * a)) χ = χ u * coef φ χ := by
  have key : ∑ a : (ZMod n)ˣ, φ (u * a) * χ ((a : ZMod n)⁻¹) =
      χ u * ∑ b : (ZMod n)ˣ, φ b * χ ((b : ZMod n)⁻¹) := by
    rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft u⁻¹)]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Equiv.coe_mulLeft, ZMod.inv_coe_unit, mul_inv_cancel_left]
    rw [show (u⁻¹ * b)⁻¹ = b⁻¹ * u by group, Units.val_mul, map_mul]
    ring
  unfold coef
  rw [key]; ring

end CharacterExpansion
end ResearchBankV18
end Erdos287
