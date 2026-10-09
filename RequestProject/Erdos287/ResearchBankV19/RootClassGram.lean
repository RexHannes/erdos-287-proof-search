import Mathlib

/-!
# Erdős #287 — Research Bank V19 §3: the root-class Gram identity

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

For units `r_j` of `ZMod g` and complex `z_j` (`j` in a finite index set):

    ∑_{j,k} z_j conj(z_k) (1_{r_j = r_k} − 1/φ(g))
      = (1/φ(g)) ∑_{χ ≠ χ₀} |∑_j z_j χ(r_j)|².

Kernel-proved (LEAN BANK), exact finite-group setting (Dirichlet characters mod `g`, Mathlib's
orthogonality `DirichletCharacter.sum_char_inv_mul_char_eq` and `MulChar.star_apply'`):
* `all_characters` — `∑_χ |S_χ|² = φ(g) ∑_{j,k} z_j conj(z_k) 1_{r_j = r_k}`;
* `principal_term` — `|S_{χ₀}|² = ∑_{j,k} z_j conj(z_k)`;
* **`root_class_gram`** — the identity above.  This is the fallback when coherence has not been
  proved.
-/

namespace Erdos287
namespace ResearchBankV19
namespace RootClassGram

variable {g : ℕ} [NeZero g] {J : Type*} [Fintype J]

/-- `S_χ = ∑_j z_j χ(r_j)`. -/
noncomputable def S (z : J → ℂ) (r : J → (ZMod g)ˣ) (χ : DirichletCharacter ℂ g) : ℂ :=
  ∑ j, z j * χ (r j)

omit [NeZero g] in
theorem star_char_unit (χ : DirichletCharacter ℂ g) (u : (ZMod g)ˣ) :
    star (χ u) = χ ((u : ZMod g)⁻¹) := by
  rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]

theorem orth (a b : (ZMod g)ˣ) :
    ∑ χ : DirichletCharacter ℂ g, χ (b : ZMod g) * star (χ a) =
      if a = b then (g.totient : ℂ) else 0 := by
  rw [show ∑ χ : DirichletCharacter ℂ g, χ (b : ZMod g) * star (χ a) =
      ∑ χ : DirichletCharacter ℂ g, χ ((a : ZMod g)⁻¹) * χ (b : ZMod g) from
    Finset.sum_congr rfl fun χ _ => by rw [star_char_unit, mul_comm]]
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit (b : ZMod g)]
  simp only [Units.val_inj]

theorem all_characters (z : J → ℂ) (r : J → (ZMod g)ˣ) :
    ∑ χ : DirichletCharacter ℂ g, S z r χ * star (S z r χ) =
      (g.totient : ℂ) * ∑ j, ∑ k, z j * star (z k) * (if r j = r k then 1 else 0) := by
  unfold S
  have e : ∀ χ : DirichletCharacter ℂ g,
      (∑ j, z j * χ (r j)) * star (∑ k, z k * χ (r k)) =
        ∑ j, ∑ k, z j * star (z k) * (χ (r j) * star (χ (r k))) := by
    intro χ
    rw [star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [star_mul']; ring
  simp_rw [e]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum, orth]
  by_cases h : r j = r k
  · rw [if_pos h.symm, if_pos h]; ring
  · rw [if_neg (Ne.symm h), if_neg h]; ring

omit [NeZero g] in
theorem principal_term (z : J → ℂ) (r : J → (ZMod g)ˣ) :
    S z r 1 * star (S z r 1) = ∑ j, ∑ k, z j * star (z k) := by
  unfold S
  simp_rw [MulChar.one_apply_coe, mul_one]
  rw [star_sum, Finset.sum_mul_sum]

theorem totient_ne_zero : (g.totient : ℂ) ≠ 0 := by
  have : 0 < g.totient := Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne g))
  exact_mod_cast this.ne'

/-- **The root-class Gram identity.** -/
theorem root_class_gram (z : J → ℂ) (r : J → (ZMod g)ˣ) :
    ∑ j, ∑ k, z j * star (z k) * ((if r j = r k then 1 else 0) - (g.totient : ℂ)⁻¹) =
      (g.totient : ℂ)⁻¹ *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ g), S z r χ * star (S z r χ) := by
  have hall := all_characters z r
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ g)),
    principal_term] at hall
  have hrest : ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ g), S z r χ * star (S z r χ) =
      (g.totient : ℂ) * ∑ j, ∑ k, z j * star (z k) * (if r j = r k then 1 else 0) -
        ∑ j, ∑ k, z j * star (z k) := by
    rw [← hall]; ring
  rw [hrest, mul_sub, ← mul_assoc, inv_mul_cancel₀ totient_ne_zero, one_mul]
  simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

end RootClassGram
end ResearchBankV19
end Erdos287
