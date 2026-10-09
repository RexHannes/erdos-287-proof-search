import Mathlib

/-!
# Erdős #287 — the random three-colouring count

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

`card_compat_mul`: if `q : Fin J ↪ Fin K` and `c : Fin J → Fin 3`, the number of colourings
`χ : Fin K → Fin 3` with `χ (q i) = c i` for all `i` is `3^{K-J}`, i.e.
`#{χ compatible} · 3^J = 3^K`.  This is the exact normalisation behind the prime-colouring
decoupling of distinctness across the three Pascadi factors.
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Physical.Factor

theorem card_compat_mul {K J : ℕ} (q : Fin J → Fin K) (hq : Function.Injective q)
    (c : Fin J → Fin 3) :
    (univ.filter (fun χ : Fin K → Fin 3 => ∀ i, χ (q i) = c i)).card * 3 ^ J = 3 ^ K := by
  classical
  set F : Fin K → Fin 3 → ℕ := fun x v => if ∀ i, q i = x → c i = v then 1 else 0 with hF
  have step12 : (univ.filter (fun χ : Fin K → Fin 3 => ∀ i, χ (q i) = c i)).card =
      ∑ χ : Fin K → Fin 3, ∏ x, F x (χ x) := by
    rw [card_filter]
    refine sum_congr rfl (fun χ _ => ?_)
    rw [hF, prod_boole]
    simp only [mem_univ, true_implies]
    congr 1
    apply propext
    constructor
    · intro h x i hi; rw [← hi, h i]
    · intro h i; exact (h (q i) i rfl).symm
  have step3 : ∑ χ : Fin K → Fin 3, ∏ x, F x (χ x) = ∏ x, ∑ v, F x v := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  have step4 : ∀ x, ∑ v, F x v = if x ∈ univ.image q then 1 else 3 := by
    intro x
    rw [hF, sum_boole]
    split_ifs with hx
    · obtain ⟨i0, -, rfl⟩ := mem_image.1 hx
      have : univ.filter (fun v : Fin 3 => ∀ i, q i = q i0 → c i = v) = {c i0} := by
        ext v
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · intro h; exact (h i0 rfl).symm
        · rintro rfl i hi; rw [hq hi]
      rw [this]; simp
    · have : univ.filter (fun v : Fin 3 => ∀ i, q i = x → c i = v) = univ := by
        ext v
        simp only [mem_filter, mem_univ, true_and, iff_true]
        intro i hi
        exact absurd (mem_image.2 ⟨i, mem_univ _, hi⟩) hx
      rw [this]; simp
  have hJK : J ≤ K := by
    simpa using Fintype.card_le_of_injective q hq
  rw [step12, step3, prod_congr rfl (fun x _ => step4 x), prod_ite, prod_const_one, one_mul,
    prod_const]
  have hcard : (univ.filter (fun x : Fin K => x ∉ univ.image q)).card = K - J := by
    rw [filter_not, filter_mem_eq_inter, univ_inter, card_sdiff_of_subset (subset_univ _),
      card_image_of_injective _ hq]
    simp
  rw [hcard, ← pow_add, Nat.sub_add_cancel hJK]

end Erdos287.Physical.Factor
