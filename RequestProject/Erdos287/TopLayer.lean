import RequestProject.Erdos287.Defs

/-!
# Erdős Problem #287 — top-layer congruence and obstructions

Let `A` be a finite set of positive integers with `∑_{a∈A} 1/a = 1`, let `p` be a prime,
`e = topExp A p` the maximal `p`-adic valuation, and `A_p^{max} = topLayer A p`.

If `e ≥ 1`, writing each `a ∈ A_p^{max}` as `a = p^e · m_a` with `p ∤ m_a`
(so `m_a = ordCompl[p] a`), we have

`∑_{a ∈ A_p^{max}} m_a⁻¹ ≡ 0 (mod p)`.

We deduce the singleton/pair/triple obstructions.
-/

open scoped BigOperators

set_option maxHeartbeats 4000000

namespace Erdos287

/-
**Top-layer congruence.** With `m_a = ordCompl[p] a = a / p^e`, the sum of the
mod-`p` inverses of the cofactors over the top `p`-adic layer vanishes in `ZMod p`.
-/
theorem topLayer_congruence
    (A : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hpos : ∀ a ∈ A, 0 < a)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1)
    (he : 1 ≤ topExp A p) :
    (∑ a ∈ topLayer A p, (((ordCompl[p] a : ℕ) : ZMod p))⁻¹) = 0 := by
  have h_mul_ne_zero : ( (∏ a ∈ A, (a / p ^ (Nat.factorization a p))):ZMod p ) ≠ 0 := by
    haveI := Fact.mk hp; simp_all +decide [ Finset.prod_eq_zero_iff, ZMod.natCast_eq_zero_iff ] ;
    exact fun x hx => Nat.not_dvd_ordCompl hp ( ne_of_gt ( hpos x hx ) );
  have h_identity : (∑ a ∈ A, (p ^ (topExp A p - Nat.factorization a p) * (∏ b ∈ A.erase a, (b / p ^ Nat.factorization b p)) : ℕ)) = p ^ topExp A p * (∏ a ∈ A, (a / p ^ Nat.factorization a p)) := by
    -- Multiply both sides of the equation by $p^e * N$ to clear the denominators.
    have h_mul : (∑ a ∈ A, (p ^ topExp A p * (∏ b ∈ A, (b / p ^ Nat.factorization b p)) : ℚ) / a) = p ^ topExp A p * (∏ a ∈ A, (a / p ^ Nat.factorization a p)) := by
      simp_all +decide [ div_eq_mul_inv, ← Finset.mul_sum _ _ _ ];
    convert h_mul using 1;
    rw [ ← @Nat.cast_inj ℚ ] ; push_cast ; rw [ Finset.sum_congr rfl ];
    intro a ha; rw [ eq_div_iff ( Nat.cast_ne_zero.mpr <| ne_of_gt <| hpos a ha ) ] ; rw [ ← Finset.mul_prod_erase _ _ ha ] ; simp +decide [ mul_comm ] ;
    rw [ Nat.cast_div ( Nat.ordProj_dvd _ _ ) ( by aesop ) ] ; ring;
    field_simp;
    rw [ show ( p : ℚ ) ^ topExp A p = p ^ ( Nat.factorization a p ) * p ^ ( topExp A p - Nat.factorization a p ) by rw [ ← pow_add, Nat.add_sub_of_le ( show Nat.factorization a p ≤ topExp A p from Finset.le_sup ( f := fun a => Nat.factorization a p ) ha ) ] ] ; push_cast ; ring;
  have h_identity_mod : (∑ a ∈ A, (p ^ (topExp A p - Nat.factorization a p) * (∏ b ∈ A.erase a, (b / p ^ Nat.factorization b p)) : ZMod p)) = 0 := by
    norm_cast ; simp_all +decide;
    rw [ zero_pow ( by linarith ), MulZeroClass.zero_mul ];
  have h_identity_mod_top : (∑ a ∈ topLayer A p, (∏ b ∈ A.erase a, (b / p ^ Nat.factorization b p) : ZMod p)) = 0 := by
    have h_identity_mod_top : (∑ a ∈ A \ topLayer A p, (p ^ (topExp A p - Nat.factorization a p) * (∏ b ∈ A.erase a, (b / p ^ Nat.factorization b p)) : ZMod p)) = 0 := by
      refine' Finset.sum_eq_zero fun x hx => _;
      simp_all +decide [ Finset.mem_sdiff ];
      rw [ zero_pow ] <;> norm_num;
      exact Nat.sub_ne_zero_of_lt ( lt_of_le_of_ne ( Finset.le_sup ( f := fun a => Nat.factorization a p ) hx.1 ) fun h => hx.2 <| Finset.mem_filter.mpr ⟨ hx.1, h ⟩ );
    simp_all +decide [ topLayer ];
    convert h_identity_mod_top using 2 ; aesop;
  convert congr_arg ( fun x : ZMod p => x * ( ∏ a ∈ A, ( a / p ^ a.factorization p : ZMod p ) ) ⁻¹ ) h_identity_mod_top using 1;
  · rw [ Finset.sum_mul _ _ _ ];
    refine' Finset.sum_congr rfl fun x hx => _;
    rw [ ← Finset.prod_erase_mul _ _ ( Finset.mem_coe.mpr ( Finset.mem_of_mem_filter _ hx ) ), mul_comm ];
    haveI := Fact.mk hp; simp_all +decide [ Finset.prod_eq_zero_iff ] ;
  · ring

/-
The top `p`-adic layer cannot be a singleton (when `e ≥ 1`).
-/
theorem topLayer_card_ne_one
    (A : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hpos : ∀ a ∈ A, 0 < a)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1)
    (he : 1 ≤ topExp A p) :
    (topLayer A p).card ≠ 1 := by
  intro h
  have h_singleton : ∃ a, topLayer A p = {a} := by
    exact Finset.card_eq_one.mp h;
  -- By `topLayer_congruence A p hp hpos hsum he`, `∑ x ∈ topLayer A p, ((ordCompl[p] x : ZMod p))⁻¹ = 0`.
  obtain ⟨a, ha⟩ := h_singleton
  have h_sum : ((ordCompl[p] a : ZMod p))⁻¹ = 0 := by
    have := topLayer_congruence A p hp hpos hsum he; simp_all +decide [ Finset.sum_singleton ] ;
  haveI := Fact.mk hp; simp_all +decide ;
  rw [ ZMod.natCast_eq_zero_iff ] at h_sum ; exact Nat.not_dvd_ordCompl hp ( ne_of_gt ( hpos a ( Finset.mem_filter.mp ( ha.symm ▸ Finset.mem_singleton_self _ ) |>.1 ) ) ) h_sum;

/-
**Two-element obstruction.** If the top layer is `{a₁, a₂}` with cofactors
`m₁, m₂`, then `p ∣ m₁ + m₂`.
-/
theorem topLayer_two_obstruction
    (A : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hpos : ∀ a ∈ A, 0 < a)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1)
    (he : 1 ≤ topExp A p)
    {a₁ a₂ : ℕ} (ha : topLayer A p = {a₁, a₂}) (hne : a₁ ≠ a₂) :
    p ∣ (ordCompl[p] a₁ + ordCompl[p] a₂) := by
  have h_cong : (((ordCompl[p] a₁ : ℕ) : ZMod p))⁻¹ + (((ordCompl[p] a₂ : ℕ) : ZMod p))⁻¹ = 0 := by
    convert topLayer_congruence A p hp hpos hsum he using 1;
    rw [ ha, Finset.sum_pair hne ];
  haveI := Fact.mk hp; rw [ ← ZMod.natCast_eq_zero_iff ] ; simp_all +decide [ add_eq_zero_iff_eq_neg ] ;
  rw [ inv_eq_iff_eq_inv ] at h_cong ; aesop

/-
**Three-element obstruction.** If the top layer is `{a₁, a₂, a₃}` with cofactors
`m₁, m₂, m₃`, then `p ∣ m₁m₂ + m₁m₃ + m₂m₃`.
-/
theorem topLayer_three_obstruction
    (A : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hpos : ∀ a ∈ A, 0 < a)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1)
    (he : 1 ≤ topExp A p)
    {a₁ a₂ a₃ : ℕ} (ha : topLayer A p = {a₁, a₂, a₃})
    (h₁₂ : a₁ ≠ a₂) (h₁₃ : a₁ ≠ a₃) (h₂₃ : a₂ ≠ a₃) :
    p ∣ (ordCompl[p] a₁ * ordCompl[p] a₂ + ordCompl[p] a₁ * ordCompl[p] a₃
          + ordCompl[p] a₂ * ordCompl[p] a₃) := by
  have h_cong : (∑ a ∈ ({a₁, a₂, a₃} : Finset ℕ), ((ordCompl[p] a : ℕ) : ZMod p)⁻¹) = 0 := by
    have := topLayer_congruence A p hp hpos hsum he; aesop;
  have h_inv_ne_zero : (a₁ / p ^ (Nat.factorization a₁ p) : ZMod p) ≠ 0 ∧ (a₂ / p ^ (Nat.factorization a₂ p) : ZMod p) ≠ 0 ∧ (a₃ / p ^ (Nat.factorization a₃ p) : ZMod p) ≠ 0 := by
    have h_inv_ne_zero : ∀ a ∈ ({a₁, a₂, a₃} : Finset ℕ), (a / p ^ (Nat.factorization a p) : ℕ) ≠ 0 ∧ ¬(p ∣ (a / p ^ (Nat.factorization a p) : ℕ)) := by
      intro a ha; have := topLayer_subset A p; simp_all +decide [ Finset.ext_iff ] ;
      exact ⟨ Nat.le_of_dvd ( hpos a ( this ( by aesop ) ) ) ( Nat.ordProj_dvd _ _ ), Nat.not_dvd_ordCompl hp ( hpos a ( this ( by aesop ) ) |> ne_of_gt ) ⟩;
    haveI := Fact.mk hp; simp_all +decide [ ← ZMod.natCast_eq_zero_iff ] ;
  haveI := Fact.mk hp; simp_all +decide [ ← ZMod.natCast_eq_zero_iff ] ;
  grind

end Erdos287