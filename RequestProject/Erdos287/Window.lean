import RequestProject.Erdos287.TopLayer
import RequestProject.Erdos287.Cnum

/-!
# Erdős Problem #287 — prime-power window exclusion

If `A ⊆ {1,…,M}` with `∑_{a∈A} 1/a = 1`, `q = p^e ≤ M`, `j = ⌊M/q⌋`, and `p > C(j)`,
then no element of `A` is divisible by `q`.
-/

open scoped BigOperators

set_option maxHeartbeats 4000000

namespace Erdos287

/-
If the mod-`p` inverse sum of a finite set `S` of positive integers coprime to `p`
vanishes in `ZMod p`, then `p` divides the numerator of `∑_{s∈S} 1/s`.
-/
theorem dvd_num_of_sum_inv_zero (S : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hpos : ∀ s ∈ S, 0 < s) (hcop : ∀ s ∈ S, ¬ p ∣ s)
    (h0 : (∑ s ∈ S, ((s : ZMod p))⁻¹) = 0) :
    (p : ℤ) ∣ (∑ s ∈ S, (1 : ℚ) / s).num := by
  have h_num : (∑ s ∈ S, (s : ℚ)⁻¹).num * (∏ s ∈ S, s) ≡ 0 [ZMOD p] := by
    have h_num : (∑ s ∈ S, (s : ℚ)⁻¹).num * (∏ s ∈ S, s) = (∑ s ∈ S, (∏ t ∈ S \ {s}, t)) * (∑ s ∈ S, (s : ℚ)⁻¹).den := by
      have h_num : (∑ s ∈ S, (s : ℚ)⁻¹) * (∏ s ∈ S, s) = (∑ s ∈ S, (∏ t ∈ S \ {s}, t)) := by
        push_cast [ Finset.sum_mul _ _ _ ];
        exact Finset.sum_congr rfl fun x hx => by rw [ inv_mul_eq_div, div_eq_iff ( Nat.cast_ne_zero.mpr <| ne_of_gt <| hpos x hx ) ] ; rw [ Finset.prod_eq_prod_diff_singleton_mul hx ] ;
      rw [ ← Rat.num_div_den ( ∑ s ∈ S, ( s : ℚ ) ⁻¹ ) ] at h_num;
      rw [ div_mul_eq_mul_div, div_eq_iff ] at h_num <;> norm_cast at * ; aesop;
    haveI := Fact.mk hp; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ] ;
    have h_sum_zero : (∑ s ∈ S, (∏ t ∈ S \ {s}, (t : ZMod p))) = (∏ s ∈ S, (s : ZMod p)) * (∑ s ∈ S, (s : ZMod p)⁻¹) := by
      rw [ Finset.mul_sum _ _ _ ];
      refine' Finset.sum_congr rfl fun x hx => _;
      rw [ ← Finset.prod_sdiff ( Finset.singleton_subset_iff.mpr hx ), Finset.prod_singleton ];
      rw [ mul_assoc, mul_inv_cancel₀ ( by rw [ Ne.eq_def, ZMod.natCast_eq_zero_iff ] ; exact hcop x hx ), mul_one ];
    aesop;
  simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_eq_intCast_iff ];
  haveI := Fact.mk hp; simp_all +decide [ Finset.prod_eq_zero_iff, ZMod.natCast_eq_zero_iff ] ;
  exact h_num.resolve_right fun ⟨ a, ha, ha' ⟩ => hcop a ha ha'

/-
**Prime-power window exclusion.** If `A ⊆ {1,…,M}`, `∑ 1/a = 1`, `q = p^e ≤ M`,
`j = ⌊M/q⌋`, and `p > C(j)`, then no element of `A` is divisible by `q`.

The hypothesis `hqM : p^e ≤ M` is included because it is part of the stated problem,
but the proof does not use it: if `p^e > M`, no element `a ≤ M` can be divisible by `p^e`,
so the conclusion holds trivially.
-/
theorem primePower_window_exclusion
    (A : Finset ℕ) (M p e : ℕ) (hp : p.Prime)
    (hpos : ∀ a ∈ A, 0 < a)
    (hAM : ∀ a ∈ A, a ≤ M)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1)
    (he : 1 ≤ e)
    (hqM : p ^ e ≤ M)
    (hpC : C (M / p ^ e) < (p : ℤ)) :
    ∀ a ∈ A, ¬ (p ^ e ∣ a) := by
  contrapose! hpC; haveI := Fact.mk hp; simp_all +decide [ div_eq_mul_inv ] ;
  obtain ⟨a₀, ha₀A, ha₀q⟩ : ∃ a₀ ∈ A, p ^ e ∣ a₀ := hpC
  set E := A.sup (fun a => Nat.factorization a p)
  have hE_ge_e : e ≤ E := by
    exact le_trans ( Nat.le_of_not_lt fun h => absurd ( Nat.dvd_trans ( pow_dvd_pow _ h ) ha₀q ) ( Nat.pow_succ_factorization_not_dvd ( ne_of_gt ( hpos a₀ ha₀A ) ) hp ) ) ( Finset.le_sup ( f := fun a => Nat.factorization a p ) ha₀A )
  have hE_nonempty : (topLayer A p).Nonempty := by
    -- Since $E$ is the supremum of the $p$-adic valuations of elements in $A$, there must be some $a \in A$ such that $Nat.factorization a p = E$.
    obtain ⟨a, haA, haE⟩ : ∃ a ∈ A, Nat.factorization a p = E := by
      exact Finset.exists_max_image _ _ ⟨ a₀, ha₀A ⟩ |> fun ⟨ a, ha₁, ha₂ ⟩ => ⟨ a, ha₁, le_antisymm ( Finset.le_sup ( f := fun a => Nat.factorization a p ) ha₁ ) ( Finset.sup_le fun x hx => ha₂ x hx ) ⟩;
    exact ⟨ a, Finset.mem_filter.mpr ⟨ haA, haE ⟩ ⟩
  have hsum_cong : (∑ a ∈ topLayer A p, ((ordCompl[p] a : ZMod p))⁻¹) = 0 := by
    convert topLayer_congruence A p hp hpos _ _ using 1;
    · grind;
    · exact le_trans he hE_ge_e;
  -- Let `S := (topLayer A p).image (fun a => ordCompl[p] a)`.
  set S := (topLayer A p).image (fun a => ordCompl[p] a) with hS_def
  have hS_nonempty : S.Nonempty := by
    exact ⟨ _, Finset.mem_image_of_mem _ hE_nonempty.choose_spec ⟩
  have hS_subset : S ⊆ Finset.Icc 1 (M / p ^ e) := by
    intro s hs; obtain ⟨ a, ha, rfl ⟩ := Finset.mem_image.mp hs; simp_all +decide [ topLayer ] ;
    exact ⟨ Nat.div_pos ( Nat.le_of_dvd ( hpos a ha.1 ) ( ha.2 ▸ Nat.ordProj_dvd _ _ ) ) ( pow_pos hp.pos _ ), Nat.div_le_div_right ( hAM a ha.1 ) |> le_trans <| Nat.div_le_div_left ( pow_le_pow_right₀ hp.one_lt.le hE_ge_e ) <| pow_pos hp.pos _ ⟩
  have hS_pos : ∀ s ∈ S, 0 < s := by
    exact fun s hs => Finset.mem_Icc.mp ( hS_subset hs ) |>.1
  have hS_not_div : ∀ s ∈ S, ¬ p ∣ s := by
    intro s hs; obtain ⟨ a, ha, rfl ⟩ := Finset.mem_image.mp hs; exact Nat.not_dvd_ordCompl hp ( ne_of_gt ( hpos a ( topLayer_subset _ _ ha ) ) ) ;
  have hS_sum_inv_zero : (∑ s ∈ S, ((s : ZMod p))⁻¹) = 0 := by
    rw [ Finset.sum_image ] ; aesop;
    intros a ha b hb hab; have := Nat.div_mul_cancel ( Nat.ordProj_dvd a p ) ; have := Nat.div_mul_cancel ( Nat.ordProj_dvd b p ) ; simp_all +decide [ Nat.factorization_eq_zero_iff ] ;
    simp_all +decide [ topLayer ]
  have hS_num_div : (p : ℤ) ∣ (∑ s ∈ S, (1 : ℚ) / s).num := by
    convert dvd_num_of_sum_inv_zero S p hp hS_pos hS_not_div _ using 1 ; aesop
  have hS_num_le_C : (∑ s ∈ S, (1 : ℚ) / s).num ≤ C (M / p ^ e) := by
    convert num_le_C ( M / p ^ e ) S hS_nonempty hS_subset using 1
  have hS_num_pos : 0 < (∑ s ∈ S, (1 : ℚ) / s).num := by
    exact Rat.num_pos.mpr ( Finset.sum_pos ( fun x hx => one_div_pos.mpr <| Nat.cast_pos.mpr <| hS_pos x hx ) hS_nonempty )
  have h_contra : (p : ℤ) ≤ (∑ s ∈ S, (1 : ℚ) / s).num := by
    exact Int.le_of_dvd hS_num_pos hS_num_div
  linarith [hS_num_le_C]

end Erdos287