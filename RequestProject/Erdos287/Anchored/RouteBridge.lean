import RequestProject.Erdos287.Anchored.PrimePowerLayer
import RequestProject.Erdos287.TopLayer
import RequestProject.Erdos287.ProblemStatement

/-!
# Bridges between the anchored route and the existing #287 objects

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Two *proved* bridges are provided — nothing else is imported from, or exported to, the other
routes:

* `padicValRat_recipSum_iff_zmod_inv_sum`: for cofactors prime to `p`, the anchored valuation
  condition `v_p(∑ 1/c) ≥ 1` is **exactly** the mod-`p` inverse-sum condition used in the
  elementary top-layer package;
* `topLayer_anchoredFeasible`: consequently, for any finite set of positive integers with
  reciprocal sum `1` and top `p`-adic exponent `≥ 1`, the cofactor set of the top layer is
  anchored-feasible.  This is the anchored-route reading of the banked theorem
  `Erdos287.topLayer_congruence`.

A third, purely bookkeeping bridge records that the exact #287 counterexample predicate
produces the ambient compiler identity `cofactorNum A A = lcmOf A`.
-/

open scoped BigOperators

namespace Erdos287
namespace Anchored

/-- If no element of `C` is divisible by the prime `p`, then neither is `lcmOf C`. -/
theorem not_dvd_lcmOf {p : ℕ} (hp : p.Prime) {C : Finset ℕ} (h : ∀ c ∈ C, ¬ p ∣ c) :
    ¬ p ∣ lcmOf C := by
  classical
  have hcop : Nat.Coprime p (lcmOf C) := by
    induction C using Finset.induction_on with
    | empty => simp [lcmOf]
    | insert a s ha ih =>
        have h1 : Nat.Coprime p a := (Nat.Prime.coprime_iff_not_dvd hp).2 (h a (by simp))
        have h2 : Nat.Coprime p (lcmOf s) := ih (fun c hc => h c (by simp [hc]))
        have hins : lcmOf (insert a s) = Nat.lcm a (lcmOf s) := by
          simp [lcmOf, Finset.lcm_insert, lcm]
        rw [hins]
        exact Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul a (lcmOf s))
          (Nat.Coprime.mul_right h1 h2)
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop

/-- The integral numerator is divisible by `p` exactly when the mod-`p` inverse sum vanishes
(for cofactors prime to `p`). -/
theorem dvd_cofactorNum_iff_zmod_inv_sum (p : ℕ) [hp : Fact p.Prime] {C : Finset ℕ}
    (hpos : ∀ c ∈ C, 0 < c) (hnd : ∀ c ∈ C, ¬ p ∣ c) :
    p ∣ cofactorNum C C ↔ (∑ c ∈ C, ((c : ZMod p))⁻¹) = 0 := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hL : ¬ p ∣ lcmOf C := not_dvd_lcmOf hp.out hnd
  have hLz : ((lcmOf C : ℕ) : ZMod p) ≠ 0 := fun h => hL ((ZMod.natCast_eq_zero_iff _ _).1 h)
  have hcast : ((cofactorNum C C : ℕ) : ZMod p)
      = ((lcmOf C : ℕ) : ZMod p) * ∑ c ∈ C, ((c : ZMod p))⁻¹ := by
    rw [cofactorNum]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro c hc
    have hcz : ((c : ℕ) : ZMod p) ≠ 0 := fun h => hnd c hc ((ZMod.natCast_eq_zero_iff _ _).1 h)
    obtain ⟨k, hk⟩ := Finset.dvd_lcm (f := id) hc
    have hk' : lcmOf C = c * k := hk
    have hck : lcmOf C / c = k := by
      rw [hk']
      exact Nat.mul_div_cancel_left k (hpos c hc)
    rw [hck, hk']
    push_cast
    field_simp
  constructor
  · intro h
    have h0 : ((cofactorNum C C : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
    rw [hcast] at h0
    rcases mul_eq_zero.1 h0 with h' | h'
    · exact absurd h' hLz
    · exact h'
  · intro h
    refine (ZMod.natCast_eq_zero_iff _ _).1 ?_
    rw [hcast, h, mul_zero]

/-- **`padicValRat_recipSum_iff_zmod_inv_sum`.**  `KERNEL-PROVED` bridge.  For a nonempty
finite set of positive cofactors none of which is divisible by `p`, the anchored valuation
condition is exactly the mod-`p` inverse-sum condition of the elementary top-layer package. -/
theorem padicValRat_recipSum_iff_zmod_inv_sum (p : ℕ) [hp : Fact p.Prime] {C : Finset ℕ}
    (hne : C.Nonempty) (hpos : ∀ c ∈ C, 0 < c) (hnd : ∀ c ∈ C, ¬ p ∣ c) :
    1 ≤ padicValRat p (recipSum C) ↔ (∑ c ∈ C, ((c : ZMod p))⁻¹) = 0 := by
  have hL : ¬ p ∣ lcmOf C := not_dvd_lcmOf hp.out hnd
  have ht : padicValNat p (lcmOf C) = 0 := padicValNat.eq_zero_of_not_dvd hL
  have hiff := layer_primePower_iff p (Finset.Subset.refl C) hpos hne
  rw [ht] at hiff
  rw [← hiff, pow_one]
  exact dvd_cofactorNum_iff_zmod_inv_sum p hpos hnd

/-! ## A.23  The top layer as an anchored state -/

/-- The cofactor set of the top `p`-adic layer of `A`. -/
def topCofactors (A : Finset ℕ) (p : ℕ) : Finset ℕ :=
  (topLayer A p).image (fun a => ordCompl[p] a)

/-- **`topLayer_anchoredFeasible`.**  `KERNEL-PROVED` bridge.  For a finite set `A` of
positive integers with `∑ 1/a = 1` and top `p`-adic exponent at least `1`, the cofactor set of
the top layer is anchored-feasible (with every cofactor mandatorily selected). -/
theorem topLayer_anchoredFeasible {A : Finset ℕ} {p : ℕ} (hp : p.Prime)
    (hpos : ∀ a ∈ A, 0 < a) (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) (he : 1 ≤ topExp A p) :
    AnchoredFeasible p (topCofactors A p) (topCofactors A p) ∅ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  -- the top layer is nonempty
  have hAne : A.Nonempty := by
    rcases Finset.eq_empty_or_nonempty A with rfl | h
    · simp [topExp] at he
    · exact h
  obtain ⟨a₀, ha₀A, ha₀⟩ := Finset.exists_mem_eq_sup A hAne (fun a => Nat.factorization a p)
  have ha₀top : a₀ ∈ topLayer A p := mem_topLayer.2 ⟨ha₀A, ha₀.symm⟩
  have hTne : (topLayer A p).Nonempty := ⟨a₀, ha₀top⟩
  have hCne : (topCofactors A p).Nonempty := hTne.image _
  -- the cofactors are positive and prime to `p`
  have hCpos : ∀ c ∈ topCofactors A p, 0 < c := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc
    have haA : a ∈ A := (mem_topLayer.1 ha).1
    exact Nat.ordCompl_pos p (hpos a haA).ne'
  have hCnd : ∀ c ∈ topCofactors A p, ¬ p ∣ c := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc
    have haA : a ∈ A := (mem_topLayer.1 ha).1
    exact Nat.not_dvd_ordCompl hp (hpos a haA).ne'
  -- the mod-`p` inverse sum over the cofactors is the banked top-layer congruence
  have hinj : Set.InjOn (fun a => ordCompl[p] a) (topLayer A p) := by
    intro a ha b hb hab
    have hea : Nat.factorization a p = topExp A p := (mem_topLayer.1 ha).2
    have heb : Nat.factorization b p = topExp A p := (mem_topLayer.1 hb).2
    have ra : p ^ (Nat.factorization a p) * ordCompl[p] a = a :=
      Nat.ordProj_mul_ordCompl_eq_self a p
    have rb : p ^ (Nat.factorization b p) * ordCompl[p] b = b :=
      Nat.ordProj_mul_ordCompl_eq_self b p
    have hab' : a / p ^ topExp A p = b / p ^ topExp A p := by
      have hc : ordCompl[p] a = ordCompl[p] b := hab
      rwa [hea, heb] at hc
    rw [← ra, ← rb, hea, heb, hab']
  have hsum0 : (∑ c ∈ topCofactors A p, ((c : ZMod p))⁻¹) = 0 := by
    rw [topCofactors, Finset.sum_image (fun a ha b hb h => hinj ha hb h)]
    exact topLayer_congruence A p hp hpos hsum he
  have hval : 1 ≤ padicValRat p (recipSum (topCofactors A p)) :=
    (padicValRat_recipSum_iff_zmod_inv_sum p hCne hCpos hCnd).2 hsum0
  exact ⟨topCofactors A p, mem_allowed.2 ⟨Finset.Subset.refl _, Finset.Subset.refl _, by simp⟩,
    Or.inr hval⟩

/-! ## A.24  The exact counterexample predicate -/

/-- **`counterexample_cofactorNum_eq_lcmOf`.**  `KERNEL-PROVED`.  For an exact #287
counterexample the ambient compiler identity holds in the anchored conventions. -/
theorem counterexample_cofactorNum_eq_lcmOf {A : Finset ℕ} (h : Erdos287Counterexample A) :
    cofactorNum A A = lcmOf A := by
  have hpos : ∀ a ∈ A, 0 < a := fun a ha => lt_trans Nat.zero_lt_one (h.one_lt a ha)
  have hrec : recipSum A = ((cofactorNum A A : ℕ) : ℚ) / ((lcmOf A : ℕ) : ℚ) :=
    recipSum_eq_cofactorNum_div (Finset.Subset.refl A) hpos
  have h1 : recipSum A = 1 := h.sum_one
  have hLq : ((lcmOf A : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (lcmOf_pos hpos).ne'
  rw [h1, eq_comm, div_eq_one_iff_eq hLq] at hrec
  exact_mod_cast hrec

end Anchored
end Erdos287
