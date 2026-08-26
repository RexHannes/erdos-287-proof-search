import Mathlib
import RequestProject.Erdos287.TopLayer

/-!
# Trusted bank — Erdős #287: the `p`-adic carry tower

This file formalizes the two "carry tower" statements of the bank list, in the precise
form in which they are true for a reciprocal-sum-`1` set `A`:

* `lcm_sq_dvd_prod` : `lcm(A)² ∣ ∏_{a ∈ A} a`;
* `lcm_dvd_pairwise_diff_prod` : `lcm(A) ∣ ∏_{a < b ∈ A} (b - a)`.

Both are consequences of the *non-singleton top layer* theorem
(`Erdos287.topLayer_card_ne_one`, already in the bank): for every prime `p` whose
maximal valuation `e = topExp A p` is positive, the top `p`-adic layer contains at
least two elements, each divisible by `p^e`.  This gives `2e` copies of `p` inside the
product, and one factor `b - a` divisible by `p^e` inside the pairwise-difference
product.

Note that **both statements genuinely need the reciprocal-sum hypothesis**: for a
general finite set they fail, e.g. `A = {2, 3}` has `lcm = 6`, `lcm² = 36 ∤ 6`, and
`lcm = 6 ∤ (3 - 2) = 1` (see `lcm_sq_not_dvd_prod_general`,
`lcm_not_dvd_diff_general`).
-/

open scoped BigOperators

namespace TrustedBank
namespace CarryTower

open Erdos287

/-! ## The valuation of a finite lcm -/

theorem factorization_lcm_apply {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (p : ℕ) :
    (Nat.lcm a b).factorization p = max (a.factorization p) (b.factorization p) := by
  rw [Nat.factorization_lcm ha hb]; simp [Finsupp.sup_apply]

/-- The `p`-adic valuation of `lcm A` is the maximal valuation `topExp A p`. -/
theorem factorization_finset_lcm :
    ∀ (A : Finset ℕ), (∀ a ∈ A, a ≠ 0) → ∀ p : ℕ,
      (A.lcm id).factorization p = topExp A p := by
  intro A
  classical
  induction A using Finset.induction_on with
  | empty => intro _ p; simp [topExp]
  | @insert a s ha ih =>
    intro hpos p
    have h1 : a ≠ 0 := hpos a (Finset.mem_insert_self a s)
    have hs : ∀ x ∈ s, x ≠ 0 := fun x hx => hpos x (Finset.mem_insert_of_mem hx)
    have h2 : (s.lcm id) ≠ 0 := Finset.lcm_ne_zero_iff.mpr hs
    rw [Finset.lcm_insert]
    have : (lcm (id a) (s.lcm id)) = Nat.lcm a (s.lcm id) := rfl
    rw [this, factorization_lcm_apply h1 h2, ih hs p]
    simp [topExp, Finset.sup_insert]

/-! ## Two elements in the top layer -/

/-- If the maximal `p`-adic valuation is positive, then `p` is prime and the top layer
has at least two elements. -/
theorem two_le_card_topLayer (A : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hpos : ∀ a ∈ A, 0 < a) (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) (he : 1 ≤ topExp A p) :
    2 ≤ (topLayer A p).card := by
  have hne1 : (topLayer A p).card ≠ 1 := topLayer_card_ne_one A p hp hpos hsum he
  have hAne : A.Nonempty := by
    rcases Finset.eq_empty_or_nonempty A with rfl | h
    · simp [topExp] at he
    · exact h
  obtain ⟨a, haA, ha⟩ := Finset.exists_mem_eq_sup A hAne (fun a => Nat.factorization a p)
  have hmem : a ∈ topLayer A p := mem_topLayer.2 ⟨haA, ha.symm⟩
  have hne0 : (topLayer A p).card ≠ 0 := by
    intro h
    rw [Finset.card_eq_zero] at h
    simp [h] at hmem
  omega

/-- Two distinct elements of the top layer, in increasing order. -/
theorem exists_two_topLayer (A : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hpos : ∀ a ∈ A, 0 < a) (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) (he : 1 ≤ topExp A p) :
    ∃ a b, a ∈ topLayer A p ∧ b ∈ topLayer A p ∧ a < b := by
  have h2 := two_le_card_topLayer A p hp hpos hsum he
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    Finset.one_lt_card.mp (show 1 < (topLayer A p).card by omega)
  rcases lt_or_gt_of_ne hxy with h | h
  · exact ⟨x, y, hx, hy, h⟩
  · exact ⟨y, x, hy, hx, h⟩

/-- Every element of the top layer is divisible by `p^e`. -/
theorem pow_topExp_dvd_of_mem_topLayer {A : Finset ℕ} {p a : ℕ} (ha : a ∈ topLayer A p) :
    p ^ (topExp A p) ∣ a := by
  obtain ⟨-, hval⟩ := mem_topLayer.1 ha
  rw [← hval]
  exact Nat.ordProj_dvd a p

/-! ## Carry tower: the levels of the `p`-adic filtration -/

/-- The `k`-th level of the `p`-adic filtration of `A`. -/
def level (A : Finset ℕ) (p k : ℕ) : Finset ℕ := A.filter (fun a => p ^ k ∣ a)

theorem level_succ_subset (A : Finset ℕ) (p k : ℕ) : level A p (k + 1) ⊆ level A p k := by
  intro a ha
  simp only [level, Finset.mem_filter] at ha ⊢
  exact ⟨ha.1, dvd_trans (pow_dvd_pow p (Nat.le_succ k)) ha.2⟩

theorem topLayer_subset_level (A : Finset ℕ) (p : ℕ) :
    topLayer A p ⊆ level A p (topExp A p) := by
  intro a ha
  exact Finset.mem_filter.2 ⟨(mem_topLayer.1 ha).1, pow_topExp_dvd_of_mem_topLayer ha⟩

/-- Above the top exponent the tower is empty: no element of `A` is divisible by
`p^(e+1)`. -/
theorem level_succ_topExp_eq_empty (A : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hpos : ∀ a ∈ A, 0 < a) : level A p (topExp A p + 1) = ∅ := by
  ext a
  simp only [level, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
  intro haA hdvd
  have hane : a ≠ 0 := (hpos a haA).ne'
  have := (Nat.Prime.pow_dvd_iff_le_factorization hp hane).1 hdvd
  have hle : Nat.factorization a p ≤ topExp A p := Finset.le_sup (f := fun a => Nat.factorization a p) haA
  omega

/-! ## `lcm(A)² ∣ ∏ a` -/

/-- **Carry tower I.**  For a finite set of positive integers whose reciprocals sum to
`1`, the square of the lcm divides the product. -/
theorem lcm_sq_dvd_prod (A : Finset ℕ) (hpos : ∀ a ∈ A, 0 < a)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) :
    (A.lcm id) ^ 2 ∣ ∏ a ∈ A, a := by
  have hne : ∀ a ∈ A, a ≠ 0 := fun a ha => (hpos a ha).ne'
  have hL : A.lcm id ≠ 0 := Finset.lcm_ne_zero_iff.mpr hne
  have hP : (∏ a ∈ A, a) ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 hL) hP]
  rw [Finsupp.le_iff]
  intro p _
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    factorization_finset_lcm A hne p, Nat.factorization_prod (fun a ha => hne a ha),
    Finset.sum_apply']
  rcases Nat.eq_zero_or_pos (topExp A p) with h0 | he
  · simp [h0]
  · -- `p` must be prime and the top layer has at least two elements
    have hprime : p.Prime := by
      by_contra hp
      have hAne : A.Nonempty := by
        rcases Finset.eq_empty_or_nonempty A with rfl | h
        · simp [topExp] at he
        · exact h
      obtain ⟨a, haA, ha⟩ := Finset.exists_mem_eq_sup A hAne (fun a => Nat.factorization a p)
      have hzero : Nat.factorization a p = 0 := Nat.factorization_eq_zero_of_not_prime a hp
      have h0 : topExp A p = 0 := by
        show (A.sup fun a => Nat.factorization a p) = 0
        exact ha.trans hzero
      omega
    have h2 := two_le_card_topLayer A p hprime hpos hsum he
    have hsub : topLayer A p ⊆ A := topLayer_subset A p
    have hstep : ∑ a ∈ topLayer A p, Nat.factorization a p ≤ ∑ a ∈ A, Nat.factorization a p :=
      Finset.sum_le_sum_of_subset hsub
    have heq : ∑ a ∈ topLayer A p, Nat.factorization a p
        = (topLayer A p).card * topExp A p := by
      rw [Finset.sum_congr rfl (fun a ha => (mem_topLayer.1 ha).2), Finset.sum_const,
        smul_eq_mul]
    have : 2 * topExp A p ≤ (topLayer A p).card * topExp A p := by
      exact Nat.mul_le_mul_right _ h2
    omega

/-! ## `lcm(A) ∣ ∏_{a < b} (b - a)` -/

/-- The set of increasing pairs of `A`. -/
def pairs (A : Finset ℕ) : Finset (ℕ × ℕ) := A.offDiag.filter (fun q => q.1 < q.2)

theorem mem_pairs {A : Finset ℕ} {q : ℕ × ℕ} :
    q ∈ pairs A ↔ q.1 ∈ A ∧ q.2 ∈ A ∧ q.1 < q.2 := by
  simp only [pairs, Finset.mem_filter, Finset.mem_offDiag]
  constructor
  · rintro ⟨⟨h1, h2, -⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2, by omega⟩, h3⟩

/-- **Carry tower II.**  For a finite set of positive integers whose reciprocals sum to
`1`, the lcm divides the product of all pairwise differences. -/
theorem lcm_dvd_pairwise_diff_prod (A : Finset ℕ) (hpos : ∀ a ∈ A, 0 < a)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) :
    (A.lcm id) ∣ ∏ q ∈ pairs A, (q.2 - q.1) := by
  have hne : ∀ a ∈ A, a ≠ 0 := fun a ha => (hpos a ha).ne'
  have hL : A.lcm id ≠ 0 := Finset.lcm_ne_zero_iff.mpr hne
  have hfac : ∀ q ∈ pairs A, q.2 - q.1 ≠ 0 := by
    intro q hq
    have := (mem_pairs.1 hq).2.2
    omega
  have hD : (∏ q ∈ pairs A, (q.2 - q.1)) ≠ 0 := Finset.prod_ne_zero_iff.mpr hfac
  rw [← Nat.factorization_le_iff_dvd hL hD, Finsupp.le_iff]
  intro p _
  rw [factorization_finset_lcm A hne p, Nat.factorization_prod hfac, Finset.sum_apply']
  rcases Nat.eq_zero_or_pos (topExp A p) with h0 | he
  · simp [h0]
  · have hprime : p.Prime := by
      by_contra hp
      have hAne : A.Nonempty := by
        rcases Finset.eq_empty_or_nonempty A with rfl | h
        · simp [topExp] at he
        · exact h
      obtain ⟨a, haA, ha⟩ := Finset.exists_mem_eq_sup A hAne (fun a => Nat.factorization a p)
      have hzero : Nat.factorization a p = 0 := Nat.factorization_eq_zero_of_not_prime a hp
      have h0 : topExp A p = 0 := by
        show (A.sup fun a => Nat.factorization a p) = 0
        exact ha.trans hzero
      omega
    obtain ⟨a, b, ha, hb, hab⟩ := exists_two_topLayer A p hprime hpos hsum he
    have hqmem : (a, b) ∈ pairs A :=
      mem_pairs.2 ⟨(mem_topLayer.1 ha).1, (mem_topLayer.1 hb).1, hab⟩
    have hdvd : p ^ (topExp A p) ∣ b - a :=
      Nat.dvd_sub (pow_topExp_dvd_of_mem_topLayer hb) (pow_topExp_dvd_of_mem_topLayer ha)
    have hbne : b - a ≠ 0 := by omega
    have hle : topExp A p ≤ Nat.factorization (b - a) p :=
      (Nat.Prime.pow_dvd_iff_le_factorization hprime hbne).1 hdvd
    have hsingle : Nat.factorization ((a, b).2 - (a, b).1) p
        ≤ ∑ q ∈ pairs A, Nat.factorization (q.2 - q.1) p :=
      Finset.single_le_sum (f := fun q : ℕ × ℕ => Nat.factorization (q.2 - q.1) p)
        (fun q _ => Nat.zero_le _) hqmem
    simp only at hsingle
    omega

/-! ## The reciprocal-sum hypothesis is necessary -/

/-- For a general finite set the square of the lcm need not divide the product:
`A = {2, 3}` has `lcm² = 36 ∤ 6`. -/
theorem lcm_sq_not_dvd_prod_general :
    ¬ ((({2, 3} : Finset ℕ).lcm id) ^ 2 ∣ ∏ a ∈ ({2, 3} : Finset ℕ), a) := by
  decide

/-- For a general finite set the lcm need not divide the pairwise-difference product:
`A = {2, 3}` has `lcm = 6 ∤ (3 - 2) = 1`. -/
theorem lcm_not_dvd_diff_general :
    ¬ ((({2, 3} : Finset ℕ).lcm id) ∣ ∏ q ∈ pairs ({2, 3} : Finset ℕ), (q.2 - q.1)) := by
  decide

end CarryTower
end TrustedBank
