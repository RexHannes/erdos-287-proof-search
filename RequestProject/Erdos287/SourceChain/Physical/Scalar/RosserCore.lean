import Mathlib

/-!
# Erdős #287 — scalar sieve: the combinatorial Rosser (β-sieve) inequality

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

Generic finite combinatorics behind the pointwise sieve inequalities for the
upper/lower linear-sieve supports `𝒟^±(D)` (Pascadi, arXiv:2505.00653v2, Definition 5.1) and for
Lichtman's parity-dependent box supports `𝐃_r^+` (Lichtman, arXiv:2109.02851v2, §5).

A squarefree number is encoded by its (finite) set of prime factors, listed in *decreasing*
order `p_1 > p_2 > ⋯`.  The position of `p ∈ S` in that list is `1 + #{q ∈ S : p < q}`, so
"odd position" means `Even #{q ∈ S : p < q}`.

* `rosserSum D s R = ∑_{S ⊆ R} 1_{D(s ∪ S)} (-1)^{|S|}`;
* `rosserSum_insert` — peeling an element;
* `rosser_upper` / `rosser_lower` — if `D` is closed under deleting the smallest element and
  membership can only fail at odd (resp. even) positions, then
  `∑_{S ⊆ T, D S} (-1)^{|S|} ≥ 1_{T=∅}` (resp. `≤ 1_{T=∅}`);
* `exists_odd_position_witness` / `exists_even_position_witness` — the product of a monotone
  weight `f ≥ 1` over `S` is controlled by the condition at a single odd (resp. even, or first)
  position.  This gives the level bounds of the supports.
-/

open scoped BigOperators
open Finset

namespace Erdos287.Physical.Sieve

variable {α : Type*} [LinearOrder α]

/-- `G(s, R) = ∑_{S ⊆ R} 1_{D(s ∪ S)} (-1)^{|S|}`. -/
def rosserSum (D : Finset α → Prop) [DecidablePred D] (s R : Finset α) : ℤ :=
  ∑ S ∈ R.powerset, if D (s ∪ S) then (-1) ^ S.card else 0

/-- Peeling an element `a ∉ R`: `G(s, R ∪ {a}) = G(s, R) - G(s ∪ {a}, R)`. -/
theorem rosserSum_insert (D : Finset α → Prop) [DecidablePred D] (s R : Finset α) {a : α}
    (ha : a ∉ R) :
    rosserSum D s (insert a R) = rosserSum D s R - rosserSum D (insert a s) R := by
  unfold rosserSum
  rw [Finset.sum_powerset_insert ha, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun S hS => ?_)
  have haS : a ∉ S := fun h => ha (Finset.mem_powerset.1 hS h)
  rw [Finset.card_insert_of_notMem haS,
    show s ∪ insert a S = insert a s ∪ S by
      ext x; simp only [mem_union, mem_insert]; tauto]
  split_ifs <;> simp [pow_succ]

/-- The generic parity-sensitive Rosser inequality.  `E` is the parity of `|s|` at which an
extension by a smaller element is automatic (`Odd` for the upper sieve, `Even` for the lower). -/
theorem rosser_generic (D : Finset α → Prop) [DecidablePred D] (U : α → Prop) (E : ℕ → Prop)
    (hE : ∀ n, E (n + 1) ↔ ¬ E n)
    (hpre : ∀ s p, (∀ x ∈ s, p < x) → D (insert p s) → D s)
    (hext : ∀ s p, U p → (∀ x ∈ s, p < x) → E s.card → D s → D (insert p s)) :
    ∀ R : Finset α, (∀ x ∈ R, U x) → ∀ s : Finset α, (∀ x ∈ R, ∀ y ∈ s, x < y) →
      (¬ E s.card → (if D s ∧ R = ∅ then (1 : ℤ) else 0) ≤ rosserSum D s R) ∧
      (E s.card → rosserSum D s R ≤ if D s ∧ R = ∅ then (1 : ℤ) else 0) := by
  intro R
  induction R using Finset.induction_on_max with
  | h0 =>
    intro _ s _
    have : rosserSum D s ∅ = if D s ∧ (∅ : Finset α) = ∅ then 1 else 0 := by
      simp [rosserSum]
    exact ⟨fun _ => this.ge, fun _ => this.le⟩
  | step a R hlt ih =>
    intro hU s hRs
    have haR : a ∉ R := fun h => lt_irrefl a (hlt a h)
    have hUR : ∀ x ∈ R, U x := fun x hx => hU x (mem_insert_of_mem hx)
    have hUa : U a := hU a (mem_insert_self a R)
    have has : ∀ y ∈ s, a < y := fun y hy => hRs a (mem_insert_self a R) y hy
    have hRs' : ∀ x ∈ R, ∀ y ∈ s, x < y := fun x hx y hy => hRs x (mem_insert_of_mem hx) y hy
    have hRas : ∀ x ∈ R, ∀ y ∈ insert a s, x < y := by
      intro x hx y hy
      rcases mem_insert.1 hy with rfl | hy
      · exact hlt x hx
      · exact hRs' x hx y hy
    have hcard : (insert a s).card = s.card + 1 :=
      card_insert_of_notMem (fun h => lt_irrefl a (has a h))
    have hne : ¬ (D s ∧ insert a R = ∅) := fun h => (insert_ne_empty a R) h.2
    rw [rosserSum_insert D s R haR, if_neg hne]
    obtain ⟨ih1, ih2⟩ := ih hUR s hRs'
    obtain ⟨ih3, ih4⟩ := ih hUR (insert a s) hRas
    rw [hcard] at ih3 ih4
    refine ⟨fun hs => ?_, fun hs => ?_⟩
    · have h1 := ih1 hs
      have h2 := ih4 ((hE _).2 hs)
      have h3 : (if D (insert a s) ∧ R = ∅ then (1 : ℤ) else 0) ≤
          (if D s ∧ R = ∅ then (1 : ℤ) else 0) := by
        by_cases h : D (insert a s) ∧ R = ∅
        · rw [if_pos h, if_pos ⟨hpre s a has h.1, h.2⟩]
        · rw [if_neg h]; split_ifs <;> norm_num
      linarith
    · have h1 := ih2 hs
      have h2 := ih3 (fun h => ((hE _).1 h) hs)
      have h3 : (if D (insert a s) ∧ R = ∅ then (1 : ℤ) else 0) =
          (if D s ∧ R = ∅ then (1 : ℤ) else 0) := by
        have : D (insert a s) ↔ D s := ⟨hpre s a has, hext s a hUa has hs⟩
        simp only [this]
      linarith

/-- **Upper Rosser inequality**: conditions only at odd positions. -/
theorem rosser_upper (D : Finset α → Prop) [DecidablePred D] (U : α → Prop) (hD0 : D ∅)
    (hpre : ∀ s p, (∀ x ∈ s, p < x) → D (insert p s) → D s)
    (hext : ∀ s p, U p → (∀ x ∈ s, p < x) → Odd s.card → D s → D (insert p s))
    (T : Finset α) (hT : ∀ x ∈ T, U x) :
    (if T = ∅ then (1 : ℤ) else 0) ≤ ∑ S ∈ T.powerset, if D S then (-1) ^ S.card else 0 := by
  have := (rosser_generic D U Odd (fun n => Nat.odd_add_one) hpre hext T hT ∅
    (by simp)).1 (by simp)
  simpa [rosserSum, hD0] using this

/-- **Lower Rosser inequality**: conditions only at even positions (plus an arbitrary
condition at the first position, encoded in `U`). -/
theorem rosser_lower (D : Finset α → Prop) [DecidablePred D] (U : α → Prop)
    (hpre : ∀ s p, (∀ x ∈ s, p < x) → D (insert p s) → D s)
    (hext : ∀ s p, U p → (∀ x ∈ s, p < x) → Even s.card → D s → D (insert p s))
    (T : Finset α) (hT : ∀ x ∈ T, U x) :
    (∑ S ∈ T.powerset, if D S then (-1) ^ S.card else 0) ≤ if T = ∅ then (1 : ℤ) else 0 := by
  have := (rosser_generic D U Even (fun n => Nat.even_add_one) hpre hext T hT ∅
    (by simp)).2 (by simp)
  have h2 : (if D ∅ ∧ T = ∅ then (1 : ℤ) else 0) ≤ if T = ∅ then 1 else 0 := by
    split_ifs <;> simp_all
  exact (by simpa [rosserSum] using this : _ ≤ _).trans h2

/-! ### Level witnesses -/

/-- The elements of `S` above `p` (the primes preceding `p` in decreasing order). -/
def above (S : Finset α) (p : α) : Finset α := S.filter (fun q => p < q)

theorem above_insert_of_lt {s : Finset α} {p q : α} (hp : ∀ x ∈ s, p < x) (hq : q ∈ s) :
    above (insert p s) q = above s q := by
  ext x
  simp only [above, mem_filter, mem_insert]
  constructor
  · rintro ⟨rfl | hx, hqx⟩
    · exact absurd (hp q hq) (not_lt.2 hqx.le)
    · exact ⟨hx, hqx⟩
  · rintro ⟨hx, hqx⟩; exact ⟨Or.inr hx, hqx⟩

theorem above_insert_self {s : Finset α} {p : α} (hp : ∀ x ∈ s, p < x) :
    above (insert p s) p = s := by
  ext x
  simp only [above, mem_filter, mem_insert]
  constructor
  · rintro ⟨rfl | hx, hpx⟩
    · exact absurd hpx (lt_irrefl _)
    · exact hx
  · intro hx; exact ⟨Or.inr hx, hp x hx⟩

theorem above_min (S : Finset α) (hS : S.Nonempty) :
    above S (S.min' hS) = S.erase (S.min' hS) := by
  ext x
  simp only [above, mem_filter, mem_erase]
  constructor
  · rintro ⟨hx, hlt⟩; exact ⟨ne_of_gt hlt, hx⟩
  · rintro ⟨hne, hx⟩; exact ⟨hx, lt_of_le_of_ne (S.min'_le x hx) (Ne.symm hne)⟩

theorem above_second (S : Finset α) (hS : S.Nonempty) (hne : (S.erase (S.min' hS)).Nonempty) :
    above S ((S.erase (S.min' hS)).min' hne) =
      (S.erase (S.min' hS)).erase ((S.erase (S.min' hS)).min' hne) := by
  set m := S.min' hS
  set m2 := (S.erase m).min' hne
  have hm2 : m2 ∈ S.erase m := (S.erase m).min'_mem hne
  have hm2S : m2 ∈ S := mem_of_mem_erase hm2
  have hmm2 : m < m2 := lt_of_le_of_ne (S.min'_le m2 hm2S) (Ne.symm (ne_of_mem_erase hm2))
  ext x
  simp only [above, mem_filter, mem_erase]
  constructor
  · rintro ⟨hx, hlt⟩
    exact ⟨ne_of_gt hlt, ne_of_gt (hmm2.trans hlt), hx⟩
  · rintro ⟨h2, h1, hx⟩
    exact ⟨hx, lt_of_le_of_ne ((S.erase m).min'_le x (mem_erase.2 ⟨h1, hx⟩)) (Ne.symm h2)⟩

/-- Two-smallest-elements product bound used by both witnesses. -/
theorem prod_le_second (f : α → ℝ) (S : Finset α) (hS : S.Nonempty)
    (hne : (S.erase (S.min' hS)).Nonempty)
    (hf1 : ∀ x ∈ S, 1 ≤ f x) (hmono : ∀ x ∈ S, ∀ y ∈ S, x ≤ y → f x ≤ f y) :
    ∏ q ∈ S, f q ≤ (∏ q ∈ (S.erase (S.min' hS)).erase ((S.erase (S.min' hS)).min' hne), f q) *
      f ((S.erase (S.min' hS)).min' hne) ^ 2 := by
  set m := S.min' hS
  set m2 := (S.erase m).min' hne
  have hm : m ∈ S := S.min'_mem hS
  have hm2 : m2 ∈ S.erase m := (S.erase m).min'_mem hne
  have hm2S : m2 ∈ S := mem_of_mem_erase hm2
  have hmm2 : m < m2 := lt_of_le_of_ne (S.min'_le m2 hm2S) (Ne.symm (ne_of_mem_erase hm2))
  rw [← Finset.mul_prod_erase S f hm, ← Finset.mul_prod_erase (S.erase m) f hm2]
  have h0 : 0 ≤ ∏ q ∈ (S.erase m).erase m2, f q := Finset.prod_nonneg (fun x hx => by
    linarith [hf1 x (mem_of_mem_erase (mem_of_mem_erase hx))])
  have h1 := hf1 m hm
  have h2 := hmono m hm m2 hm2S hmm2.le
  have h3 : f m * (f m2 * ∏ q ∈ (S.erase m).erase m2, f q) ≤
      f m2 * (f m2 * ∏ q ∈ (S.erase m).erase m2, f q) := by
    apply mul_le_mul_of_nonneg_right h2
    exact mul_nonneg (by linarith) h0
  calc f m * (f m2 * ∏ q ∈ (S.erase m).erase m2, f q)
      ≤ f m2 * (f m2 * ∏ q ∈ (S.erase m).erase m2, f q) := h3
    _ = (∏ q ∈ (S.erase m).erase m2, f q) * f m2 ^ 2 := by ring

theorem prod_le_first (f : α → ℝ) (S : Finset α) (hS : S.Nonempty)
    (hf1 : ∀ x ∈ S, 1 ≤ f x) :
    ∏ q ∈ S, f q ≤ (∏ q ∈ S.erase (S.min' hS), f q) * f (S.min' hS) ^ 2 := by
  have hm : S.min' hS ∈ S := S.min'_mem hS
  rw [← Finset.mul_prod_erase S f hm, mul_comm, pow_two]
  have h0 : 0 ≤ ∏ q ∈ S.erase (S.min' hS), f q := Finset.prod_nonneg (fun x hx => by
    linarith [hf1 x (mem_of_mem_erase hx)])
  have := hf1 _ hm
  have h3 : (∏ q ∈ S.erase (S.min' hS), f q) * 1 ≤
      (∏ q ∈ S.erase (S.min' hS), f q) * f (S.min' hS) := mul_le_mul_of_nonneg_left this h0
  nlinarith

/-- A monotone weight `f ≥ 1` on a nonempty `S`: the full product is bounded by
`(∏_{above p} f) · f(p)^2` for some `p` at an **odd** position (`Even #above`). -/
theorem exists_odd_position_witness (f : α → ℝ) (S : Finset α) (hS : S.Nonempty)
    (hf1 : ∀ x ∈ S, 1 ≤ f x) (hmono : ∀ x ∈ S, ∀ y ∈ S, x ≤ y → f x ≤ f y) :
    ∃ p ∈ S, Even (above S p).card ∧ ∏ q ∈ S, f q ≤ (∏ q ∈ above S p, f q) * f p ^ 2 := by
  by_cases hev : Even (S.erase (S.min' hS)).card
  · exact ⟨_, S.min'_mem hS, by rw [above_min]; exact hev,
      by rw [above_min]; exact prod_le_first f S hS hf1⟩
  · have hne : (S.erase (S.min' hS)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro h; rw [h] at hev; exact hev (by simp)
    have hm2 := (S.erase (S.min' hS)).min'_mem hne
    refine ⟨_, mem_of_mem_erase hm2, ?_, ?_⟩
    · rw [above_second S hS hne, card_erase_of_mem hm2]
      rcases Nat.not_even_iff_odd.1 hev with ⟨k, hk⟩
      rw [hk]; simp
    · rw [above_second S hS hne]; exact prod_le_second f S hS hne hf1 hmono

/-- A monotone weight `f ≥ 1` on a nonempty `S`: the full product is bounded by
`(∏_{above p} f) · f(p)^2` for some `p` at an **even** position, or for the **largest**
element (first position, `above = ∅`). -/
theorem exists_even_position_witness (f : α → ℝ) (S : Finset α) (hS : S.Nonempty)
    (hf1 : ∀ x ∈ S, 1 ≤ f x) (hmono : ∀ x ∈ S, ∀ y ∈ S, x ≤ y → f x ≤ f y) :
    ∃ p ∈ S, (Odd (above S p).card ∨ above S p = ∅) ∧
      ∏ q ∈ S, f q ≤ (∏ q ∈ above S p, f q) * f p ^ 2 := by
  have hbase := prod_le_first f S hS hf1
  rw [← above_min] at hbase
  by_cases hodd : Odd (S.erase (S.min' hS)).card
  · exact ⟨_, S.min'_mem hS, Or.inl (by rw [above_min]; exact hodd), hbase⟩
  · by_cases hemp : S.erase (S.min' hS) = ∅
    · exact ⟨_, S.min'_mem hS, Or.inr (by rw [above_min]; exact hemp), hbase⟩
    have hne : (S.erase (S.min' hS)).Nonempty := Finset.nonempty_iff_ne_empty.2 hemp
    have hm2 := (S.erase (S.min' hS)).min'_mem hne
    refine ⟨_, mem_of_mem_erase hm2, Or.inl ?_, ?_⟩
    · rw [above_second S hS hne, card_erase_of_mem hm2]
      rcases Nat.not_odd_iff_even.1 hodd with ⟨k, hk⟩
      have hk0 : k ≠ 0 := by
        rintro rfl; simp at hk; exact hemp hk
      obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      rw [hk]; exact ⟨k', by omega⟩
    · rw [above_second S hS hne]; exact prod_le_second f S hS hne hf1 hmono

end Erdos287.Physical.Sieve
