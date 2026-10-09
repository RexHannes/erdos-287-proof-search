import Mathlib

/-!
# Erdős #287 — post-V87 → V90R: the V90 cyclic contact graph

**ERDŐS #287 REMAINS OPEN.  This file is pure finite combinatorics.**

`ContactCycle r m` is the graph on `ZMod r` in which `x ~ y` iff the cyclic difference
`(y - x).val` lies in the *useful* range `m, m+1, …, r - m` (the circular complete graph
usually written `K_{r/m}`).  In the V90 notation `G(r, k)` the non-edges are the pairs at
cyclic distance `≤ k`, so `G(r, k) = ContactCycle r (k+1)`; we provide the abbreviation `G r k`.

Main results (all unconditional):

* `alpha_contactCycle` — for `1 ≤ m` and `2m ≤ r`, `α(ContactCycle r m) = m`;
  equivalently `α(G(r, m-1)) = m` (`alpha_G`).  The upper bound is a general proof via a
  Cauchy–Davenport-type estimate for sums with an interval in `ZMod r`
  (`card_shiftSet_ge`); no finite enumeration is used.
* `alpha_G_11_2` — `α(G(11,2)) = 3`, whose useful differences are `3,…,8`
  (`G_11_2_adj_iff`), plus the independent `decide` regression check
  `G_11_2_four_subsets_have_edge`.
* `width_ratio` — for `r = 4m+1`, `(r - m)/m = 3 + 1/m`; `widthParam_spec` — for every real
  `s > 3`, the explicit `m = ⌊1/(s-3)⌋₊ + 1 ≥ 1` satisfies `3 + 1/m < s`.
-/

open scoped BigOperators
open Classical

namespace Erdos287.PostV87V90R

/-- The useful-difference relation: `(y - x).val ∈ [m, r - m]`. -/
def UsefulDiff (r m : ℕ) (x y : ZMod r) : Prop := m ≤ (y - x).val ∧ (y - x).val ≤ r - m

/-- **The cyclic contact graph** on `ZMod r` with useful differences `m, …, r - m`. -/
def ContactCycle (r m : ℕ) [NeZero r] : SimpleGraph (ZMod r) where
  Adj x y := x ≠ y ∧ UsefulDiff r m x y
  symm := by
    intro x y ⟨hne, h1, h2⟩
    refine ⟨hne.symm, ?_⟩
    have hxy : x - y = -(y - x) := by ring
    have hz : y - x ≠ 0 := sub_ne_zero.mpr hne.symm
    have hlt := ZMod.val_lt (y - x)
    unfold UsefulDiff
    rw [hxy, ZMod.neg_val, if_neg hz]
    omega
  loopless := ⟨fun x h => h.1 rfl⟩

instance (r m : ℕ) [NeZero r] : DecidableRel (ContactCycle r m).Adj := fun x y => by
  unfold ContactCycle UsefulDiff; infer_instance

theorem contactCycle_adj_iff {r m : ℕ} [NeZero r] {x y : ZMod r} :
    (ContactCycle r m).Adj x y ↔ x ≠ y ∧ m ≤ (y - x).val ∧ (y - x).val ≤ r - m := Iff.rfl

/-- V90 notation: `G(r, k)` has non-edges at cyclic distance `≤ k`, i.e. useful differences
`k+1, …, r-k-1`. -/
abbrev G (r k : ℕ) [NeZero r] : SimpleGraph (ZMod r) := ContactCycle r (k + 1)

/-! ## Independence number (finite) -/

section Indep

variable {V : Type*} [Fintype V]

/-- A finset is independent if it contains no edge. -/
def IndepFinset (Γ : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ¬ Γ.Adj x y

/-- The independence number `α(Γ)` (maximum cardinality of an independent finset). -/
noncomputable def alpha (Γ : SimpleGraph V) : ℕ :=
  ((Finset.univ : Finset (Finset V)).filter (IndepFinset Γ)).sup Finset.card

theorem card_le_alpha {Γ : SimpleGraph V} {S : Finset V} (h : IndepFinset Γ S) :
    S.card ≤ alpha Γ :=
  Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)

theorem alpha_le {Γ : SimpleGraph V} {k : ℕ}
    (h : ∀ S : Finset V, IndepFinset Γ S → S.card ≤ k) : alpha Γ ≤ k :=
  Finset.sup_le fun S hS => h S (Finset.mem_filter.1 hS).2

/-- **Pigeonhole consumer.**  A finset with more than `α(Γ)` elements contains an edge. -/
theorem exists_adj_of_alpha_lt {Γ : SimpleGraph V} {S : Finset V} (h : alpha Γ < S.card) :
    ∃ x ∈ S, ∃ y ∈ S, Γ.Adj x y := by
  by_contra hc
  push_neg at hc
  have := card_le_alpha (Γ := Γ) (S := S) hc
  omega

/-- `α` is attained. -/
theorem exists_indep_card_alpha (Γ : SimpleGraph V) :
    ∃ S : Finset V, IndepFinset Γ S ∧ S.card = alpha Γ := by
  obtain ⟨S, hS, h⟩ := Finset.exists_mem_eq_sup
    ((Finset.univ : Finset (Finset V)).filter (IndepFinset Γ))
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [IndepFinset]⟩⟩ Finset.card
  exact ⟨S, (Finset.mem_filter.1 hS).2, h.symm⟩

end Indep

/-! ## Sums with an interval in `ZMod r` -/

section Sumset

variable {r : ℕ} [NeZero r]

/-- A nonempty subset of `ZMod r` closed under `+1` is everything. -/
theorem eq_univ_of_add_one_closed {T : Finset (ZMod r)} (hne : T.Nonempty)
    (h : ∀ x ∈ T, x + 1 ∈ T) : T = Finset.univ := by
  obtain ⟨x0, hx0⟩ := hne
  have hall : ∀ n : ℕ, x0 + (n : ZMod r) ∈ T := by
    intro n
    induction n with
    | zero => simpa using hx0
    | succ n ih =>
      have := h _ ih
      simpa [add_assoc] using this
  ext y
  simp only [Finset.mem_univ, iff_true]
  have := hall (y - x0).val
  rwa [ZMod.natCast_zmod_val, add_sub_cancel] at this

/-- The shifted interval sum `S + {c, c+1, …, c+L-1}`. -/
noncomputable def shiftSet (S : Finset (ZMod r)) (c L : ℕ) : Finset (ZMod r) :=
  Finset.univ.filter (fun x => ∃ s ∈ S, ∃ k < L, x = s + ((c + k : ℕ) : ZMod r))

theorem mem_shiftSet {S : Finset (ZMod r)} {c L : ℕ} {x : ZMod r} :
    x ∈ shiftSet S c L ↔ ∃ s ∈ S, ∃ k < L, x = s + ((c + k : ℕ) : ZMod r) := by
  simp [shiftSet]

theorem shiftSet_mono {S : Finset (ZMod r)} {c L : ℕ} :
    shiftSet S c L ⊆ shiftSet S c (L + 1) := by
  intro x hx
  obtain ⟨s, hs, k, hk, rfl⟩ := mem_shiftSet.1 hx
  exact mem_shiftSet.2 ⟨s, hs, k, by omega, rfl⟩

theorem add_one_mem_shiftSet {S : Finset (ZMod r)} {c L : ℕ} {x : ZMod r}
    (hx : x ∈ shiftSet S c L) : x + 1 ∈ shiftSet S c (L + 1) := by
  obtain ⟨s, hs, k, hk, rfl⟩ := mem_shiftSet.1 hx
  refine mem_shiftSet.2 ⟨s, hs, k + 1, by omega, ?_⟩
  push_cast; ring

theorem card_shiftSet_one (S : Finset (ZMod r)) (c : ℕ) :
    (shiftSet S c 1).card = S.card := by
  have : shiftSet S c 1 = S.image (fun s => s + (c : ZMod r)) := by
    ext x
    simp only [mem_shiftSet, Finset.mem_image]
    constructor
    · rintro ⟨s, hs, k, hk, rfl⟩
      have : k = 0 := by omega
      subst this
      exact ⟨s, hs, by simp⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, 0, by omega, by simp⟩
  rw [this, Finset.card_image_of_injective _ (add_left_injective _)]

/-- **Cauchy–Davenport-type bound for an interval.**  For nonempty `S ⊆ ZMod r` and
`L ≥ 1`, `|S + {c, …, c+L-1}| ≥ min(r, |S| + L - 1)`. -/
theorem card_shiftSet_ge {S : Finset (ZMod r)} (hS : S.Nonempty) (c : ℕ) :
    ∀ L : ℕ, 1 ≤ L → min r (S.card + L - 1) ≤ (shiftSet S c L).card := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base =>
    rw [card_shiftSet_one]
    exact min_le_right _ _
  | succ L hL ih =>
    by_cases hu : shiftSet S c L = Finset.univ
    · have h1 : (shiftSet S c L).card ≤ (shiftSet S c (L + 1)).card :=
        Finset.card_le_card shiftSet_mono
      rw [hu, Finset.card_univ, ZMod.card] at h1
      exact le_trans (min_le_left _ _) h1
    · have hne : (shiftSet S c L).Nonempty := by
        obtain ⟨s, hs⟩ := hS
        exact ⟨s + ((c + 0 : ℕ) : ZMod r), mem_shiftSet.2 ⟨s, hs, 0, by omega, rfl⟩⟩
      have : ¬ ∀ x ∈ shiftSet S c L, x + 1 ∈ shiftSet S c L :=
        fun h => hu (eq_univ_of_add_one_closed hne h)
      push_neg at this
      obtain ⟨x, hx, hx1⟩ := this
      have hsub : insert (x + 1) (shiftSet S c L) ⊆ shiftSet S c (L + 1) := by
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact add_one_mem_shiftSet hx
        · exact shiftSet_mono hy
      have h2 := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hx1] at h2
      have : min r (S.card + (L + 1) - 1) ≤ min r (S.card + L - 1) + 1 := by omega
      omega

end Sumset

/-! ## `α(ContactCycle r m) = m` -/

section Alpha

variable {r m : ℕ} [NeZero r]

/-- **Upper bound.**  Every independent set of `ContactCycle r m` (`1 ≤ m`, `2m ≤ r`) has at
most `m` elements. -/
theorem indep_card_le (hm : 1 ≤ m) (hr : 2 * m ≤ r) {S : Finset (ZMod r)}
    (hS : IndepFinset (ContactCycle r m) S) : S.card ≤ m := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hdisj : Disjoint (shiftSet S m (r - 2 * m + 1)) S := by
    rw [Finset.disjoint_left]
    intro x hx hxS
    obtain ⟨s, hs, k, hk, rfl⟩ := mem_shiftSet.1 hx
    apply hS s hs _ hxS
    have hval : ((s + ((m + k : ℕ) : ZMod r)) - s).val = m + k := by
      rw [add_sub_cancel_left, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have : ((s + ((m + k : ℕ) : ZMod r)) - s).val = 0 := by
        rw [← h, sub_self, ZMod.val_zero]
      omega
    · omega
    · omega
  have hcard := card_shiftSet_ge hne m (r - 2 * m + 1) (by omega)
  have hsum : (shiftSet S m (r - 2 * m + 1)).card + S.card ≤ r := by
    rw [← Finset.card_union_of_disjoint hdisj]
    calc _ ≤ (Finset.univ : Finset (ZMod r)).card := Finset.card_le_univ _
      _ = r := ZMod.card r
  have hSpos : 0 < S.card := Finset.card_pos.2 hne
  rcases le_total r (S.card + (r - 2 * m + 1) - 1) with h | h
  · rw [min_eq_left h] at hcard; omega
  · rw [min_eq_right h] at hcard; omega

/-- The arc `{0, 1, …, m-1}`. -/
noncomputable def arc (r m : ℕ) : Finset (ZMod r) :=
  (Finset.range m).image (fun i : ℕ => (i : ZMod r))

omit [NeZero r] in
theorem arc_card (hr : m ≤ r) : (arc r m).card = m := by
  unfold arc
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  have := congrArg ZMod.val hij
  simp only [ZMod.val_natCast] at this
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

/-- **Lower bound.**  The arc of `m` consecutive vertices is independent. -/
theorem arc_indep (hr : 2 * m ≤ r) : IndepFinset (ContactCycle r m) (arc r m) := by
  intro x hx y hy hadj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
  simp only [Finset.mem_range] at hi hj
  obtain ⟨hne, h1, h2⟩ := hadj
  rcases le_total i j with hij | hij
  · have : ((j : ZMod r) - (i : ZMod r)) = ((j - i : ℕ) : ZMod r) := by
      rw [Nat.cast_sub hij]
    rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at h1
    omega
  · have hc : ((j : ZMod r) - (i : ZMod r)) = -((i - j : ℕ) : ZMod r) := by
      rw [Nat.cast_sub hij]; ring
    have hz : ((i - j : ℕ) : ZMod r) ≠ 0 := by
      intro h0
      apply hne
      have : ((j : ZMod r) - (i : ZMod r)) = 0 := by rw [hc, h0, neg_zero]
      exact (sub_eq_zero.1 this).symm
    have hpos : 0 < i - j := by
      rcases Nat.eq_zero_or_pos (i - j) with h | h
      · exact absurd (by rw [h]; simp) hz
      · exact h
    rw [hc, ZMod.neg_val, if_neg hz, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at h2
    omega

/-- **V90 cyclic independence theorem.**  For `1 ≤ m` and `2m ≤ r`,
`α(ContactCycle r m) = m`. -/
theorem alpha_contactCycle (hm : 1 ≤ m) (hr : 2 * m ≤ r) :
    alpha (ContactCycle r m) = m := by
  apply le_antisymm
  · exact alpha_le fun S hS => indep_card_le hm hr hS
  · calc m = (arc r m).card := (arc_card (by omega)).symm
      _ ≤ _ := card_le_alpha (arc_indep hr)

/-- The same theorem in V90 notation: `α(G(r, m-1)) = m` for `1 ≤ m`, `2m ≤ r`. -/
theorem alpha_G (hm : 1 ≤ m) (hr : 2 * m ≤ r) : alpha (G r (m - 1)) = m := by
  have : m - 1 + 1 = m := by omega
  unfold G; rw [this]; exact alpha_contactCycle hm hr

/-- **Occupancy-to-edge consumer.**  Any `m + 1` vertices of `ContactCycle r m` contain a
useful edge. -/
theorem exists_useful_edge (hm : 1 ≤ m) (hr : 2 * m ≤ r) {O : Finset (ZMod r)}
    (hO : m + 1 ≤ O.card) : ∃ x ∈ O, ∃ y ∈ O, (ContactCycle r m).Adj x y :=
  exists_adj_of_alpha_lt (by rw [alpha_contactCycle hm hr]; omega)

end Alpha

/-! ## The specialisation `G(11,2)` -/

/-- The useful differences of `G(11,2)` are exactly `3, 4, 5, 6, 7, 8`. -/
theorem G_11_2_adj_iff (x y : ZMod 11) :
    (G 11 2).Adj x y ↔ (y - x).val ∈ ({3, 4, 5, 6, 7, 8} : Finset ℕ) := by
  have hlt := ZMod.val_lt (y - x)
  simp only [G, contactCycle_adj_iff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h1, h2⟩; omega
  · intro h
    refine ⟨?_, by omega, by omega⟩
    rintro rfl
    simp at h

/-- **`α(G(11,2)) = 3`** (the general theorem with `m = 3`, `r = 11`). -/
theorem alpha_G_11_2 : alpha (G 11 2) = 3 := alpha_G (m := 3) (by norm_num) (by norm_num)

set_option maxRecDepth 20000 in
/-- **Finite regression check** (independent of the general proof, kernel `decide` on a Boolean
enumeration of all 330 four-subsets of `{0,…,10}`): every 4-subset contains a pair whose cyclic
difference `(y - x) mod 11` lies in `{3,…,8}`. -/
theorem G_11_2_four_subsets_have_edge :
    ((List.range 11).sublistsLen 4).all
      (fun l => l.any fun x => l.any fun y => decide ((y + 11 - x) % 11 ∈ [3, 4, 5, 6, 7, 8])) =
      true := by
  decide

/-- Regression: `{0,1,2}` is an independent 3-set of `G(11,2)` — three occupied blocks do
**not** force a contact. -/
theorem G_11_2_three_indep :
    ∀ x ∈ ({0, 1, 2} : Finset (ZMod 11)), ∀ y ∈ ({0, 1, 2} : Finset (ZMod 11)),
      (y - x).val ∉ ({3, 4, 5, 6, 7, 8} : Finset ℕ) := by
  decide

/-! ## Width ratio -/

/-- For `r = 4m + 1`, `(r - m)/m = 3 + 1/m`. -/
theorem width_ratio {m r : ℕ} (hm : 1 ≤ m) (hr : r = 4 * m + 1) :
    ((r : ℝ) - m) / m = 3 + 1 / m := by
  subst hr
  have : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  push_cast
  field_simp
  ring

/-- The explicit width parameter `m(s) = ⌊1/(s-3)⌋₊ + 1`. -/
noncomputable def widthParam (s : ℝ) : ℕ := ⌊1 / (s - 3)⌋₊ + 1

theorem one_le_widthParam (s : ℝ) : 1 ≤ widthParam s := by
  unfold widthParam; omega

/-- **Constructive width choice.**  For every real `s > 3`, `m = ⌊1/(s-3)⌋₊ + 1 ≥ 1`
satisfies `3 + 1/m < s`. -/
theorem widthParam_spec {s : ℝ} (hs : 3 < s) : 3 + 1 / (widthParam s : ℝ) < s := by
  unfold widthParam
  have hpos : 0 < s - 3 := by linarith
  have hlt : 1 / (s - 3) < (⌊1 / (s - 3)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hm : (0 : ℝ) < (⌊1 / (s - 3)⌋₊ : ℝ) + 1 := by positivity
  push_cast
  have : 1 / ((⌊1 / (s - 3)⌋₊ : ℝ) + 1) < s - 3 := by
    rw [div_lt_iff₀ hm]
    rw [div_lt_iff₀ hpos] at hlt
    linarith
  linarith

theorem exists_width_parameter {s : ℝ} (hs : 3 < s) :
    ∃ m : ℕ, 1 ≤ m ∧ 3 + 1 / (m : ℝ) < s :=
  ⟨widthParam s, one_le_widthParam s, widthParam_spec hs⟩

/-- For `r = 4m+1` with `m = widthParam s`, the graph width `(r - m)/m` is below `s`. -/
theorem width_lt_of_widthParam {s : ℝ} (hs : 3 < s) :
    (((4 * widthParam s + 1 : ℕ) : ℝ) - widthParam s) / widthParam s < s := by
  rw [width_ratio (one_le_widthParam s) rfl]
  exact widthParam_spec hs

/-! ## The general V90 annulus barrier (isolated; OPEN here, unused downstream)

The real-line averaging theorem "edges only at log-distance in `[D₋, D₊]` ⟹
`α ≥ ⌈|V| D₋ / (D₋ + D₊)⌉`" is **not** proved here: it needs a continuous averaging over
shifts.  It is recorded as the explicit statement `AnnulusBarrier287` and is **not used** by any
downstream theorem: the W3 and `E287_11_4` consumers use only `alpha_contactCycle`. -/

/-- **(OPEN geometric provider, unused downstream.)** -/
def AnnulusBarrier287 : Prop :=
  ∀ (Dm Dp : ℝ), 0 < Dm → Dm ≤ Dp → ∀ (V : Finset ℝ) (Γ : SimpleGraph ℝ),
    (∀ x ∈ V, ∀ y ∈ V, Γ.Adj x y → Dm ≤ |x - y| ∧ |x - y| ≤ Dp) →
    ∃ S ⊆ V, (∀ x ∈ S, ∀ y ∈ S, ¬ Γ.Adj x y) ∧
      (V.card : ℝ) * Dm / (Dm + Dp) ≤ S.card

end Erdos287.PostV87V90R
