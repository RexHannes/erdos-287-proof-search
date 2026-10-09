import Mathlib

/-!
# Anchored V3 — column zero-sum packets

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Elementary zero-sum packet extraction for a single column.  For a prime (indeed, any modulus)
`ℓ` and a family of **nonzero** coefficients in `ZMod ℓ` indexed by a finite set `s`:

* among any `ℓ` of the entries the `ℓ + 1` prefix sums collide (pigeonhole), so some nonempty
  block of size `≤ ℓ` has zero sum;
* because all coefficients are nonzero, no packet is a singleton, hence every packet has size
  at least `2`;
* repeated extraction yields pairwise disjoint packets, leaves fewer than `ℓ` entries
  unused, and produces at least `⌊n / ℓ⌋` packets from `n` entries;
* any union of disjoint packets is again column neutral.

## FIREWALL

`manyNeutralPackets_not_exactTarget` records the retraction: packet abundance does **not**
imply that a prescribed integer target is hit.  Nothing in this module may be used to infer
coefficient HIT from the number of packets.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV3
namespace ColumnPackets

/-- The block between two colliding prefix sums has zero sum. -/
theorem zeroSum_block_of_prefix_collision {ℓ : ℕ} {s t : Finset ℕ} (hts : t ⊆ s)
    {f : ℕ → ZMod ℓ} {g : ℕ → ℕ}
    (hgmem : ∀ j, j < ℓ → g j ∈ t)
    (hginj : ∀ j₁ < ℓ, ∀ j₂ < ℓ, g j₁ = g j₂ → j₁ = j₂)
    {P : ℕ → ZMod ℓ} (hP : P = fun k => ∑ j ∈ Finset.range k, f (g j))
    {k₁ k₂ : ℕ} (heq : P k₁ = P k₂) (hlt : k₁ < k₂) (hk₂ : k₂ < ℓ + 1) :
    ∃ E ⊆ s, E.Nonempty ∧ E.card ≤ ℓ ∧ ∑ i ∈ E, f i = 0 := by
  classical
  have hbound : ∀ j ∈ Finset.Ico k₁ k₂, j < ℓ := by
    intro j hj
    simp only [Finset.mem_Ico] at hj
    omega
  refine ⟨(Finset.Ico k₁ k₂).image g, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    exact hts (hgmem j (hbound j hj))
  · refine Finset.Nonempty.image ?_ g
    exact ⟨k₁, by simp only [Finset.mem_Ico]; omega⟩
  · calc ((Finset.Ico k₁ k₂).image g).card ≤ (Finset.Ico k₁ k₂).card := Finset.card_image_le
      _ = k₂ - k₁ := Nat.card_Ico k₁ k₂
      _ ≤ ℓ := by omega
  · rw [Finset.sum_image (fun a ha b hb hab => hginj a (hbound a ha) b (hbound b hb) hab)]
    have hsplit : ∑ j ∈ Finset.Ico k₁ k₂, f (g j)
        = (∑ j ∈ Finset.range k₂, f (g j)) - ∑ j ∈ Finset.range k₁, f (g j) :=
      Finset.sum_Ico_eq_sub _ (le_of_lt hlt)
    rw [hsplit]
    have h1 : P k₁ = ∑ j ∈ Finset.range k₁, f (g j) := by rw [hP]
    have h2 : P k₂ = ∑ j ∈ Finset.range k₂, f (g j) := by rw [hP]
    rw [← h1, ← h2, heq, sub_self]

/-- **Pigeonhole zero-sum block.**  Any `ℓ` entries contain a nonempty sub-family of size at
most `ℓ` whose coefficients sum to zero in `ZMod ℓ`. -/
theorem exists_zeroSum_subset {ℓ : ℕ} (hℓ : 0 < ℓ) (s : Finset ℕ) (f : ℕ → ZMod ℓ)
    (hcard : ℓ ≤ s.card) :
    ∃ E ⊆ s, E.Nonempty ∧ E.card ≤ ℓ ∧ ∑ i ∈ E, f i = 0 := by
  classical
  haveI : NeZero ℓ := ⟨by omega⟩
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq hcard
  -- an enumeration of `t`
  set g : ℕ → ℕ := fun j => if h : j < ℓ then (t.orderIsoOfFin htcard ⟨j, h⟩ : ℕ) else 0 with hg
  have hgmem : ∀ j, j < ℓ → g j ∈ t := by
    intro j hj
    simp only [hg, dif_pos hj]
    exact (t.orderIsoOfFin htcard ⟨j, hj⟩).2
  have hginj : ∀ j₁ < ℓ, ∀ j₂ < ℓ, g j₁ = g j₂ → j₁ = j₂ := by
    intro j₁ h₁ j₂ h₂ heq
    simp only [hg, dif_pos h₁, dif_pos h₂] at heq
    have : t.orderIsoOfFin htcard ⟨j₁, h₁⟩ = t.orderIsoOfFin htcard ⟨j₂, h₂⟩ :=
      Subtype.ext heq
    have := (t.orderIsoOfFin htcard).injective this
    simpa using congrArg Fin.val this
  -- prefix sums
  set P : ℕ → ZMod ℓ := fun k => ∑ j ∈ Finset.range k, f (g j) with hP
  have hcardlt : Fintype.card (ZMod ℓ) < Fintype.card (Fin (ℓ + 1)) := by
    simp [ZMod.card]
  obtain ⟨k₁, k₂, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin (ℓ + 1) => P (k : ℕ)) hcardlt
  -- order the two collision points
  rcases lt_or_gt_of_ne (fun h : (k₁ : ℕ) = (k₂ : ℕ) => hne (Fin.ext h)) with hlt | hlt
  · exact zeroSum_block_of_prefix_collision hts hgmem hginj hP heq hlt k₂.isLt
  · exact zeroSum_block_of_prefix_collision hts hgmem hginj hP heq.symm hlt k₁.isLt

/-- With all coefficients nonzero no packet is a singleton, so every extracted packet has at
least two entries. -/
theorem exists_zeroSum_subset_two_le {ℓ : ℕ} (hℓ : 0 < ℓ) (s : Finset ℕ) (f : ℕ → ZMod ℓ)
    (hnz : ∀ i ∈ s, f i ≠ 0) (hcard : ℓ ≤ s.card) :
    ∃ E ⊆ s, 2 ≤ E.card ∧ E.card ≤ ℓ ∧ ∑ i ∈ E, f i = 0 := by
  classical
  obtain ⟨E, hEs, hne, hle, hsum⟩ := exists_zeroSum_subset hℓ s f hcard
  refine ⟨E, hEs, ?_, hle, hsum⟩
  rcases Nat.lt_or_ge E.card 2 with h | h
  · exfalso
    interval_cases h' : E.card
    · exact absurd (Finset.card_eq_zero.mp h') (Finset.nonempty_iff_ne_empty.mp hne)
    · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h'
      subst hi
      simp only [Finset.sum_singleton] at hsum
      exact hnz i (hEs (Finset.mem_singleton_self i)) hsum
  · exact h

/-- **Repeated extraction.**  From `n` nonzero coefficients one extracts at least `⌊n / ℓ⌋`
pairwise disjoint zero-sum packets, each of size between `2` and `ℓ`. -/
theorem exists_disjoint_packets {ℓ : ℕ} (hℓ : 0 < ℓ) (f : ℕ → ZMod ℓ) :
    ∀ s : Finset ℕ, (∀ i ∈ s, f i ≠ 0) →
      ∃ P : Finset (Finset ℕ),
        (∀ E ∈ P, E ⊆ s ∧ 2 ≤ E.card ∧ E.card ≤ ℓ ∧ ∑ i ∈ E, f i = 0) ∧
        (∀ E ∈ P, ∀ F ∈ P, E ≠ F → Disjoint E F) ∧
        s.card / ℓ ≤ P.card := by
  classical
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro hnz
    rcases Nat.lt_or_ge s.card ℓ with hsmall | hbig
    · exact ⟨∅, by simp, by simp, by simp [Nat.div_eq_of_lt hsmall]⟩
    · obtain ⟨E, hEs, hE2, hEℓ, hEsum⟩ := exists_zeroSum_subset_two_le hℓ s f hnz hbig
      have hEne : E.Nonempty := Finset.card_pos.mp (by omega)
      have hssub : s \ E ⊂ s := by
        refine Finset.ssubset_iff_of_subset (Finset.sdiff_subset) |>.mpr ?_
        obtain ⟨i, hi⟩ := hEne
        exact ⟨i, hEs hi, by simp [hi]⟩
      obtain ⟨P', hP'mem, hP'disj, hP'card⟩ :=
        ih (s \ E) hssub (fun i hi => hnz i (Finset.mem_sdiff.mp hi).1)
      have hEnotin : E ∉ P' := by
        intro hmem
        obtain ⟨i, hi⟩ := hEne
        have := (hP'mem E hmem).1 hi
        exact (Finset.mem_sdiff.mp this).2 hi
      refine ⟨insert E P', ?_, ?_, ?_⟩
      · intro F hF
        rcases Finset.mem_insert.mp hF with rfl | hF'
        · exact ⟨hEs, hE2, hEℓ, hEsum⟩
        · obtain ⟨h1, h2, h3, h4⟩ := hP'mem F hF'
          exact ⟨h1.trans Finset.sdiff_subset, h2, h3, h4⟩
      · intro F hF G hG hne
        have key : ∀ H ∈ P', Disjoint E H := by
          intro H hH
          refine Finset.disjoint_left.mpr ?_
          intro a haE haH
          exact (Finset.mem_sdiff.mp ((hP'mem H hH).1 haH)).2 haE
        rcases Finset.mem_insert.mp hF with rfl | hF'
        · rcases Finset.mem_insert.mp hG with rfl | hG'
          · exact absurd rfl hne
          · exact key G hG'
        · rcases Finset.mem_insert.mp hG with rfl | hG'
          · exact (key F hF').symm
          · exact hP'disj F hF' G hG' hne
      · have hcard : (s \ E).card = s.card - E.card := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hEs]
        have hins : (insert E P').card = P'.card + 1 := Finset.card_insert_of_notMem hEnotin
        have h1 : s.card / ℓ = (s.card - ℓ) / ℓ + 1 := Nat.div_eq_sub_div hℓ hbig
        have h2 : (s.card - ℓ) / ℓ ≤ (s \ E).card / ℓ := by
          apply Nat.div_le_div_right
          omega
        omega

/-- **Any union of disjoint packets preserves column neutrality.** -/
theorem sum_biUnion_eq_zero {ℓ : ℕ} (f : ℕ → ZMod ℓ) (P : Finset (Finset ℕ))
    (hdisj : ∀ E ∈ P, ∀ F ∈ P, E ≠ F → Disjoint E F)
    (hzero : ∀ E ∈ P, ∑ i ∈ E, f i = 0) :
    ∑ i ∈ P.biUnion (fun E => E), f i = 0 := by
  classical
  have hpd : (P : Set (Finset ℕ)).PairwiseDisjoint (fun E => E) := by
    intro E hE F hF hne
    exact hdisj E hE F hF hne
  rw [Finset.sum_biUnion hpd]
  exact Finset.sum_eq_zero (fun E hE => hzero E hE)

/-- **FIREWALL — packet abundance does not imply an exact coefficient hit.**

An explicit finite witness: four unit coefficients modulo `2` admit two disjoint zero-sum
packets, yet no zero pattern at all has integer weight `3`. -/
theorem manyNeutralPackets_not_exactTarget :
    (∃ E F : Finset ℕ, E ⊆ Finset.range 4 ∧ F ⊆ Finset.range 4 ∧ Disjoint E F ∧
        2 ≤ E.card ∧ 2 ≤ F.card ∧ 2 ∣ E.card ∧ 2 ∣ F.card) ∧
      ∀ E ⊆ Finset.range 4, 2 ∣ E.card → E.card / 2 ≠ 3 := by
  classical
  constructor
  · exact ⟨{0, 1}, {2, 3}, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide⟩
  · intro E hE _
    have : E.card ≤ 4 := by
      have := Finset.card_le_card hE
      simpa using this
    omega

end ColumnPackets
end AnchoredV3
end Erdos287
