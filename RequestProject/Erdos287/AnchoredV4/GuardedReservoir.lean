import RequestProject.Erdos287.AnchoredV4.PrimePowerDescent

/-!
# Anchored V4 — the guarded reservoir (finite core)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

A `GuardedReservoir` is a finite set of *eligible even positions* of the interval which are fresh
(not already omitted) and whose neighbours all have low normalized height, so that omitting **any**
subset of them preserves the `no-00` guard and the mask discipline
(`GuardedReservoir.noAdjacent_absorb`), and changes the word value by exactly the reciprocal sum
of the chosen subset (`GuardedReservoir.wordSum_absorb`).

The module also bans the standard fallacy: `positive_mass_not_exact_coverage` is an explicit finite
witness of a guarded reservoir whose mass exceeds a target `Δ > 0` and which nevertheless has
**no** subset with reciprocal sum exactly `Δ`.  Positive reservoir mass is not exact subset-sum
coverage.
-/

namespace Erdos287
namespace AnchoredV4

/-- A finite guarded reservoir of eligible even positions, relative to the current omission set
`Zcur` and the height threshold `Q` of the odd-zero mask. -/
structure GuardedReservoir (aM M Q : ℕ) (Zcur : Finset ℕ) where
  /-- the eligible positions -/
  positions : Finset ℕ
  /-- eligible positions lie in the interior of the interval -/
  positions_subset : positions ⊆ Finset.Ioo aM M
  /-- eligible positions are currently selected (fresh) -/
  positions_fresh : Disjoint positions Zcur
  /-- eligible positions are even -/
  positions_even : ∀ c ∈ positions, Even c
  /-- both neighbours of an eligible position have low normalized height -/
  positions_nb_low : ∀ c ∈ positions, ∀ j, (j = c + 1 ∨ j + 1 = c) → normHeight j ≤ Q

namespace GuardedReservoir

variable {aM M Q : ℕ} {Zcur : Finset ℕ}

/-- The total reservoir mass. -/
def mass (R : GuardedReservoir aM M Q Zcur) : ℚ := recipSum R.positions

lemma mass_nonneg (R : GuardedReservoir aM M Q Zcur) : 0 ≤ R.mass := recipSum_nonneg _

/-- Omitting any subset of the reservoir preserves the `no-00` guard. -/
theorem noAdjacent_absorb (R : GuardedReservoir aM M Q Zcur) {mask : Finset ℕ}
    (hmask_high : ∀ n ∈ mask, Q < normHeight n) (hZ : NoAdjacent Zcur)
    (hZmask : ∀ z ∈ Zcur, ¬ Even z → z ∈ mask) {E : Finset ℕ} (hE : E ⊆ R.positions) :
    NoAdjacent (Zcur ∪ E) :=
  noAdjacent_union_even_of_mask hZ hZmask (fun c hc => R.positions_even c (hE hc))
    (fun c hc j hj hmem =>
      absurd (hmask_high j hmem) (not_lt.2 (R.positions_nb_low c (hE hc) j hj)))

/-- Omitting a subset of the reservoir changes the word value by exactly its reciprocal sum. -/
theorem wordSum_absorb (R : GuardedReservoir aM M Q Zcur) {E : Finset ℕ} (hE : E ⊆ R.positions) :
    wordSum (Finset.Icc aM M) (Zcur ∪ E) = wordSum (Finset.Icc aM M) Zcur - recipSum E :=
  wordSum_union (hE.trans (R.positions_subset.trans Finset.Ioo_subset_Icc_self))
    (Finset.disjoint_of_subset_left hE R.positions_fresh)

/-- The mask discipline survives absorption (all new omissions are even). -/
theorem mask_absorb (R : GuardedReservoir aM M Q Zcur) {mask : Finset ℕ}
    (hZmask : ∀ z ∈ Zcur, ¬ Even z → z ∈ mask) {E : Finset ℕ} (hE : E ⊆ R.positions) :
    ∀ z ∈ Zcur ∪ E, ¬ Even z → z ∈ mask := by
  intro z hz hodd
  rcases Finset.mem_union.1 hz with h | h
  · exact hZmask z h hodd
  · exact absurd (R.positions_even z (hE h)) hodd

/-- Exact absorption of a target by a reservoir. -/
def AbsorbsExactly (R : GuardedReservoir aM M Q Zcur) (Δ : ℚ) : Prop :=
  ∃ E ⊆ R.positions, recipSum E = Δ

end GuardedReservoir

/-! ## Firewall: positive mass is not exact coverage -/

private lemma normHeight_le_of_le {j Q : ℕ} (hj1 : 1 ≤ j) (hjQ : j ≤ Q) : normHeight j ≤ Q := by
  have hQ : 1 ≤ Q := le_trans hj1 hjQ
  exact (normalizedHeight_le_iff_dvd_two_lcm (by omega) hQ).1
    (Dvd.dvd.mul_left (dvd_L hj1 hjQ) 2)

/-- A one-element guarded reservoir `{4}` inside `[0, 10]` with mask threshold `100`. -/
def singletonReservoir : GuardedReservoir 0 10 100 (∅ : Finset ℕ) where
  positions := {4}
  positions_subset := by decide
  positions_fresh := by simp
  positions_even := by decide
  positions_nb_low := by
    intro c hc j hj
    simp only [Finset.mem_singleton] at hc
    subst hc
    rcases hj with rfl | hj
    · exact normHeight_le_of_le (by norm_num) (by norm_num)
    · have : j = 3 := by omega
      subst this
      exact normHeight_le_of_le (by norm_num) (by norm_num)

/-- **Firewall.**  Positive reservoir mass — even mass strictly larger than the target — does not
imply exact subset-sum coverage of the target. -/
theorem positive_mass_not_exact_coverage :
    0 < (1 : ℚ) / 8 ∧ (1 : ℚ) / 8 < singletonReservoir.mass ∧
      ¬ singletonReservoir.AbsorbsExactly (1 / 8) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · simp [GuardedReservoir.mass, singletonReservoir, recipSum]
    norm_num
  · rintro ⟨E, hE, hsum⟩
    have : E = ∅ ∨ E = {4} := Finset.subset_singleton_iff.1 hE
    rcases this with rfl | rfl <;> simp [recipSum] at hsum

end AnchoredV4
end Erdos287
