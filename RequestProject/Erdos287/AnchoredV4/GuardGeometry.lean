import RequestProject.Erdos287.AnchoredV4.DoubledLattice

/-!
# Anchored V4 — guard geometry (the finite `no-00` combinatorics)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

A *word* on an interval `I` of denominators is described by the finite set `Z ⊆ I` of **omitted**
(zero) positions; the *selected* positions are `I \ Z` and the value of the word is the reciprocal
sum `wordSum I Z = ∑ n ∈ I \ Z, 1/n`.

The `no-00` guard is `NoAdjacent Z : ∀ i ∈ Z, i + 1 ∉ Z`.  This module proves, with no analytic
input whatsoever:

* all-even omission sets always satisfy the guard (`noAdjacent_of_all_even`);
* the guard is inherited by subsets, in particular restoring an omitted position to selected can
  never create an adjacent pair (`NoAdjacent.subset`, `NoAdjacent.erase`);
* inserting a new even center whose two (odd) neighbours are outside the declared odd-zero mask
  preserves the guard (`noAdjacent_insert_even_of_mask`);
* adding a whole fresh even reservoir preserves the guard (`noAdjacent_union_even_of_mask`);
* exact bookkeeping of the word value under omission and restoration (`wordSum_insert`,
  `wordSum_erase`), and additivity of reciprocal sums over disjoint sets.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV4

/-- The reciprocal sum of a finite set of denominators. -/
def recipSum (E : Finset ℕ) : ℚ := ∑ n ∈ E, (1 : ℚ) / n

@[simp] lemma recipSum_empty : recipSum ∅ = 0 := by simp [recipSum]

lemma recipSum_insert {n : ℕ} {E : Finset ℕ} (h : n ∉ E) :
    recipSum (insert n E) = 1 / n + recipSum E := by
  simp [recipSum, Finset.sum_insert h]

lemma recipSum_union_of_disjoint {E F : Finset ℕ} (h : Disjoint E F) :
    recipSum (E ∪ F) = recipSum E + recipSum F := by
  simp [recipSum, Finset.sum_union h]

lemma recipSum_nonneg (E : Finset ℕ) : 0 ≤ recipSum E :=
  Finset.sum_nonneg fun n _ => by positivity

/-- The value of the word on `I` with omitted positions `Z`. -/
def wordSum (I Z : Finset ℕ) : ℚ := recipSum (I \ Z)

/-- Omitting one further selected position decreases the word value by exactly its reciprocal. -/
lemma wordSum_insert {I Z : Finset ℕ} {z : ℕ} (hz : z ∈ I) (hzZ : z ∉ Z) :
    wordSum I (insert z Z) = wordSum I Z - 1 / z := by
  classical
  have hsplit : I \ Z = insert z (I \ insert z Z) := by
    ext x
    by_cases hx : x = z <;> simp [hx, hz, hzZ, Finset.mem_sdiff]
  have hnot : z ∉ I \ insert z Z := by simp
  have := recipSum_insert (n := z) (E := I \ insert z Z) hnot
  unfold wordSum
  rw [hsplit, this]
  ring

/-- Restoring an omitted position to selected increases the word value by exactly its
reciprocal. -/
lemma wordSum_erase {I Z : Finset ℕ} {z : ℕ} (hz : z ∈ I) (hzZ : z ∈ Z) :
    wordSum I (Z.erase z) = wordSum I Z + 1 / z := by
  classical
  have h1 : Z = insert z (Z.erase z) := (Finset.insert_erase hzZ).symm
  have h2 : z ∉ Z.erase z := Finset.notMem_erase z Z
  have := wordSum_insert (I := I) (Z := Z.erase z) hz h2
  rw [← h1] at this
  linarith

/-- Omitting a whole fresh block of selected positions decreases the word value by exactly the
reciprocal sum of the block. -/
lemma wordSum_union {I Z E : Finset ℕ} (hE : E ⊆ I) (hdisj : Disjoint E Z) :
    wordSum I (Z ∪ E) = wordSum I Z - recipSum E := by
  classical
  have hsub : E ⊆ I \ Z := by
    intro x hx
    exact Finset.mem_sdiff.2 ⟨hE hx, fun hxZ => (Finset.disjoint_left.1 hdisj hx) hxZ⟩
  have hsplit : I \ (Z ∪ E) = (I \ Z) \ E := by
    ext x; simp [Finset.mem_sdiff]; tauto
  unfold wordSum recipSum
  rw [hsplit, Finset.sum_sdiff_eq_sub hsub]

/-! ## The `no-00` guard -/

/-- The guard: no two omitted positions are adjacent. -/
def NoAdjacent (Z : Finset ℕ) : Prop := ∀ i ∈ Z, i + 1 ∉ Z

@[simp] lemma noAdjacent_empty : NoAdjacent ∅ := by simp [NoAdjacent]

/-- **Two distinct even positions are never adjacent**, so an all-even omission set is always
guarded. -/
theorem noAdjacent_of_all_even {Z : Finset ℕ} (h : ∀ z ∈ Z, Even z) : NoAdjacent Z := by
  intro i hi hi1
  have h1 := h i hi
  have h2 := h (i + 1) hi1
  rw [Nat.even_add_one] at h2
  exact h2 h1

/-- The guard is inherited by subsets: restoring omitted positions to selected can never create a
new adjacent pair. -/
theorem NoAdjacent.subset {Z Z' : Finset ℕ} (hsub : Z' ⊆ Z) (h : NoAdjacent Z) :
    NoAdjacent Z' := fun i hi hi1 => h i (hsub hi) (hsub hi1)

theorem NoAdjacent.erase {Z : Finset ℕ} (z : ℕ) (h : NoAdjacent Z) : NoAdjacent (Z.erase z) :=
  h.subset (Finset.erase_subset z Z)

/-- Inserting a center whose two neighbours are not omitted preserves the guard. -/
theorem noAdjacent_insert {Z : Finset ℕ} {c : ℕ} (h : NoAdjacent Z) (hup : c + 1 ∉ Z)
    (hdown : ∀ i ∈ Z, i + 1 ≠ c) : NoAdjacent (insert c Z) := by
  intro i hi hi1
  rcases Finset.mem_insert.1 hi with rfl | hiZ
  · rcases Finset.mem_insert.1 hi1 with h1 | h1
    · omega
    · exact hup h1
  · rcases Finset.mem_insert.1 hi1 with h1 | h1
    · exact hdown i hiZ h1
    · exact h i hiZ h1

/-- **Safe even center.**  If every odd omitted position of `Z` lies in the declared odd-zero mask
`H`, the new center `c` is even, and both neighbours of `c` are outside `H`, then omitting `c`
preserves the guard. -/
theorem noAdjacent_insert_even_of_mask {Z H : Finset ℕ} {c : ℕ} (h : NoAdjacent Z)
    (hmask : ∀ z ∈ Z, ¬ Even z → z ∈ H) (hc : Even c)
    (hnb : ∀ j, (j = c + 1 ∨ j + 1 = c) → j ∉ H) : NoAdjacent (insert c Z) := by
  refine noAdjacent_insert h (fun hmem => ?_) (fun i hi hic => ?_)
  · have hodd : ¬ Even (c + 1) := by simp [Nat.even_add_one, hc]
    exact hnb (c + 1) (Or.inl rfl) (hmask _ hmem hodd)
  · have hodd : ¬ Even i := by
      intro hi2
      have : Even (i + 1) := hic ▸ hc
      rw [Nat.even_add_one] at this
      exact this hi2
    exact hnb i (Or.inr hic) (hmask i hi hodd)

/-- **Fresh even reservoir.**  Adding a whole set of fresh even centers, all of whose neighbours
avoid the odd-zero mask, preserves the guard. -/
theorem noAdjacent_union_even_of_mask {Z H E : Finset ℕ} (h : NoAdjacent Z)
    (hmask : ∀ z ∈ Z, ¬ Even z → z ∈ H) (hE : ∀ c ∈ E, Even c)
    (hnb : ∀ c ∈ E, ∀ j, (j = c + 1 ∨ j + 1 = c) → j ∉ H) : NoAdjacent (Z ∪ E) := by
  intro i hi hi1
  rcases Finset.mem_union.1 hi with hiZ | hiE <;> rcases Finset.mem_union.1 hi1 with h1Z | h1E
  · exact h i hiZ h1Z
  · -- `i` omitted, `i+1` an even reservoir center: then `i` is odd, hence in `H`
    have hodd : ¬ Even i := by
      have := hE _ h1E
      rw [Nat.even_add_one] at this
      exact this
    exact hnb (i + 1) h1E i (Or.inr rfl) (hmask i hiZ hodd)
  · -- `i` an even reservoir center, `i+1` omitted: then `i+1` is odd, hence in `H`
    have hodd : ¬ Even (i + 1) := by simp [Nat.even_add_one, hE i hiE]
    exact hnb i hiE (i + 1) (Or.inl rfl) (hmask _ h1Z hodd)
  · have h1 := hE i hiE
    have h2 := hE (i + 1) h1E
    rw [Nat.even_add_one] at h2
    exact h2 h1

/-- Multiple descent steps: a union of guarded sets each satisfying the mask discipline stays
guarded. -/
theorem noAdjacent_union_even_of_mask' {Z H E F : Finset ℕ} (h : NoAdjacent Z)
    (hmask : ∀ z ∈ Z, ¬ Even z → z ∈ H) (hE : ∀ c ∈ E ∪ F, Even c)
    (hnb : ∀ c ∈ E ∪ F, ∀ j, (j = c + 1 ∨ j + 1 = c) → j ∉ H) : NoAdjacent (Z ∪ E ∪ F) := by
  have : Z ∪ E ∪ F = Z ∪ (E ∪ F) := by ext x; simp
  rw [this]
  exact noAdjacent_union_even_of_mask h hmask hE hnb

/-- Every omitted position of a guarded all-even set stays even after a further even insertion:
the mask discipline is stable. -/
theorem mask_stable_insert {Z H : Finset ℕ} {c : ℕ} (hmask : ∀ z ∈ Z, ¬ Even z → z ∈ H)
    (hc : Even c) : ∀ z ∈ insert c Z, ¬ Even z → z ∈ H := by
  intro z hz hodd
  rcases Finset.mem_insert.1 hz with rfl | hzZ
  · exact absurd hc hodd
  · exact hmask z hzZ hodd

end AnchoredV4
end Erdos287
