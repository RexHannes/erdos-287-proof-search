import RequestProject.Erdos287.AnchoredV4.EntryMobility

/-!
# Anchored V4 — necessary conditions for ENTRY, and the status of ENTRY existence

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

ENTRY existence is the live research owner.  This module proves genuine **necessary** conditions
that any ENTRY must satisfy, which is what a future construction has to meet (or a future
impossibility proof has to contradict):

* `normHeight_le_self` — the normalized prime-power height never exceeds its argument;
* `Entry.Q_lt_mem` — consequently **every omitted position exceeds `Q`**;
* `noAdjacent_card_bound` and `Entry.two_mul_card_le` — a guarded omission set inside `(aM, M)`
  has at most `(M − aM)/2` elements;
* `Entry.odd_mem_mask` — every odd omitted position is inside the declared mask, so the mask must
  itself contain enough high-height positions.

`EntryExists` is the exact open owner.  It is inhabited here **only** in the degenerate
one-point case, which is explicitly *not* an ENTRY for large `M`.
-/

namespace Erdos287
namespace AnchoredV4

/-- The normalized prime-power height of a positive integer never exceeds it. -/
theorem normHeight_le_self {n : ℕ} (hn : 1 ≤ n) : normHeight n ≤ n := by
  rw [normHeight, max_le_iff]
  refine ⟨hn, Finset.sup_le ?_⟩
  intro p hp
  have hn0 : n ≠ 0 := by omega
  have hdvd : p ^ n.factorization p ∣ n := Nat.ordProj_dvd n p
  have hle : p ^ n.factorization p ≤ n := Nat.le_of_dvd (by omega) hdvd
  by_cases hp2 : p = 2
  · subst hp2
    rw [heightAt_two]
    calc 2 ^ (n.factorization 2 - 1) ≤ 2 ^ n.factorization 2 :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ n := hle
  · rw [heightAt_odd hp2]
    exact hle

/-- **Necessary condition.**  Every omitted position of an ENTRY is larger than `Q`. -/
theorem Entry.Q_lt_mem {M aM Q Y : ℕ} (e : Entry M aM Q Y) {z : ℕ} (hz : z ∈ e.Z) : Q < z :=
  lt_of_lt_of_le (e.height_gt hz) (normHeight_le_self (e.Z_pos hz))

/-- A guarded (`no-00`) omission set inside the open interval `(aM, M)` has at most half as many
elements as the interval has positions. -/
theorem noAdjacent_card_bound {aM M : ℕ} {Z : Finset ℕ} (hZ : Z ⊆ Finset.Ioo aM M)
    (hna : NoAdjacent Z) : 2 * Z.card ≤ M - aM := by
  classical
  have hdisj : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' →
      Disjoint ({z, z + 1} : Finset ℕ) ({z', z' + 1} : Finset ℕ) := by
    intro z hz z' hz' hne
    simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    have h1 : z + 1 ∉ Z := hna z hz
    have h2 : z' + 1 ∉ Z := hna z' hz'
    rintro a (rfl | rfl) hcon <;> rcases hcon with h | h
    · exact hne h
    · exact h2 (by rw [← h]; exact hz)
    · exact h1 (by rw [h]; exact hz')
    · exact hne (by omega)
  have hsub : Z.biUnion (fun z => ({z, z + 1} : Finset ℕ)) ⊆ Finset.Icc (aM + 1) M := by
    intro x hx
    simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hx
    obtain ⟨z, hz, hx⟩ := hx
    have := hZ hz
    simp only [Finset.mem_Ioo] at this
    simp only [Finset.mem_Icc]
    rcases hx with rfl | rfl <;> omega
  have hcard : (Z.biUnion (fun z => ({z, z + 1} : Finset ℕ))).card = 2 * Z.card := by
    rw [Finset.card_biUnion hdisj]
    rw [Finset.sum_congr rfl (fun z _ => by simp : ∀ z ∈ Z, ({z, z + 1} : Finset ℕ).card = 2)]
    simp [mul_comm]
  have := Finset.card_le_card hsub
  rw [hcard, Nat.card_Icc] at this
  omega

/-- **Necessary condition.**  An ENTRY omission set is at most half the size of the interval. -/
theorem Entry.two_mul_card_le {M aM Q Y : ℕ} (e : Entry M aM Q Y) : 2 * e.Z.card ≤ M - aM :=
  noAdjacent_card_bound e.Z_subset e.Z_noAdjacent

/-- **Necessary condition.**  Every odd omitted position lies in the declared mask, and the mask
consists of positions of height `> Q`. -/
theorem Entry.odd_mem_mask {M aM Q Y : ℕ} (e : Entry M aM Q Y) {z : ℕ} (hz : z ∈ e.Z)
    (hodd : ¬ Even z) : z ∈ e.mask ∧ Q < normHeight z :=
  ⟨e.Z_odd_mask z hz hodd, e.height_gt hz⟩

/-- **The ENTRY-existence owner.**  This is the live research question; it is `OPEN`. -/
def EntryExists (M aM Q Y : ℕ) : Prop := Nonempty (Entry M aM Q Y)

/-- The degenerate parameters admit an ENTRY.  This is a consistency check of the definition and
**not** evidence for ENTRY existence at large `M`. -/
theorem entryExists_degenerate : EntryExists 1 0 1 1 := ⟨entryDegenerate⟩

/-- Any ENTRY at parameters with a nonempty omission set forces the interval to be long enough;
recorded as the first quantitative constraint on a candidate construction. -/
theorem Entry.interval_length_lower_bound {M aM Q Y : ℕ} (e : Entry M aM Q Y)
    (hne : e.Z.Nonempty) : 2 ≤ M - aM := by
  have h := e.two_mul_card_le
  have : 1 ≤ e.Z.card := Finset.card_pos.2 hne
  omega

end AnchoredV4
end Erdos287
