import Mathlib

/-!
# Anchored V2 — the finite unit-list subset-sum theorem

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The finite group lemma behind the coupled repair batches: for `m ≥ 2`, any list of `m − 1`
units of `ℤ/m` (repetitions allowed) has subsets attaining **every** residue.

Proof architecture (exactly the intended one): start with the attainable set `{0}`; adding a
new unit `c` replaces the attainable set `A` by `A ∪ (A + c)`.  If that does not grow `A` then
`A` is invariant under translation by `c`, and since a unit generates the additive cyclic group,
a nonempty invariant set is everything.  Hence the cardinality grows by at least one at each
step until all `m` residues occur.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV2

/-- The set of subset sums of the family `c` over subsets of the index set `s`. -/
def attain {n : ℕ} {m : ℕ} (c : Fin n → ZMod m) (s : Finset (Fin n)) : Finset (ZMod m) :=
  s.powerset.image (fun I => ∑ i ∈ I, c i)

/-- A nonempty subset of `ZMod m` invariant under translation by a unit is everything. -/
theorem eq_univ_of_add_unit_invariant {m : ℕ} [NeZero m] {A : Finset (ZMod m)}
    (hne : A.Nonempty) {c : ZMod m} (hc : IsUnit c)
    (hinv : ∀ x ∈ A, x + c ∈ A) : A = Finset.univ := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨b, hb⟩ := hc.exists_right_inv
  have hstep : ∀ k : ℕ, x₀ + (k : ZMod m) * c ∈ A := by
    intro k
    induction k with
    | zero => simpa using hx₀
    | succ k ih =>
        have := hinv _ ih
        have hcast : x₀ + ((k + 1 : ℕ) : ZMod m) * c = x₀ + (k : ZMod m) * c + c := by
          push_cast
          ring
        rwa [hcast]
  refine Finset.eq_univ_of_forall ?_
  intro y
  obtain ⟨k, hk⟩ := ZMod.natCast_zmod_surjective (n := m) ((y - x₀) * b)
  have := hstep k
  rwa [hk, show (y - x₀) * b * c = y - x₀ by rw [mul_assoc, mul_comm b c, hb, mul_one],
    add_sub_cancel] at this

/-- One step of the attainable-set recursion strictly increases the cardinality, unless the
attainable set is already everything. -/
theorem card_union_image_add_lt {m : ℕ} [NeZero m] {A : Finset (ZMod m)} (hne : A.Nonempty)
    (hA : A ≠ Finset.univ) {c : ZMod m} (hc : IsUnit c) :
    A.card < (A ∪ A.image (fun x => x + c)).card := by
  classical
  by_contra hcon
  push_neg at hcon
  have hsub : A ⊆ A ∪ A.image (fun x => x + c) := Finset.subset_union_left
  have heq : A = A ∪ A.image (fun x => x + c) := Finset.eq_of_subset_of_card_le hsub hcon
  have hinv : ∀ x ∈ A, x + c ∈ A := by
    intro x hx
    rw [heq]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx)
  exact hA (eq_univ_of_add_unit_invariant hne hc hinv)

theorem attain_empty {n m : ℕ} (c : Fin n → ZMod m) : attain c ∅ = {0} := by
  simp [attain]

theorem attain_nonempty {n m : ℕ} (c : Fin n → ZMod m) (s : Finset (Fin n)) :
    (attain c s).Nonempty := by
  refine ⟨0, ?_⟩
  refine Finset.mem_image.2 ⟨∅, ?_, by simp⟩
  simp

/-- The attainable set grows by one translation step at each new index. -/
theorem attain_insert {n m : ℕ} (c : Fin n → ZMod m) {a : Fin n} {s : Finset (Fin n)}
    (ha : a ∉ s) :
    attain c (insert a s) = attain c s ∪ (attain c s).image (fun x => x + c a) := by
  classical
  unfold attain
  rw [Finset.powerset_insert, Finset.image_union, Finset.image_image, Finset.image_image]
  congr 1
  refine Finset.image_congr ?_
  intro I hI
  have hIa : a ∉ I := fun h => ha (Finset.mem_powerset.1 hI h)
  simp only [Function.comp_apply]
  rw [Finset.sum_insert hIa, add_comm]

/-- The attainable set has at least `min m (|s| + 1)` elements. -/
theorem card_attain_ge {m : ℕ} [NeZero m] {n : ℕ} (c : Fin n → ZMod m) (hc : ∀ i, IsUnit (c i))
    (s : Finset (Fin n)) : min m (s.card + 1) ≤ (attain c s).card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [attain_empty]
      have h1 : (1 : ℕ) ≤ m := Nat.one_le_iff_ne_zero.2 (NeZero.ne m)
      simp [h1]
  | insert a s ha ih =>
      rw [attain_insert c ha]
      by_cases huniv : attain c s = Finset.univ
      · have : attain c s ∪ (attain c s).image (fun x => x + c a) = Finset.univ := by
          rw [huniv]
          exact Finset.univ_subset_iff.1 Finset.subset_union_left
        rw [this, Finset.card_univ, ZMod.card m]
        exact min_le_left _ _
      · have hlt := card_union_image_add_lt (attain_nonempty c s) huniv (hc a)
        have hcard : s.card + 1 = (insert a s).card := (Finset.card_insert_of_notMem ha).symm
        have := ih
        omega

/-- **`exists_subset_sum_eq`.**  `KERNEL-PROVED`.  The unit-list subset-sum theorem: for
`m ≥ 2` and any family of at least `m − 1` units of `ℤ/m` (repetitions allowed), every residue
is a subset sum. -/
theorem exists_subset_sum_eq {m : ℕ} (hm : 2 ≤ m) {n : ℕ} (hn : m - 1 ≤ n)
    (c : Fin n → ZMod m) (hc : ∀ i, IsUnit (c i)) (t : ZMod m) :
    ∃ I : Finset (Fin n), ∑ i ∈ I, c i = t := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  have hcardu : (Finset.univ : Finset (Fin n)).card = n := by simp
  have hge := card_attain_ge c hc (Finset.univ : Finset (Fin n))
  rw [hcardu] at hge
  have hmin : m ≤ min m (n + 1) := by omega
  have hle : (attain c Finset.univ).card ≤ Fintype.card (ZMod m) := Finset.card_le_univ _
  rw [ZMod.card m] at hle
  have hcard : (attain c Finset.univ).card = Fintype.card (ZMod m) := by
    rw [ZMod.card m]
    omega
  have huniv : attain c Finset.univ = Finset.univ := Finset.eq_univ_of_card _ hcard
  have ht : t ∈ attain c (Finset.univ : Finset (Fin n)) := by
    rw [huniv]; exact Finset.mem_univ t
  obtain ⟨I, -, hI⟩ := Finset.mem_image.1 ht
  exact ⟨I, hI⟩

end AnchoredV2
end Erdos287
