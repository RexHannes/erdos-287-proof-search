import RequestProject.Erdos287.ClosureInputs

/-!
# Erdős #287 — the ordered-sequence dictionary (append-only bridge layer)

The project already contains

* the exact set-form predicate `Erdos287Counterexample`,
* the set-form statement `Erdos287Statement := ∀ A, ¬ Erdos287Counterexample A`,
* the *forward* bridge `erdos287_seq_of_no_counterexample` from the set form to the
  ordered-sequence form of the published problem.

What was still missing is the **converse purely logical bridge**: that the
ordered-sequence formulation is not *weaker* than the set formulation.  This file supplies
it, so that the two public formulations are proved equivalent and no reading of the
problem is silently weakened:

* `Erdos287SeqStatement` — the published ordered form, verbatim;
* `erdos287SeqStatement_of_statement` — set form ⇒ ordered form (repackaging of the
  existing theorem);
* `erdos287Statement_of_seqStatement` — ordered form ⇒ set form (**new**);
* `erdos287Statement_iff_seqStatement` — the equivalence (**new**);
* `sum_recip_rat_iff_real` — the reciprocal-sum condition may be read in `ℚ` or in `ℝ`
  without change (**new**);
* `gap_le_two_iff_orderEmb_gap` — the "adjacent gap ≤ 2" field of the set predicate is
  exactly the adjacent-gap condition on the increasing enumeration of `A` (**new**).

Nothing here is analytic, and nothing here proves or assumes any instance of Erdős #287:
these are dictionary lemmas between formulations of the *same* open problem.
-/

open scoped BigOperators

namespace Erdos287

/-- **The published statement of Erdős #287, ordered form.**  For every finite strictly
increasing sequence `1 < n 0 < n 1 < ⋯ < n (k-1)` of integers whose reciprocals sum to `1`,
some adjacent gap is at least `3`. -/
def Erdos287SeqStatement : Prop :=
  ∀ (k : ℕ) (n : ℕ → ℕ),
    (∀ i j, i < j → j < k → n i < n j) →
    (∀ i, i < k → 1 < n i) →
    (∑ i ∈ Finset.range k, (1 : ℚ) / (n i) = 1) →
    ∃ i, i + 1 < k ∧ n i + 3 ≤ n (i + 1)

/-- The reciprocal-sum side condition is insensitive to whether it is read in `ℚ` or `ℝ`. -/
theorem sum_recip_rat_iff_real (A : Finset ℕ) :
    (∑ a ∈ A, (1 : ℚ) / a = 1) ↔ (∑ a ∈ A, (1 : ℝ) / a = 1) := by
  constructor
  · intro h
    have : ((∑ a ∈ A, (1 : ℚ) / a : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by rw [h]
    push_cast at this
    simpa using this
  · intro h
    have : ((∑ a ∈ A, (1 : ℚ) / a : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by push_cast; simpa using h
    exact_mod_cast this

/-! ### The increasing enumeration of a finite set -/

section Enumeration

variable {A : Finset ℕ}

/-- The increasing enumeration of `A`, extended by `0` outside its range. -/
noncomputable def enum (A : Finset ℕ) (i : ℕ) : ℕ :=
  if h : i < A.card then A.orderEmbOfFin rfl ⟨i, h⟩ else 0

theorem enum_mem {i : ℕ} (h : i < A.card) : enum A i ∈ A := by
  simp only [enum, dif_pos h]
  exact A.orderEmbOfFin_mem rfl _

theorem enum_lt_enum {i j : ℕ} (hij : i < j) (hj : j < A.card) : enum A i < enum A j := by
  have hi : i < A.card := lt_trans hij hj
  simp only [enum, dif_pos hi, dif_pos hj]
  exact (A.orderEmbOfFin rfl).strictMono (by exact hij)

/-- Every element of `A` is an enumeration value. -/
theorem exists_enum_eq {a : ℕ} (ha : a ∈ A) : ∃ i, i < A.card ∧ enum A i = a := by
  have hr : a ∈ Set.range (A.orderEmbOfFin (rfl : A.card = A.card)) := by
    rw [A.range_orderEmbOfFin rfl]; exact ha
  obtain ⟨j, hj⟩ := hr
  exact ⟨j.1, j.2, by simp only [enum, dif_pos j.2]; simpa using hj⟩

/-- The enumeration lists the elements of `A` in order: nothing of `A` lies strictly between
two consecutive enumeration values. -/
theorem enum_succ_le {i : ℕ} (hi : i + 1 < A.card) {a : ℕ} (ha : a ∈ A) (hlt : enum A i < a) :
    enum A (i + 1) ≤ a := by
  obtain ⟨j, hj, rfl⟩ := exists_enum_eq ha
  have hicard : i < A.card := by omega
  have hij : i < j := by
    rcases lt_trichotomy i j with h | h | h
    · exact h
    · subst h; exact absurd hlt (lt_irrefl _)
    · exact absurd (enum_lt_enum h hicard) (by omega)
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hij) with h | h
  · exact le_of_eq (congrArg (enum A) h)
  · exact le_of_lt (enum_lt_enum h hj)

/-- The reciprocal sum over `A` equals the reciprocal sum of the enumeration. -/
theorem sum_enum_recip (A : Finset ℕ) :
    ∑ i ∈ Finset.range A.card, (1 : ℚ) / (enum A i) = ∑ a ∈ A, (1 : ℚ) / a := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => (1 : ℚ) / (enum A i)) A.card]
  conv_rhs => rw [← Finset.map_orderEmbOfFin_univ A (rfl : A.card = A.card)]
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp only [enum, dif_pos i.2, RelEmbedding.coe_toEmbedding]

end Enumeration

/-- **Set form ⇒ ordered form.** -/
theorem erdos287SeqStatement_of_statement (h : Erdos287Statement) : Erdos287SeqStatement :=
  fun k n hmono hone hsum => erdos287_seq_of_no_counterexample h k n hmono hone hsum

/-- **Ordered form ⇒ set form.**  A set counterexample is enumerated increasingly; the
enumeration is a strictly increasing sequence of integers `> 1` with reciprocal sum `1`, and
its adjacent gaps are all `≤ 2` because no element of `A` lies strictly between consecutive
enumeration values. -/
theorem erdos287Statement_of_seqStatement (h : Erdos287SeqStatement) : Erdos287Statement := by
  intro A hA
  have hmono : ∀ i j, i < j → j < A.card → enum A i < enum A j := fun _ _ hij hj =>
    enum_lt_enum hij hj
  have hone : ∀ i, i < A.card → 1 < enum A i := fun i hi => hA.one_lt _ (enum_mem hi)
  have hsum : ∑ i ∈ Finset.range A.card, (1 : ℚ) / (enum A i) = 1 := by
    rw [sum_enum_recip]; exact hA.sum_one
  obtain ⟨i, hi, hgap⟩ := h A.card (enum A) hmono hone hsum
  have hiA : enum A i ∈ A := enum_mem (by omega)
  have hnext : enum A (i + 1) ∈ A := enum_mem hi
  have hlt : enum A i < enum A (i + 1) := hmono i (i + 1) (by omega) hi
  rcases hA.gap_le_two _ hiA ⟨enum A (i + 1), hnext, hlt⟩ with hmem | hmem
  · have := enum_succ_le hi hmem (by omega)
    omega
  · have := enum_succ_le hi hmem (by omega)
    omega

/-- **The two public formulations of Erdős #287 are equivalent.**  Neither reading is weaker
than the other. -/
theorem erdos287Statement_iff_seqStatement : Erdos287Statement ↔ Erdos287SeqStatement :=
  ⟨erdos287SeqStatement_of_statement, erdos287Statement_of_seqStatement⟩

/-- **Adjacent-gap dictionary.**  For a set of positive integers, the "every non-maximal
element is followed within distance `2`" field is exactly the condition that consecutive
values of the increasing enumeration differ by at most `2`. -/
theorem gap_le_two_iff_orderEmb_gap (A : Finset ℕ) :
    (∀ a ∈ A, (∃ b ∈ A, a < b) → (a + 1 ∈ A ∨ a + 2 ∈ A)) ↔
      (∀ i, i + 1 < A.card → enum A (i + 1) ≤ enum A i + 2) := by
  constructor
  · intro hgap i hi
    have hiA : enum A i ∈ A := enum_mem (by omega)
    have hnext : enum A (i + 1) ∈ A := enum_mem hi
    have hlt : enum A i < enum A (i + 1) := enum_lt_enum (Nat.lt_succ_self i) hi
    rcases hgap _ hiA ⟨enum A (i + 1), hnext, hlt⟩ with hmem | hmem
    · have := enum_succ_le hi hmem (by omega); omega
    · have := enum_succ_le hi hmem (by omega); omega
  · intro hstep a ha hb
    obtain ⟨i, hi, rfl⟩ := exists_enum_eq ha
    obtain ⟨b, hbA, hab⟩ := hb
    obtain ⟨j, hj, rfl⟩ := exists_enum_eq hbA
    have hij : i < j := by
      by_contra hc
      push_neg at hc
      rcases eq_or_lt_of_le hc with rfl | hlt
      · exact lt_irrefl _ hab
      · exact absurd (enum_lt_enum hlt hi) (by omega)
    have hi1 : i + 1 < A.card := by omega
    have h1 : enum A i < enum A (i + 1) := enum_lt_enum (Nat.lt_succ_self i) hi1
    have h2 : enum A (i + 1) ≤ enum A i + 2 := hstep i hi1
    have hmem : enum A (i + 1) ∈ A := enum_mem hi1
    rcases (by omega : enum A (i + 1) = enum A i + 1 ∨ enum A (i + 1) = enum A i + 2) with
      hEq | hEq
    · exact Or.inl (hEq ▸ hmem)
    · exact Or.inr (hEq ▸ hmem)

end Erdos287
