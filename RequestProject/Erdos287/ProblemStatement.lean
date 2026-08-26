import RequestProject.Erdos287.Counterexample

/-!
# Erdős Problem #287 — the exact problem statement

The published problem asks: for every finite strictly increasing sequence of integers

  `1 < n₁ < n₂ < ⋯ < n_k`  with  `∑ 1/nᵢ = 1`,

is some consecutive gap `n_{i+1} - n_i` at least `3`?

This file introduces the **exact** project-local predicate `Erdos287Counterexample A`
describing a hypothetical counterexample and relates it to the broader historical
compiler type `Gap2CE`:

* `Erdos287Counterexample` requires `2 ≤ A.card`, `1 < a` for every `a ∈ A`,
  `∑_{a ∈ A} 1/a = 1` and all consecutive gaps `≤ 2`;
* `Gap2CE` only requires positivity (`0 < a`), so it admits irrelevant objects such as
  `A = {1}` (`gap2CE_one`, banked below as an explicit witness).  The two types are
  therefore **not** equivalent; the bridge goes one way only
  (`Erdos287Counterexample.toGap2CE`), which is the direction the reduction needs.

We also give the ordered-sequence formulation (`erdos287_seq_of_no_counterexample`),
literally matching the public statement.
-/

open scoped BigOperators

namespace Erdos287

/-- **The exact Erdős #287 counterexample predicate.**  A finite set `A` of integers `> 1`
whose reciprocals sum to `1`, with at least two elements, in which every non-maximal
element is followed within distance `2` (i.e. every consecutive gap of the sorted list of
`A` is at most `2`). -/
structure Erdos287Counterexample (A : Finset ℕ) : Prop where
  /-- At least two denominators. -/
  card_ge : 2 ≤ A.card
  /-- Every denominator exceeds `1`. -/
  one_lt : ∀ a ∈ A, 1 < a
  /-- The reciprocals sum to `1`. -/
  sum_one : ∑ a ∈ A, (1 : ℚ) / a = 1
  /-- Every non-maximal element is followed within distance `2`. -/
  gap_le_two : ∀ a ∈ A, (∃ b ∈ A, a < b) → (a + 1 ∈ A ∨ a + 2 ∈ A)

namespace Erdos287Counterexample

variable {A : Finset ℕ} (h : Erdos287Counterexample A)

include h

/-- The underlying set is nonempty. -/
theorem nonempty : A.Nonempty := Finset.card_pos.1 (by have := h.card_ge; omega)

/-- **Bridge to the historical compiler type.**  Every exact counterexample is in
particular a `Gap2CE`. -/
def toGap2CE : Gap2CE where
  A := A
  hne := h.nonempty
  hpos := fun a ha => lt_trans Nat.zero_lt_one (h.one_lt a ha)
  hsum := h.sum_one
  hgap := by
    intro a ha hne
    refine h.gap_le_two a ha ⟨A.max' h.nonempty, Finset.max'_mem _ _, ?_⟩
    exact lt_of_le_of_ne (Finset.le_max' _ _ ha) hne

@[simp] theorem toGap2CE_A : (h.toGap2CE).A = A := rfl

@[simp] theorem toGap2CE_M : (h.toGap2CE).M = A.max' h.nonempty := rfl

/-- The maximal denominator of an exact counterexample is at least `3`:
two distinct denominators `> 1` force the largest to be `≥ 3`. -/
theorem three_le_max : 3 ≤ A.max' h.nonempty := by
  by_contra hlt
  push_neg at hlt
  have hsub : A ⊆ {2} := by
    intro a ha
    have h1 : 1 < a := h.one_lt a ha
    have h2 : a ≤ A.max' h.nonempty := Finset.le_max' _ _ ha
    have : a = 2 := by omega
    simp [this]
  have := Finset.card_le_card hsub
  have := h.card_ge
  simp at *
  omega

/-- The maximal denominator of an exact counterexample is at least `4`: with `max A ≤ 3`
the whole set is contained in `{2,3}`, whose reciprocal sum is `5/6 < 1`. -/
theorem four_le_max : 4 ≤ A.max' h.nonempty := by
  by_contra hlt
  push_neg at hlt
  have hsub : A ⊆ ({2, 3} : Finset ℕ) := by
    intro a ha
    have h1 : 1 < a := h.one_lt a ha
    have h2 : a ≤ A.max' h.nonempty := Finset.le_max' _ _ ha
    have : a = 2 ∨ a = 3 := by omega
    rcases this with rfl | rfl <;> simp
  have hle : ∑ a ∈ A, (1 : ℚ) / a ≤ ∑ a ∈ ({2, 3} : Finset ℕ), (1 : ℚ) / a :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
  rw [h.sum_one] at hle
  norm_num at hle

end Erdos287Counterexample

/-! ## Non-vacuity guards

The predicate is not accidentally unsatisfiable for trivial reasons: each family of fields
is separately realisable, and it is only their *conjunction* that is at stake. -/

/-- `{2,3,4}` satisfies every field except the reciprocal-sum one (its sum is `13/12`). -/
theorem sanity_gap_fields_satisfiable :
    2 ≤ ({2, 3, 4} : Finset ℕ).card ∧ (∀ a ∈ ({2, 3, 4} : Finset ℕ), 1 < a) ∧
      (∀ a ∈ ({2, 3, 4} : Finset ℕ), (∃ b ∈ ({2, 3, 4} : Finset ℕ), a < b) →
        (a + 1 ∈ ({2, 3, 4} : Finset ℕ) ∨ a + 2 ∈ ({2, 3, 4} : Finset ℕ))) ∧
      ∑ a ∈ ({2, 3, 4} : Finset ℕ), (1 : ℚ) / a = 13 / 12 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  norm_num

/-- `{2,3,6}` satisfies every field except the gap one (`3` and `6` are `3` apart). -/
theorem sanity_sum_field_satisfiable :
    2 ≤ ({2, 3, 6} : Finset ℕ).card ∧ (∀ a ∈ ({2, 3, 6} : Finset ℕ), 1 < a) ∧
      ∑ a ∈ ({2, 3, 6} : Finset ℕ), (1 : ℚ) / a = 1 ∧
      ¬ (∀ a ∈ ({2, 3, 6} : Finset ℕ), (∃ b ∈ ({2, 3, 6} : Finset ℕ), a < b) →
        (a + 1 ∈ ({2, 3, 6} : Finset ℕ) ∨ a + 2 ∈ ({2, 3, 6} : Finset ℕ))) := by
  refine ⟨by decide, by decide, ?_, by decide⟩
  norm_num


/-- The historical type `Gap2CE` is genuinely broader: `A = {1}` inhabits it.  (This is why
the reduction is phrased against `Erdos287Counterexample` and only *maps into* `Gap2CE`.) -/
def gap2CE_one : Gap2CE where
  A := {1}
  hne := ⟨1, by simp⟩
  hpos := by intro a ha; simp at ha; omega
  hsum := by simp
  hgap := by
    intro a ha hne
    simp at ha
    exact absurd (by simp [ha]) hne

/-- ... and it is not an exact counterexample. -/
theorem not_erdos287Counterexample_one : ¬ Erdos287Counterexample {1} := by
  intro h
  have := h.one_lt 1 (by simp)
  omega

/-! ## The ordered-sequence formulation -/

/-- **Public statement, ordered form.**  If no finite set is an `Erdos287Counterexample`,
then every finite strictly increasing sequence `1 < n 0 < n 1 < ⋯ < n (k-1)` whose
reciprocals sum to `1` has a consecutive gap of at least `3`. -/
theorem erdos287_seq_of_no_counterexample
    (hno : ∀ A : Finset ℕ, ¬ Erdos287Counterexample A)
    (k : ℕ) (n : ℕ → ℕ)
    (hmono : ∀ i j, i < j → j < k → n i < n j)
    (hone : ∀ i, i < k → 1 < n i)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / (n i) = 1) :
    ∃ i, i + 1 < k ∧ n i + 3 ≤ n (i + 1) := by
  by_contra hcon
  push_neg at hcon
  -- the image set
  set A : Finset ℕ := (Finset.range k).image n with hA
  have hinj : ∀ i ∈ Finset.range k, ∀ j ∈ Finset.range k, n i = n j → i = j := by
    intro i hi j hj hij
    simp only [Finset.mem_range] at hi hj
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hij (Nat.ne_of_lt (hmono i j h hj))
    · exact h
    · exact absurd hij.symm (Nat.ne_of_lt (hmono j i h hi))
  have hinj' : Set.InjOn n (Finset.range k) := by
    intro i hi j hj hij
    exact hinj i (by simpa using hi) j (by simpa using hj) hij
  have hsumA : ∑ a ∈ A, (1 : ℚ) / a = 1 := by
    rw [hA, Finset.sum_image hinj']; exact hsum
  have hcard : A.card = k := by
    rw [hA, Finset.card_image_of_injOn (fun i hi j hj hij => hinj i hi j hj hij),
      Finset.card_range]
  -- `k ≥ 2`
  have hk2 : 2 ≤ k := by
    by_contra hk
    push_neg at hk
    interval_cases k
    · simp at hsum
    · rw [Finset.sum_range_one] at hsum
      have h1 : 1 < n 0 := hone 0 (by omega)
      have h2 : (1 : ℚ) < (n 0 : ℚ) := by exact_mod_cast h1
      have h3 : (1 : ℚ) / (n 0 : ℚ) < 1 := (div_lt_one (by linarith)).2 h2
      linarith
  refine hno A ⟨by omega, ?_, hsumA, ?_⟩
  · intro a ha
    rw [hA] at ha
    simp only [Finset.mem_image, Finset.mem_range] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact hone i hi
  · intro a ha hb
    rw [hA] at ha
    simp only [Finset.mem_image, Finset.mem_range] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    obtain ⟨b, hbA, hab⟩ := hb
    rw [hA] at hbA
    simp only [Finset.mem_image, Finset.mem_range] at hbA
    obtain ⟨j, hj, rfl⟩ := hbA
    have hij : i < j := by
      rcases lt_trichotomy i j with h | h | h
      · exact h
      · subst h; omega
      · exact absurd (hmono j i h hi) (by omega)
    have hik : i + 1 < k := by omega
    have h1 : n i < n (i + 1) := hmono i (i + 1) (by omega) hik
    have h2 : n (i + 1) < n i + 3 := hcon i hik
    have hmem : n (i + 1) ∈ A := by
      rw [hA]; exact Finset.mem_image.2 ⟨i + 1, Finset.mem_range.2 hik, rfl⟩
    rcases (by omega : n (i + 1) = n i + 1 ∨ n (i + 1) = n i + 2) with h | h
    · exact Or.inl (h ▸ hmem)
    · exact Or.inr (h ▸ hmem)

end Erdos287
