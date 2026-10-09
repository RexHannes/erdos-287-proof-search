import RequestProject.Erdos287.Anchored.CycleRank

/-!
# Anchored V2 — exact feedback-edge reduction

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

This file is append-only new material; nothing of Route S, Route D or Anchored V1 is modified.

Let `I` be a finite anchored contact instance (`Erdos287.Anchored.ContactCSP`) and let
`F ⊆ I.Edges` be a supplied set of *feedback edges* (the complement of a supplied spanning
forest `T`).  Assume every feedback edge carries the anchored **contact (OR) relation**
`rel u w a b = a || b`.

For each subset `S ⊆ F` we pin, on every feedback edge `e ∈ F`, the endpoint selected by `S`
(the first endpoint when `e ∉ S`, the second when `e ∈ S`) to be *selected*, and then delete
the feedback edge.  The resulting instance is `branch I F S`.

The main theorem `sat_iff_exists_branch` is the exact reduction

`I.Sat ↔ ∃ S ⊆ F, (branch I F S).Sat`,

which is **not** a disjoint counting identity: branch solution sets may overlap.  The number of
branches is `2 ^ |F|` (`branch_count`), and with a supplied spanning forest of `c` components
`|F| = |E| - |V| + c = β` (`feedbackSet_card`), giving the `2 ^ β` bound.  No claim is made
that `β` is uniformly bounded.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV2

open Erdos287.Anchored
open Erdos287.Anchored.ContactCSP

/-- The edges of `F` carry the anchored contact (OR) relation. -/
def IsORContact (I : ContactCSP) (F : Finset (ℕ × ℕ)) : Prop :=
  ∀ e ∈ F, ∀ a b : Bool, I.rel e.1 e.2 a b = (a || b)

/-- The endpoint of `e` chosen by the Boolean `c` (`false` = first, `true` = second). -/
def chosenEnd (e : ℕ × ℕ) (c : Bool) : ℕ := if c then e.2 else e.1

theorem chosenEnd_mem (e : ℕ × ℕ) (c : Bool) : chosenEnd e c = e.1 ∨ chosenEnd e c = e.2 := by
  cases c <;> simp [chosenEnd]

/-- The positions pinned *selected* by the choice `S ⊆ F` on the feedback edges `F`. -/
def pinnedBy (F S : Finset (ℕ × ℕ)) (v : ℕ) : Bool :=
  decide (∃ e ∈ F, chosenEnd e (decide (e ∈ S)) = v)

theorem pinnedBy_of_mem {F S : Finset (ℕ × ℕ)} {e : ℕ × ℕ} (he : e ∈ F) :
    pinnedBy F S (chosenEnd e (decide (e ∈ S))) = true := by
  simp only [pinnedBy, decide_eq_true_eq]
  exact ⟨e, he, rfl⟩

/-- The anchored branch instance: pin the chosen endpoints of all feedback edges to
*selected*, then delete the feedback edges. -/
def branch (I : ContactCSP) (F S : Finset (ℕ × ℕ)) : ContactCSP :=
  { V := I.V
    dom := fun v b => I.dom v b && (!pinnedBy F S v || b)
    Edges := I.Edges \ F
    rel := I.rel }

@[simp] theorem branch_V (I : ContactCSP) (F S : Finset (ℕ × ℕ)) : (branch I F S).V = I.V := rfl

@[simp] theorem branch_Edges (I : ContactCSP) (F S : Finset (ℕ × ℕ)) :
    (branch I F S).Edges = I.Edges \ F := rfl

@[simp] theorem branch_rel (I : ContactCSP) (F S : Finset (ℕ × ℕ)) :
    (branch I F S).rel = I.rel := rfl

theorem branch_wellFormed (I : ContactCSP) (F S : Finset (ℕ × ℕ)) (hwf : I.WellFormed) :
    (branch I F S).WellFormed := by
  intro e he
  exact hwf e (Finset.mem_sdiff.1 he).1

/-- **`sat_iff_exists_branch`.**  `KERNEL-PROVED`.  Exact feedback-edge reduction: a contact
instance whose feedback edges carry the OR relation is satisfiable exactly when *some* choice
of pinned endpoints on the feedback edges leaves a satisfiable instance with those edges
deleted. -/
theorem sat_iff_exists_branch (I : ContactCSP) (F : Finset (ℕ × ℕ)) (hwf : I.WellFormed)
    (hF : F ⊆ I.Edges) (hOR : IsORContact I F) :
    I.Sat ↔ ∃ S ∈ F.powerset, (branch I F S).Sat := by
  classical
  constructor
  · rintro ⟨f, hdom, hrel⟩
    refine ⟨F.filter (fun e => f e.1 = false), Finset.mem_powerset.2 (Finset.filter_subset _ _),
      f, ?_, ?_⟩
    · intro v hv
      have hkey : ∀ e ∈ F, f (chosenEnd e (decide (e ∈ F.filter (fun e => f e.1 = false))))
          = true := by
        intro e he
        by_cases h1 : f e.1 = false
        · have hmem : e ∈ F.filter (fun e => f e.1 = false) := Finset.mem_filter.2 ⟨he, h1⟩
          have hor : I.rel e.1 e.2 (f e.1) (f e.2) = true := hrel e (hF he)
          rw [hOR e he] at hor
          rw [h1] at hor
          simpa [chosenEnd, hmem] using hor
        · have hmem : e ∉ F.filter (fun e => f e.1 = false) := by
            simp only [Finset.mem_filter, not_and]
            exact fun _ => h1
          have h1' : f e.1 = true := by
            cases hc : f e.1 with
            | false => exact absurd hc h1
            | true => rfl
          simpa [chosenEnd, hmem] using h1'
      simp only [branch, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
      refine ⟨hdom v hv, ?_⟩
      by_cases hp : pinnedBy F (F.filter (fun e => f e.1 = false)) v = true
      · right
        simp only [pinnedBy, decide_eq_true_eq] at hp
        obtain ⟨e, he, hev⟩ := hp
        rw [← hev]
        exact hkey e he
      · left
        simpa using hp
    · intro e he
      exact hrel e (Finset.mem_sdiff.1 he).1
  · rintro ⟨S, -, f, hdom, hrel⟩
    refine ⟨f, ?_, ?_⟩
    · intro v hv
      have := hdom v hv
      simp only [branch, Bool.and_eq_true] at this
      exact this.1
    · intro e he
      by_cases hFe : e ∈ F
      · set v := chosenEnd e (decide (e ∈ S)) with hv
        have hvV : v ∈ I.V := by
          rcases chosenEnd_mem e (decide (e ∈ S)) with h | h
          · rw [hv, h]; exact (hwf e he).1
          · rw [hv, h]; exact (hwf e he).2
        have hd := hdom v hvV
        simp only [branch, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hd
        have hfv : f v = true := by
          rcases hd.2 with h | h
          · exact absurd (pinnedBy_of_mem (S := S) hFe) (by rw [← hv, h]; simp)
          · exact h
        rw [hOR e hFe]
        rcases chosenEnd_mem e (decide (e ∈ S)) with h | h
        · rw [← h, ← hv, hfv]; simp
        · rw [← h, ← hv, hfv]; simp
      · have : e ∈ (branch I F S).Edges := Finset.mem_sdiff.2 ⟨he, hFe⟩
        simpa using hrel e this

/-- **`branch_count`.**  `KERNEL-PROVED`.  The feedback-edge reduction has exactly `2 ^ |F|`
branches. -/
theorem branch_count (F : Finset (ℕ × ℕ)) : F.powerset.card = 2 ^ F.card :=
  Finset.card_powerset F

/-- The feedback set of a supplied spanning forest `T`. -/
def feedbackSet (I : ContactCSP) (T : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) := I.Edges \ T

/-- With a supplied spanning forest `T` of `c` components (so `|T| + c = |V|`), the feedback
set has cardinality `β = |E| - |V| + c`. -/
theorem feedbackSet_card (I : ContactCSP) {T : Finset (ℕ × ℕ)} (hT : T ⊆ I.Edges) {c : ℕ}
    (hcard : T.card + c = I.V.card) :
    ((feedbackSet I T).card : ℤ) = (I.Edges.card : ℤ) - (I.V.card : ℤ) + (c : ℤ) := by
  have h : (feedbackSet I T).card = I.Edges.card - T.card := by
    have h0 : (I.Edges \ T).card = I.Edges.card - (T ∩ I.Edges).card := Finset.card_sdiff
    rwa [Finset.inter_eq_left.2 hT] at h0
  have hle : T.card ≤ I.Edges.card := Finset.card_le_card hT
  omega

/-- Deleting the feedback edges of a supplied spanning forest leaves exactly the forest. -/
theorem branch_edges_eq_forest (I : ContactCSP) {T : Finset (ℕ × ℕ)} (hT : T ⊆ I.Edges)
    (S : Finset (ℕ × ℕ)) : (branch I (feedbackSet I T) S).Edges = T := by
  classical
  ext e
  simp only [branch_Edges, feedbackSet, Finset.mem_sdiff, not_and, not_not]
  constructor
  · rintro ⟨he, h⟩; exact h he
  · intro he; exact ⟨hT he, fun _ => he⟩

/-- **`anchored_forest_branches`.**  `KERNEL-PROVED`.  With a supplied spanning forest `T`
whose feedback edges carry the OR relation, satisfiability of the anchored instance is decided
by at most `2 ^ β` complete anchored forest tests, each of which is an instance whose edge set
is exactly the supplied forest `T`. -/
theorem anchored_forest_branches (I : ContactCSP) {T : Finset (ℕ × ℕ)} (hwf : I.WellFormed)
    (hT : T ⊆ I.Edges) (hOR : IsORContact I (feedbackSet I T)) {c : ℕ}
    (hcard : T.card + c = I.V.card) {β : ℕ} (hβ : (feedbackSet I T).card = β) :
    (I.Sat ↔ ∃ S ∈ (feedbackSet I T).powerset, (branch I (feedbackSet I T) S).Sat) ∧
      (feedbackSet I T).powerset.card = 2 ^ β ∧
      ((β : ℤ) = (I.Edges.card : ℤ) - (I.V.card : ℤ) + (c : ℤ)) ∧
      (∀ S, (branch I (feedbackSet I T) S).Edges = T) := by
  refine ⟨sat_iff_exists_branch I _ hwf Finset.sdiff_subset hOR, ?_, ?_,
    fun S => branch_edges_eq_forest I hT S⟩
  · rw [branch_count, hβ]
  · rw [← hβ]; exact feedbackSet_card I hT hcard

/-- **`beta_two_four_tests`.**  `KERNEL-PROVED`.  Exact decision reduction at excess `β = 2`:
satisfiability is decided by at most **four** complete anchored forest tests.  (No
infeasibility is derived.) -/
theorem beta_two_four_tests (I : ContactCSP) {T : Finset (ℕ × ℕ)} (hwf : I.WellFormed)
    (hOR : IsORContact I (feedbackSet I T))
    (hβ : (feedbackSet I T).card = 2) :
    (I.Sat ↔ ∃ S ∈ (feedbackSet I T).powerset, (branch I (feedbackSet I T) S).Sat) ∧
      (feedbackSet I T).powerset.card = 4 := by
  refine ⟨sat_iff_exists_branch I _ hwf Finset.sdiff_subset hOR, ?_⟩
  rw [branch_count, hβ]
  norm_num

end AnchoredV2
end Erdos287
