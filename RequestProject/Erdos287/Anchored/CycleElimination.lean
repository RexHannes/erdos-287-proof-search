import RequestProject.Erdos287.Anchored.PathTransfer

/-!
# Exact elimination of isolated contact cycles

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

An *isolated cycle component* of the contact graph is a repetition-free cyclic list of contact
positions `x :: l` together with the closing contact edge `(last, x)`.  This file proves that
such a component is satisfiable exactly when the composed transfer of the path admits a pair
of endpoint values compatible with the closing relation:

`Sat ↔ ∃ a b, transfer … x l a b = true ∧ rel (last) x b a = true`,

a check over four Boolean pairs.  Cycle components are therefore *exactly decidable*.
-/

open scoped BigOperators

namespace Erdos287
namespace Anchored

variable (dom : ℕ → Bool → Bool) (rel : ℕ → ℕ → Bool → Bool → Bool)

/-- The contact instance carried by the cycle through `x :: l`. -/
def cycleCSP (dom : ℕ → Bool → Bool) (rel : ℕ → ℕ → Bool → Bool → Bool)
    (x : ℕ) (l : List ℕ) : ContactCSP :=
  { V := (x :: l).toFinset
    dom := dom
    Edges := insert (lastOf x l, x) (((x :: l).zip l).toFinset)
    rel := rel }

theorem cycleCSP_wellFormed (x : ℕ) (l : List ℕ) : (cycleCSP dom rel x l).WellFormed := by
  intro e he
  simp only [cycleCSP, Finset.mem_insert, List.mem_toFinset] at he
  rcases he with rfl | he
  · exact ⟨by simpa [cycleCSP, List.mem_toFinset] using lastOf_mem x l,
      by simp [cycleCSP, List.mem_toFinset]⟩
  · have := List.of_mem_zip he
    exact ⟨by simpa [cycleCSP, List.mem_toFinset] using this.1,
      by simpa [cycleCSP, List.mem_toFinset] using List.mem_cons_of_mem x this.2⟩

/-- **`cycleCSP_sat_iff`.**  `KERNEL-PROVED`.  Exact decision of an isolated cycle component
by the composed transfer plus the closing relation. -/
theorem cycleCSP_sat_iff (x : ℕ) (l : List ℕ) (hnd : (x :: l).Nodup) :
    (cycleCSP dom rel x l).Sat ↔
      ∃ a b : Bool, transfer dom rel x l a b = true ∧ rel (lastOf x l) x b a = true := by
  constructor
  · rintro ⟨f, hdom, hrel⟩
    have hok : chainOk dom rel x l f := by
      refine (chainOk_iff dom rel x l f).2 ⟨?_, ?_⟩
      · intro v hv
        exact hdom v (by simpa [cycleCSP, List.mem_toFinset] using hv)
      · intro e he
        refine hrel e ?_
        simp only [cycleCSP, Finset.mem_insert, List.mem_toFinset]
        exact Or.inr he
    have hclose : rel (lastOf x l) x (f (lastOf x l)) (f x) = true :=
      hrel (lastOf x l, x) (by simp [cycleCSP])
    exact ⟨f x, f (lastOf x l),
      (transfer_spec dom rel x l hnd _ _).2 ⟨f, rfl, rfl, hok⟩, hclose⟩
  · rintro ⟨a, b, htr, hclose⟩
    obtain ⟨f, hfx, hfb, hok⟩ := (transfer_spec dom rel x l hnd a b).1 htr
    obtain ⟨h1, h2⟩ := (chainOk_iff dom rel x l f).1 hok
    refine ⟨f, ?_, ?_⟩
    · intro v hv
      exact h1 v (by simpa [cycleCSP, List.mem_toFinset] using hv)
    · intro e he
      simp only [cycleCSP, Finset.mem_insert, List.mem_toFinset] at he
      rcases he with rfl | he
      · simpa [hfx, hfb] using hclose
      · exact h2 e he

/-- Satisfiability of an isolated cycle component is decidable by the finite four-pair
check. -/
instance decidableCycleCriterion (x : ℕ) (l : List ℕ) :
    Decidable (∃ a b : Bool, transfer dom rel x l a b = true ∧ rel (lastOf x l) x b a = true) :=
  inferInstance

end Anchored
end Erdos287
