import RequestProject.Erdos287.Anchored.ForestElimination
import RequestProject.Erdos287.Anchored.CycleElimination

/-!
# Cycle rank of a contact component, and reduction to a leafless kernel

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The *excess* (cyclomatic count) of a finite contact instance is

`excess I = |Edges| − |V| + 1`.

This file proves:

* `excess_elimLeaf` / `Peel.excess_eq`: leaf elimination preserves the excess exactly;
* `pathCSP_excess` and `cycleCSP_excess`: a contact path has excess `0`, an isolated contact
  cycle has excess `1`;
* `exists_peel_to_leafless`: every finite contact instance peels, in finitely many exact
  steps, to a **leafless** instance — the finite branching kernel — whose satisfiability is
  still exactly decidable (`ContactCSP.sat_iff_satB`).

Nothing here rejects any kernel; that global step is the `OPEN` node recorded in
`Anchored/BicyclicInterface.lean`.
-/

open scoped BigOperators

namespace Erdos287
namespace Anchored

namespace ContactCSP

/-- The excess (cyclomatic count) `|Edges| − |V| + 1` of a finite contact instance. -/
def excess (I : ContactCSP) : ℤ := (I.Edges.card : ℤ) - (I.V.card : ℤ) + 1

/-- **`excess_elimLeaf`.**  `KERNEL-PROVED`.  Leaf elimination removes one position and one
edge, hence preserves the excess. -/
theorem excess_elimLeaf (I : ContactCSP) {x y : ℕ} (hx : x ∈ I.V) (hedge : (x, y) ∈ I.Edges) :
    (I.elimLeaf x y).excess = I.excess := by
  have h1 : (I.elimLeaf x y).V.card = I.V.card - 1 := by
    simpa [elimLeaf] using Finset.card_erase_of_mem hx
  have h2 : (I.elimLeaf x y).Edges.card = I.Edges.card - 1 := by
    simpa [elimLeaf] using Finset.card_erase_of_mem hedge
  have hxpos : 1 ≤ I.V.card := Finset.card_pos.2 ⟨x, hx⟩
  have hepos : 1 ≤ I.Edges.card := Finset.card_pos.2 ⟨(x, y), hedge⟩
  simp only [excess, h1, h2]
  omega

/-- Peeling preserves the excess. -/
theorem Peel.excess_eq {I J : ContactCSP} (h : Peel I J) : J.excess = I.excess := by
  induction h with
  | refl I => rfl
  | step x y hx hy hxy hedge hiso _ ih =>
      rw [ih, excess_elimLeaf _ hx hedge]

/-! ## A.18  Excess of paths and isolated cycles -/

theorem zip_nodup_of_left : ∀ (l₁ l₂ : List ℕ), l₁.Nodup → (l₁.zip l₂).Nodup := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ _; simp
  | cons a t ih =>
      intro l₂ h
      cases l₂ with
      | nil => simp
      | cons b s =>
          rw [List.zip_cons_cons]
          refine List.nodup_cons.2 ⟨?_, ih s (List.nodup_cons.1 h).2⟩
          intro hmem
          exact (List.nodup_cons.1 h).1 (List.of_mem_zip hmem).1

/-- A contact path has excess `0`. -/
theorem pathCSP_excess (dom : ℕ → Bool → Bool) (rel : ℕ → ℕ → Bool → Bool → Bool)
    (x : ℕ) (l : List ℕ) (hnd : (x :: l).Nodup) : (pathCSP dom rel x l).excess = 0 := by
  have hV : (pathCSP dom rel x l).V.card = l.length + 1 := by
    rw [show (pathCSP dom rel x l).V = (x :: l).toFinset from rfl,
      List.toFinset_card_of_nodup hnd]
    simp
  have hE : (pathCSP dom rel x l).Edges.card = l.length := by
    have hnd' : ((x :: l).zip l).Nodup := zip_nodup_of_left _ _ hnd
    rw [show (pathCSP dom rel x l).Edges = ((x :: l).zip l).toFinset from rfl,
      List.toFinset_card_of_nodup hnd']
    simp [List.length_zip]
  simp only [excess, hV, hE]
  omega

/-- An isolated contact cycle has excess `1`. -/
theorem cycleCSP_excess (dom : ℕ → Bool → Bool) (rel : ℕ → ℕ → Bool → Bool → Bool)
    (x : ℕ) (l : List ℕ) (hnd : (x :: l).Nodup) : (cycleCSP dom rel x l).excess = 1 := by
  have hV : (cycleCSP dom rel x l).V.card = l.length + 1 := by
    rw [show (cycleCSP dom rel x l).V = (x :: l).toFinset from rfl,
      List.toFinset_card_of_nodup hnd]
    simp
  have hnd' : ((x :: l).zip l).Nodup := zip_nodup_of_left _ _ hnd
  have hnotmem : (lastOf x l, x) ∉ ((x :: l).zip l).toFinset := by
    intro hmem
    rw [List.mem_toFinset] at hmem
    have hx : x ∈ l := (List.of_mem_zip hmem).2
    exact (List.nodup_cons.1 hnd).1 hx
  have hE : (cycleCSP dom rel x l).Edges.card = l.length + 1 := by
    rw [show (cycleCSP dom rel x l).Edges
        = insert (lastOf x l, x) (((x :: l).zip l).toFinset) from rfl,
      Finset.card_insert_of_notMem hnotmem, List.toFinset_card_of_nodup hnd']
    simp [List.length_zip]
  simp only [excess, hV, hE]
  omega

/-! ## A.19  Reduction to the finite leafless kernel -/

/-- `x` is an eliminable leaf of `I`, with unique contact edge `(x, y)`. -/
def IsLeafWith (I : ContactCSP) (x y : ℕ) : Prop :=
  x ∈ I.V ∧ y ∈ I.V ∧ x ≠ y ∧ (x, y) ∈ I.Edges ∧
    ∀ e ∈ I.Edges, e ≠ (x, y) → e.1 ≠ x ∧ e.2 ≠ x

/-- An instance with no eliminable leaf: the finite branching kernel of the component. -/
def Leafless (I : ContactCSP) : Prop := ¬ ∃ x y : ℕ, IsLeafWith I x y

/-- **`exists_peel_to_leafless`.**  `KERNEL-PROVED`.  Every finite contact instance reduces,
by finitely many exact leaf eliminations, to a leafless instance (a finite branching kernel),
with satisfiability preserved at every step. -/
theorem exists_peel_to_leafless (I : ContactCSP) : ∃ J, Peel I J ∧ Leafless J := by
  classical
  generalize hn : I.Edges.card = n
  induction n using Nat.strong_induction_on generalizing I with
  | _ n ih =>
      by_cases hleaf : ∃ x y : ℕ, IsLeafWith I x y
      · obtain ⟨x, y, hx, hy, hxy, hedge, hiso⟩ := hleaf
        have hlt : (I.elimLeaf x y).Edges.card < n := by
          rw [← hn]
          exact elimLeaf_edges_card_lt I hedge
        obtain ⟨J, hJ, hJleaf⟩ := ih _ hlt (I.elimLeaf x y) rfl
        exact ⟨J, Peel.step x y hx hy hxy hedge hiso hJ, hJleaf⟩
      · exact ⟨I, Peel.refl I, hleaf⟩

/-- The reduction of `exists_peel_to_leafless` is satisfiability-exact, and the resulting
finite kernel is itself exactly decidable. -/
theorem peel_to_leafless_decidable (I : ContactCSP) :
    ∃ J, Peel I J ∧ Leafless J ∧ (I.Sat ↔ J.Sat) ∧
      (J.WellFormed → (J.Sat ↔ J.satB = true)) := by
  obtain ⟨J, hJ, hJl⟩ := exists_peel_to_leafless I
  exact ⟨J, hJ, hJl, hJ.sat_iff, fun hwf => J.sat_iff_satB hwf⟩

end ContactCSP

end Anchored
end Erdos287
