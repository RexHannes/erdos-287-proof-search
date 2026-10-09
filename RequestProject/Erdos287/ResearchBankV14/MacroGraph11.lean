import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Coloring

/-!
# Erdős #287 — Research Bank V14 §A2: the macro graph `G(11,2)`

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`G(11,2)` is the cyclic graph on `ℤ/11` in which `r ~ s` iff the circular distance is `≥ 3`.

Kernel-proved (no analytic assumptions):
* `alpha_eq_three` — `α(G) = 3`: the arc `{0,1,2}` is independent and every independent set has
  at most three vertices (`indep_card_le_three`, via the finite check `four_has_edge`);
* `properColouring` — the proper 4-colouring with classes `{0,1,2}, {3,4,5}, {6,7,8}, {9,10}`;
* `no_proper_three_colouring` — so the chromatic number is exactly `4`;
* `occupied_four_forces_edge` — at least four occupied cells force an occupied macro-edge;
* `adj_diff_range` — adjacent cells `r, s` satisfy `3 ≤ |r − s| ≤ 8` (used by the contact
  annulus).
-/

namespace Erdos287
namespace ResearchBankV14
namespace MacroGraph11

/-- Circular distance on `ℤ/11`. -/
def cdist11 (r s : Fin 11) : ℕ := min ((r.val + 11 - s.val) % 11) ((s.val + 11 - r.val) % 11)

/-- The macro graph `G(11,2)`: adjacency iff circular distance `≥ 3`. -/
def G11 : SimpleGraph (Fin 11) where
  Adj r s := 3 ≤ cdist11 r s
  symm := fun r s (h : 3 ≤ cdist11 r s) => show 3 ≤ cdist11 s r by
    unfold cdist11 at *; rwa [min_comm]
  loopless := ⟨fun r (h : 3 ≤ cdist11 r r) => by unfold cdist11 at h; simp at h⟩

instance : DecidableRel G11.Adj := fun r s =>
  inferInstanceAs (Decidable (3 ≤ cdist11 r s))

theorem adj_iff (r s : Fin 11) : G11.Adj r s ↔ 3 ≤ cdist11 r s := Iff.rfl

/-- Every four sorted vertices contain an edge (finite kernel check). -/
theorem four_has_edge : ∀ a b c d : Fin 11, a < b → b < c → c < d →
    G11.Adj a b ∨ G11.Adj a c ∨ G11.Adj a d ∨ G11.Adj b c ∨ G11.Adj b d ∨ G11.Adj c d := by
  decide

/-- An independent set of `G(11,2)`. -/
def IsIndep (S : Finset (Fin 11)) : Prop := ∀ x ∈ S, ∀ y ∈ S, ¬ G11.Adj x y

/-- **`α(G(11,2)) ≤ 3`.** -/
theorem indep_card_le_three (S : Finset (Fin 11)) (hS : IsIndep S) : S.card ≤ 3 := by
  by_contra h
  push_neg at h
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (s := S) (n := 4) (by omega)
  set f := T.orderEmbOfFin hT
  have hm : ∀ i, f i ∈ S := fun i => hTS (Finset.orderEmbOfFin_mem T hT i)
  have h01 : f 0 < f 1 := f.strictMono (by decide)
  have h12 : f 1 < f 2 := f.strictMono (by decide)
  have h23 : f 2 < f 3 := f.strictMono (by decide)
  rcases four_has_edge _ _ _ _ h01 h12 h23 with e | e | e | e | e | e
  · exact hS _ (hm 0) _ (hm 1) e
  · exact hS _ (hm 0) _ (hm 2) e
  · exact hS _ (hm 0) _ (hm 3) e
  · exact hS _ (hm 1) _ (hm 2) e
  · exact hS _ (hm 1) _ (hm 3) e
  · exact hS _ (hm 2) _ (hm 3) e

/-- The arc `{0,1,2}` is independent. -/
theorem arc_indep : IsIndep {0, 1, 2} := by unfold IsIndep; decide

/-- **`α(G(11,2)) = 3`.** -/
theorem alpha_eq_three :
    (∃ S : Finset (Fin 11), IsIndep S ∧ S.card = 3) ∧
      ∀ S : Finset (Fin 11), IsIndep S → S.card ≤ 3 :=
  ⟨⟨{0, 1, 2}, arc_indep, by decide⟩, indep_card_le_three⟩

/-- The colour map `r ↦ ⌊r/3⌋`: classes `{0,1,2}, {3,4,5}, {6,7,8}, {9,10}`. -/
def col4 (r : Fin 11) : Fin 4 := ⟨r.val / 3, by omega⟩

theorem col4_classes :
    (Finset.univ.filter fun r => col4 r = 0) = {0, 1, 2} ∧
    (Finset.univ.filter fun r => col4 r = 1) = {3, 4, 5} ∧
    (Finset.univ.filter fun r => col4 r = 2) = {6, 7, 8} ∧
    (Finset.univ.filter fun r => col4 r = 3) = {9, 10} := by decide

theorem col4_proper : ∀ r s : Fin 11, G11.Adj r s → col4 r ≠ col4 s := by decide

/-- **The proper 4-colouring of `G(11,2)`.** -/
def properColouring : G11.Coloring (Fin 4) :=
  SimpleGraph.Coloring.mk col4 fun {r s} h => col4_proper r s h

/-- **No proper 3-colouring** (each class has at most `α = 3` vertices, `3 · 3 < 11`). -/
theorem no_proper_three_colouring (c : G11.Coloring (Fin 3)) : False := by
  classical
  have hclass : ∀ i : Fin 3, (Finset.univ.filter fun r => c r = i).card ≤ 3 := by
    intro i
    apply indep_card_le_three
    intro x hx y hy hxy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact c.valid hxy (hx.trans hy.symm)
  have hsum := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin 11))) (t := (Finset.univ : Finset (Fin 3)))
    (f := fun r => c r) (fun _ _ => by simp)
  have : (∑ i : Fin 3, (Finset.univ.filter fun r => c r = i).card) ≤ ∑ _i : Fin 3, 3 :=
    Finset.sum_le_sum fun i _ => hclass i
  simp only [Finset.card_univ, Fintype.card_fin, Finset.sum_const, smul_eq_mul] at hsum this
  omega

/-- **Occupancy**: at least four occupied cells force an occupied macro-edge. -/
theorem occupied_four_forces_edge (S : Finset (Fin 11)) (hS : 4 ≤ S.card) :
    ∃ r ∈ S, ∃ s ∈ S, G11.Adj r s := by
  by_contra h
  push_neg at h
  have := indep_card_le_three S h
  omega

/-- Adjacent macro cells differ by `3 … 8`. -/
theorem adj_diff_range : ∀ r s : Fin 11, G11.Adj r s →
    3 ≤ (r.val : ℤ) - s.val ∨ 3 ≤ (s.val : ℤ) - r.val := by decide

theorem adj_diff_le : ∀ r s : Fin 11, G11.Adj r s →
    (r.val : ℤ) - s.val ≤ 8 ∧ (s.val : ℤ) - r.val ≤ 8 := by decide

end MacroGraph11
end ResearchBankV14
end Erdos287
