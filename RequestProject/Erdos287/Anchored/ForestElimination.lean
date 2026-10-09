import RequestProject.Erdos287.Anchored.ContactGraph

/-!
# Exact leaf elimination on the contact graph (forest components)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

A *leaf* of the contact graph is a position `x` occurring in exactly one contact edge
`(x, y)`.  Eliminating it means deleting `x` and the edge, and intersecting the unary domain
at `y` with the projection of the local relation.  This file proves:

* `sat_elimLeaf_iff`: leaf elimination preserves satisfiability **exactly** (both directions);
* `elimLeaf_edges_card_lt`: each elimination strictly decreases the number of contact edges,
  so the process terminates;
* `Peel.sat_iff` and `forest_decision`: a component that peels to an edgeless instance — i.e.
  a forest component — is satisfiable exactly when every remaining unary domain is nonempty.
-/

open scoped BigOperators

namespace Erdos287
namespace Anchored

namespace ContactCSP

/-- Eliminate the leaf `x`, whose only contact edge is `(x, y)`. -/
def elimLeaf (I : ContactCSP) (x y : ℕ) : ContactCSP :=
  { V := I.V.erase x
    dom := fun v b =>
      if v = y then
        I.dom v b && ((I.dom x false && I.rel x y false b) || (I.dom x true && I.rel x y true b))
      else I.dom v b
    Edges := I.Edges.erase (x, y)
    rel := I.rel }

@[simp] theorem elimLeaf_V (I : ContactCSP) (x y : ℕ) : (I.elimLeaf x y).V = I.V.erase x := rfl

@[simp] theorem elimLeaf_Edges (I : ContactCSP) (x y : ℕ) :
    (I.elimLeaf x y).Edges = I.Edges.erase (x, y) := rfl

@[simp] theorem elimLeaf_rel (I : ContactCSP) (x y : ℕ) : (I.elimLeaf x y).rel = I.rel := rfl

theorem elimLeaf_dom (I : ContactCSP) (x y v : ℕ) (b : Bool) :
    (I.elimLeaf x y).dom v b =
      (if v = y then
        I.dom v b && ((I.dom x false && I.rel x y false b) || (I.dom x true && I.rel x y true b))
      else I.dom v b) := rfl

theorem elimLeaf_dom_of_ne (I : ContactCSP) {x y v : ℕ} (h : v ≠ y) (b : Bool) :
    (I.elimLeaf x y).dom v b = I.dom v b := by
  rw [elimLeaf_dom, if_neg h]

theorem elimLeaf_dom_self (I : ContactCSP) (x y : ℕ) (b : Bool) :
    (I.elimLeaf x y).dom y b =
      (I.dom y b && ((I.dom x false && I.rel x y false b) ||
        (I.dom x true && I.rel x y true b))) := by
  rw [elimLeaf_dom, if_pos rfl]

theorem elimLeaf_wellFormed {I : ContactCSP} {x y : ℕ} (hwf : I.WellFormed)
    (hiso : ∀ e ∈ I.Edges, e ≠ (x, y) → e.1 ≠ x ∧ e.2 ≠ x) :
    (I.elimLeaf x y).WellFormed := by
  intro e he
  rw [elimLeaf_Edges, Finset.mem_erase] at he
  obtain ⟨hne, hmem⟩ := he
  obtain ⟨h1, h2⟩ := hwf e hmem
  obtain ⟨k1, k2⟩ := hiso e hmem hne
  exact ⟨by rw [elimLeaf_V]; exact Finset.mem_erase.2 ⟨k1, h1⟩,
    by rw [elimLeaf_V]; exact Finset.mem_erase.2 ⟨k2, h2⟩⟩

/-- **`sat_elimLeaf_iff`.**  `KERNEL-PROVED`.  Leaf elimination preserves satisfiability
exactly. -/
theorem sat_elimLeaf_iff (I : ContactCSP) {x y : ℕ} (hx : x ∈ I.V) (hy : y ∈ I.V)
    (hxy : x ≠ y) (hedge : (x, y) ∈ I.Edges)
    (hiso : ∀ e ∈ I.Edges, e ≠ (x, y) → e.1 ≠ x ∧ e.2 ≠ x) :
    I.Sat ↔ (I.elimLeaf x y).Sat := by
  classical
  constructor
  · rintro ⟨f, hdom, hrel⟩
    refine ⟨f, ?_, ?_⟩
    · intro v hv
      rw [elimLeaf_V, Finset.mem_erase] at hv
      have hvV : v ∈ I.V := hv.2
      by_cases hvy : v = y
      · subst hvy
        have h1 : I.dom v (f v) = true := hdom v hvV
        have h2 : I.rel x v (f x) (f v) = true := hrel (x, v) hedge
        have h3 : I.dom x (f x) = true := hdom x hx
        rw [elimLeaf_dom_self, Bool.and_eq_true]
        refine ⟨h1, ?_⟩
        rw [Bool.or_eq_true]
        rcases hfx : f x with _ | _
        · rw [hfx] at h2 h3
          exact Or.inl (by rw [Bool.and_eq_true]; exact ⟨h3, h2⟩)
        · rw [hfx] at h2 h3
          exact Or.inr (by rw [Bool.and_eq_true]; exact ⟨h3, h2⟩)
      · rw [elimLeaf_dom_of_ne I hvy]
        exact hdom v hvV
    · intro e he
      rw [elimLeaf_rel]
      rw [elimLeaf_Edges] at he
      exact hrel e (Finset.mem_of_mem_erase he)
  · rintro ⟨g, hdom, hrel⟩
    have hyV : y ∈ (I.elimLeaf x y).V := by
      rw [elimLeaf_V]
      exact Finset.mem_erase.2 ⟨fun h => hxy h.symm, hy⟩
    have hgy := hdom y hyV
    rw [elimLeaf_dom_self, Bool.and_eq_true, Bool.or_eq_true] at hgy
    obtain ⟨hgdom, hgc⟩ := hgy
    obtain ⟨c, hcx, hcrel⟩ : ∃ c : Bool, I.dom x c = true ∧ I.rel x y c (g y) = true := by
      rcases hgc with h | h
      · rw [Bool.and_eq_true] at h
        exact ⟨false, h.1, h.2⟩
      · rw [Bool.and_eq_true] at h
        exact ⟨true, h.1, h.2⟩
    refine ⟨Function.update g x c, ?_, ?_⟩
    · intro v hv
      by_cases hvx : v = x
      · subst hvx
        simpa using hcx
      · have hv' : v ∈ (I.elimLeaf x y).V := by
          rw [elimLeaf_V]
          exact Finset.mem_erase.2 ⟨hvx, hv⟩
        have hgv := hdom v hv'
        rw [Function.update_of_ne hvx]
        by_cases hvy : v = y
        · subst hvy
          rw [elimLeaf_dom_self, Bool.and_eq_true] at hgv
          exact hgv.1
        · rw [elimLeaf_dom_of_ne I hvy] at hgv
          exact hgv
    · intro e he
      by_cases hexy : e = (x, y)
      · subst hexy
        have k1 : Function.update g x c (x, y).1 = c := by simp
        have k2 : Function.update g x c (x, y).2 = g y := by
          simp [Function.update_of_ne (show (x, y).2 ≠ x from fun h => hxy h.symm)]
        rw [k1, k2]
        exact hcrel
      · obtain ⟨k1, k2⟩ := hiso e he hexy
        have he' : e ∈ (I.elimLeaf x y).Edges := by
          rw [elimLeaf_Edges]
          exact Finset.mem_erase.2 ⟨hexy, he⟩
        have hge := hrel e he'
        rw [elimLeaf_rel] at hge
        rw [Function.update_of_ne k1, Function.update_of_ne k2]
        exact hge

/-- Each leaf elimination strictly decreases the number of contact edges. -/
theorem elimLeaf_edges_card_lt (I : ContactCSP) {x y : ℕ} (hedge : (x, y) ∈ I.Edges) :
    (I.elimLeaf x y).Edges.card < I.Edges.card := by
  rw [elimLeaf_Edges]
  exact Finset.card_erase_lt_of_mem hedge

/-! ## A.17  Iterated peeling -/

/-- `Peel I J`: the instance `J` is obtained from `I` by a finite sequence of exact leaf
eliminations. -/
inductive Peel : ContactCSP → ContactCSP → Prop
  /-- the empty sequence -/
  | refl (I : ContactCSP) : Peel I I
  /-- one exact leaf elimination, followed by a peel -/
  | step {I J : ContactCSP} (x y : ℕ) (hx : x ∈ I.V) (hy : y ∈ I.V) (hxy : x ≠ y)
      (hedge : (x, y) ∈ I.Edges)
      (hiso : ∀ e ∈ I.Edges, e ≠ (x, y) → e.1 ≠ x ∧ e.2 ≠ x)
      (h : Peel (I.elimLeaf x y) J) : Peel I J

/-- **`Peel.sat_iff`.**  `KERNEL-PROVED`.  Peeling preserves satisfiability exactly. -/
theorem Peel.sat_iff {I J : ContactCSP} (h : Peel I J) : I.Sat ↔ J.Sat := by
  induction h with
  | refl I => exact Iff.rfl
  | step x y hx hy hxy hedge hiso _ ih =>
      exact (sat_elimLeaf_iff _ hx hy hxy hedge hiso).trans ih

/-- **`forest_decision`.**  `KERNEL-PROVED`.  A component that peels to an edgeless instance
(a forest component) is satisfiable exactly when every surviving unary domain is nonempty.
This is an exact, finite decision. -/
theorem forest_decision {I J : ContactCSP} (h : Peel I J) (hJ : J.Edges = ∅) :
    I.Sat ↔ ∀ v ∈ J.V, ∃ b : Bool, J.dom v b = true :=
  (h.sat_iff).trans (J.sat_iff_domains_nonempty_of_no_edges hJ)

end ContactCSP

end Anchored
end Erdos287
