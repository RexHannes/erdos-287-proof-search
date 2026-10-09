import RequestProject.Erdos287.Anchored.CycleRank

/-!
# Anchored V2 — exact block-cut gluing at a certified articulation set

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

A *certified* block-cut decomposition of a finite anchored contact instance `I` into two blocks
`I₁, I₂` meeting only in an articulation set `art` is supplied as data (`SplitAt`), together
with the proof obligations that make it a decomposition: the vertex and edge sets are the
unions, each block's edges stay inside the block, the local relations agree with the ambient
ones, and the ambient unary domain is the conjunction of the two block domains (each block's
domain being vacuous outside the block).

The *message* a block sends across the articulation set is its `BoundaryMsg`: the set of
boundary assignments extendable to a full local solution.  The main theorem states that
feasibility is **exactly** the existence of a common boundary message, in both directions.
Note that a contact position occurring in two blocks is literally the same Boolean variable.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV2

open Erdos287.Anchored
open Erdos287.Anchored.ContactCSP

/-- The message a block sends across the articulation set: `g` restricted to `art` extends to a
full local solution of `I`. -/
def BoundaryMsg (I : ContactCSP) (art : Finset ℕ) (g : ℕ → Bool) : Prop :=
  ∃ f : ℕ → Bool, (∀ v ∈ art, f v = g v) ∧ (∀ v ∈ I.V, I.dom v (f v) = true) ∧
    ∀ e ∈ I.Edges, I.rel e.1 e.2 (f e.1) (f e.2) = true

/-- The one-contact message of a block at a single articulation position. -/
def MsgAt (I : ContactCSP) (a : ℕ) (x : Bool) : Prop :=
  ∃ f : ℕ → Bool, f a = x ∧ (∀ v ∈ I.V, I.dom v (f v) = true) ∧
    ∀ e ∈ I.Edges, I.rel e.1 e.2 (f e.1) (f e.2) = true

/-- The two-contact message of a block at two articulation positions (the relation a cycle
child sends to its articulation contacts). -/
def Msg2At (I : ContactCSP) (a b : ℕ) (x y : Bool) : Prop :=
  ∃ f : ℕ → Bool, f a = x ∧ f b = y ∧ (∀ v ∈ I.V, I.dom v (f v) = true) ∧
    ∀ e ∈ I.Edges, I.rel e.1 e.2 (f e.1) (f e.2) = true

/-- A certified block-cut decomposition of `I` into `I₁` and `I₂` meeting in `art`. -/
structure SplitAt (I I₁ I₂ : ContactCSP) (art : Finset ℕ) : Prop where
  /-- the positions are the union of the two blocks' positions -/
  V_eq : I.V = I₁.V ∪ I₂.V
  /-- the two blocks meet only in the articulation set -/
  inter_sub : I₁.V ∩ I₂.V ⊆ art
  /-- the contact edges are the union of the two blocks' contact edges -/
  Edges_eq : I.Edges = I₁.Edges ∪ I₂.Edges
  /-- the first block's edges stay inside it -/
  edges₁ : ∀ e ∈ I₁.Edges, e.1 ∈ I₁.V ∧ e.2 ∈ I₁.V
  /-- the second block's edges stay inside it -/
  edges₂ : ∀ e ∈ I₂.Edges, e.1 ∈ I₂.V ∧ e.2 ∈ I₂.V
  /-- the first block carries the ambient local relations -/
  rel₁ : ∀ e ∈ I₁.Edges, ∀ a b, I₁.rel e.1 e.2 a b = I.rel e.1 e.2 a b
  /-- the second block carries the ambient local relations -/
  rel₂ : ∀ e ∈ I₂.Edges, ∀ a b, I₂.rel e.1 e.2 a b = I.rel e.1 e.2 a b
  /-- the ambient unary domain is the conjunction of the two block domains -/
  dom_eq : ∀ v b, I.dom v b = (I₁.dom v b && I₂.dom v b)
  /-- the first block's domain is vacuous outside it -/
  dom₁_out : ∀ v, v ∉ I₁.V → ∀ b, I₁.dom v b = true
  /-- the second block's domain is vacuous outside it -/
  dom₂_out : ∀ v, v ∉ I₂.V → ∀ b, I₂.dom v b = true

/-- **`sat_split_iff`.**  Feasibility preservation in both directions for a certified block-cut
decomposition: the instance is satisfiable exactly when the two blocks send a common
articulation message. -/
theorem sat_split_iff {I I₁ I₂ : ContactCSP} {art : Finset ℕ} (h : SplitAt I I₁ I₂ art) :
    I.Sat ↔ ∃ g : ℕ → Bool, BoundaryMsg I₁ art g ∧ BoundaryMsg I₂ art g := by
  classical
  constructor
  · rintro ⟨f, hdom, hrel⟩
    refine ⟨f, ⟨f, fun v _ => rfl, ?_, ?_⟩, ⟨f, fun v _ => rfl, ?_, ?_⟩⟩
    · intro v hv
      have hvI : v ∈ I.V := by rw [h.V_eq]; exact Finset.mem_union_left _ hv
      have hd := hdom v hvI
      rw [h.dom_eq, Bool.and_eq_true] at hd
      exact hd.1
    · intro e he
      have heI : e ∈ I.Edges := by rw [h.Edges_eq]; exact Finset.mem_union_left _ he
      rw [h.rel₁ e he]
      exact hrel e heI
    · intro v hv
      have hvI : v ∈ I.V := by rw [h.V_eq]; exact Finset.mem_union_right _ hv
      have hd := hdom v hvI
      rw [h.dom_eq, Bool.and_eq_true] at hd
      exact hd.2
    · intro e he
      have heI : e ∈ I.Edges := by rw [h.Edges_eq]; exact Finset.mem_union_right _ he
      rw [h.rel₂ e he]
      exact hrel e heI
  · rintro ⟨g, ⟨f₁, ha₁, hd₁, hr₁⟩, ⟨f₂, ha₂, hd₂, hr₂⟩⟩
    set f : ℕ → Bool := fun v => if v ∈ I₁.V then f₁ v else f₂ v with hf
    have hboth : ∀ v ∈ I₁.V, v ∈ I₂.V → f₁ v = f₂ v := by
      intro v h1 h2
      have hart : v ∈ art := h.inter_sub (Finset.mem_inter.2 ⟨h1, h2⟩)
      rw [ha₁ v hart, ha₂ v hart]
    have hf1 : ∀ v ∈ I₁.V, f v = f₁ v := by
      intro v hv; simp [hf, hv]
    have hf2 : ∀ v ∈ I₂.V, f v = f₂ v := by
      intro v hv
      by_cases h1 : v ∈ I₁.V
      · simp [hf, h1, hboth v h1 hv]
      · simp [hf, h1]
    refine ⟨f, ?_, ?_⟩
    · intro v hv
      rw [h.dom_eq, Bool.and_eq_true]
      constructor
      · by_cases h1 : v ∈ I₁.V
        · rw [hf1 v h1]; exact hd₁ v h1
        · exact h.dom₁_out v h1 _
      · by_cases h2 : v ∈ I₂.V
        · rw [hf2 v h2]; exact hd₂ v h2
        · exact h.dom₂_out v h2 _
    · intro e he
      rw [h.Edges_eq] at he
      rcases Finset.mem_union.1 he with he1 | he2
      · rw [← h.rel₁ e he1, hf1 _ (h.edges₁ e he1).1, hf1 _ (h.edges₁ e he1).2]
        exact hr₁ e he1
      · rw [← h.rel₂ e he2, hf2 _ (h.edges₂ e he2).1, hf2 _ (h.edges₂ e he2).2]
        exact hr₂ e he2

/-- The articulation message at a single contact position determines the boundary message. -/
theorem boundaryMsg_singleton (I : ContactCSP) (a : ℕ) (g : ℕ → Bool) :
    BoundaryMsg I {a} g ↔ MsgAt I a (g a) := by
  constructor
  · rintro ⟨f, hag, hd, hr⟩
    exact ⟨f, hag a (Finset.mem_singleton_self a), hd, hr⟩
  · rintro ⟨f, hfa, hd, hr⟩
    refine ⟨f, ?_, hd, hr⟩
    intro v hv
    rw [Finset.mem_singleton.1 hv, hfa]

/-- **`sat_split_single_iff`.**  Exact decision at a single articulation position: the instance
is satisfiable exactly when both blocks admit the same Boolean value at the articulation. -/
theorem sat_split_single_iff {I I₁ I₂ : ContactCSP} {a : ℕ} (h : SplitAt I I₁ I₂ {a}) :
    I.Sat ↔ ∃ x : Bool, MsgAt I₁ a x ∧ MsgAt I₂ a x := by
  rw [sat_split_iff h]
  constructor
  · rintro ⟨g, h1, h2⟩
    exact ⟨g a, (boundaryMsg_singleton I₁ a g).1 h1, (boundaryMsg_singleton I₂ a g).1 h2⟩
  · rintro ⟨x, h1, h2⟩
    refine ⟨fun _ => x, ?_, ?_⟩
    · exact (boundaryMsg_singleton I₁ a (fun _ => x)).2 h1
    · exact (boundaryMsg_singleton I₂ a (fun _ => x)).2 h2

end AnchoredV2
end Erdos287
