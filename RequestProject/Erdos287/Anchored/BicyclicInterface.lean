import RequestProject.Erdos287.Anchored.CycleRank

/-!
# The branching kernel interface — deliberately `OPEN`

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Forest components (excess `0`) and isolated cycle components (excess `1`) of the contact graph
are eliminated exactly in `Anchored/ForestElimination.lean` and
`Anchored/CycleElimination.lean`.  What remains after peeling is a finite **leafless**
instance — a *branching kernel* — whose satisfiability is still exactly decidable, but whose
*global rejection* is **not** proved here and is not proved anywhere in this repository.

This file
* states the global rejection statement `BranchingKernelRejection` as a *parameterised
  interface* which is deliberately **not inhabited** (the `OPEN` node of this route);
* proves the hostile firewall `branchingKernelRejection_unconditional_false`: without a
  hypothesis restricting the kernels to those actually produced by the projection, the
  statement is plainly false — an explicit satisfiable leafless instance of excess `2` is
  exhibited;
* records the endpoint theorem of the route (`anchored_contact_endpoint`).
-/

open scoped BigOperators

namespace Erdos287
namespace Anchored

open ContactCSP

/-- **The `OPEN` global step.**  `Arises` is the (here unformalised) predicate selecting the
contact instances actually produced by the high-power projection.  Rejection of *all* the
resulting branching kernels is the open node of this route; no inhabitant is provided. -/
def BranchingKernelRejection (Arises : ContactCSP → Prop) : Prop :=
  ∀ I : ContactCSP, Arises I → Leafless I → 2 ≤ I.excess → ¬ I.Sat

/-- An explicit satisfiable leafless contact instance of excess `2`. -/
def bicyclicWitness : ContactCSP :=
  { V := {0, 1}
    dom := fun _ _ => true
    Edges := {(0, 1), (1, 0), (0, 0)}
    rel := fun _ _ _ _ => true }

theorem bicyclicWitness_sat : bicyclicWitness.Sat :=
  ⟨fun _ => false, by intro v _; rfl, by intro e _; rfl⟩

theorem bicyclicWitness_excess : bicyclicWitness.excess = 2 := by
  have hV : bicyclicWitness.V.card = 2 := by decide
  have hE : bicyclicWitness.Edges.card = 3 := by decide
  simp only [excess, hV, hE]
  norm_num

theorem bicyclicWitness_leafless : Leafless bicyclicWitness := by
  rintro ⟨x, y, -, -, hxy, hedge, hiso⟩
  have hmem : (x, y) = ((0 : ℕ), (1 : ℕ)) ∨ (x, y) = ((1 : ℕ), (0 : ℕ)) ∨
      (x, y) = ((0 : ℕ), (0 : ℕ)) := by
    simpa [bicyclicWitness, Finset.mem_insert] using hedge
  rcases hmem with h | h | h
  · have hx : x = 0 := congrArg Prod.fst h
    have h10 : ((1 : ℕ), (0 : ℕ)) ∈ bicyclicWitness.Edges := by decide
    have hne : ((1 : ℕ), (0 : ℕ)) ≠ (x, y) := by
      intro hcon
      exact absurd (congrArg Prod.fst hcon) (by omega)
    have := (hiso _ h10 hne).2
    simp [hx] at this
  · have hx : x = 1 := congrArg Prod.fst h
    have h01 : ((0 : ℕ), (1 : ℕ)) ∈ bicyclicWitness.Edges := by decide
    have hne : ((0 : ℕ), (1 : ℕ)) ≠ (x, y) := by
      intro hcon
      exact absurd (congrArg Prod.fst hcon) (by omega)
    have := (hiso _ h01 hne).2
    simp [hx] at this
  · exact hxy ((congrArg Prod.fst h).trans (congrArg Prod.snd h).symm)

/-- **`branchingKernelRejection_unconditional_false`.**  `KERNEL-PROVED` hostile firewall.
The global rejection is false without a hypothesis restricting attention to the kernels the
projection actually produces: `bicyclicWitness` is leafless, of excess `2`, and satisfiable. -/
theorem branchingKernelRejection_unconditional_false :
    ¬ BranchingKernelRejection (fun _ => True) := by
  intro h
  exact h bicyclicWitness trivial bicyclicWitness_leafless
    (by rw [bicyclicWitness_excess]) bicyclicWitness_sat

/-! ## A.21  The endpoint theorem of the anchored route -/

/-- **`anchored_contact_endpoint`.**  `KERNEL-PROVED`.  For every finite contact instance:

1. satisfiability is exactly decided by the finite procedure `satB`;
2. a forest component (one peeling to an edgeless instance) is decided exactly by
   nonemptiness of the surviving unary domains;
3. an isolated cycle component is decided exactly by the four-pair transfer criterion;
4. every remaining component reduces, by exact leaf eliminations, to a finite leafless
   branching kernel, with satisfiability preserved and still exactly decidable.

The *global rejection* of the branching kernels is **not** part of this theorem; it is the
`OPEN` node `BranchingKernelRejection`. -/
theorem anchored_contact_endpoint (I : ContactCSP) (hwf : I.WellFormed) :
    (I.Sat ↔ I.satB = true) ∧
    (∀ J, Peel I J → J.Edges = ∅ → (I.Sat ↔ ∀ v ∈ J.V, ∃ b : Bool, J.dom v b = true)) ∧
    (∀ (dom : ℕ → Bool → Bool) (rel : ℕ → ℕ → Bool → Bool → Bool) (x : ℕ) (l : List ℕ),
      (x :: l).Nodup → I = cycleCSP dom rel x l →
        (I.Sat ↔ ∃ a b : Bool,
          transfer dom rel x l a b = true ∧ rel (lastOf x l) x b a = true)) ∧
    (∃ J, Peel I J ∧ Leafless J ∧ (I.Sat ↔ J.Sat) ∧
      (J.WellFormed → (J.Sat ↔ J.satB = true))) := by
  refine ⟨I.sat_iff_satB hwf, ?_, ?_, peel_to_leafless_decidable I⟩
  · intro J hJ hJE
    exact forest_decision hJ hJE
  · rintro dom rel x l hnd rfl
    exact cycleCSP_sat_iff dom rel x l hnd

/-- **`anchored_endpoint_of_layerRel`.**  `KERNEL-PROVED`.  The same endpoint for an instance
whose contact relations are *realized* by the anchored prime-power layer relations: the edge
relations are then exactly the local contact relations of the layers, and all four clauses of
`anchored_contact_endpoint` apply verbatim. -/
theorem anchored_endpoint_of_layerRel (p : ℕ) [Fact p.Prime] (Cof : ℕ → Finset ℕ)
    (I : ContactCSP) (hwf : I.WellFormed)
    (hreal : ∀ e ∈ I.Edges, ∀ a b : Bool,
      I.rel e.1 e.2 a b = layerRel p (Cof e.1) e.1 a b) :
    (∀ e ∈ I.Edges, ∀ a b : Bool,
        (I.rel e.1 e.2 a b = true ↔ LayerAllows p (Cof e.1) (Cof e.1) (sigPair e.1 a b))) ∧
    (I.Sat ↔ I.satB = true) ∧
    (∃ J, Peel I J ∧ Leafless J ∧ (I.Sat ↔ J.Sat) ∧
      (J.WellFormed → (J.Sat ↔ J.satB = true))) := by
  refine ⟨?_, I.sat_iff_satB hwf, peel_to_leafless_decidable I⟩
  intro e he a b
  rw [hreal e he a b]
  exact layerRel_spec p (Cof e.1) e.1 a b

end Anchored
end Erdos287
