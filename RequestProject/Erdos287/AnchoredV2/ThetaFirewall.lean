import RequestProject.Erdos287.AnchoredV2.AffineNormalForm
import RequestProject.Erdos287.AnchoredV2.FeedbackEdge

/-!
# Anchored V2 — the theta / bicyclic firewall

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

A small finite **satisfiable** example showing that

theta (`β = 2`) topology + balanced affine transfers + locally feasible relations

does **not** imply a contradiction.  The example is an abstract contact-relation instance: the
theta graph on four positions with contact (OR) relations and unconstrained unary domains,
together with the fully balanced affine transfer data in which every tree relation and every
fundamental non-tree relation is the identity.

This is a *logical firewall* only.  It is **not** a #287 survivor and says nothing about actual
arithmetic kernels.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV2

open Erdos287.Anchored
open Erdos287.Anchored.ContactCSP

/-- The theta contact instance: two hubs `0, 1` joined by three internally disjoint paths. -/
def thetaCSP : ContactCSP where
  V := {0, 1, 2, 3}
  dom := fun _ _ => true
  Edges := {(0, 2), (2, 1), (0, 3), (3, 1), (0, 1)}
  rel := fun _ _ a b => a || b

theorem thetaCSP_wellFormed : thetaCSP.WellFormed := by
  intro e he
  fin_cases he <;> exact ⟨by decide, by decide⟩

theorem thetaCSP_sat : thetaCSP.Sat :=
  ⟨fun _ => true, by intro v _; rfl, by intro e _; rfl⟩

theorem thetaCSP_excess : thetaCSP.excess = 2 := by
  have hV : thetaCSP.V.card = 4 := by decide
  have hE : thetaCSP.Edges.card = 5 := by decide
  simp only [excess, hV, hE]
  norm_num

theorem thetaCSP_leafless : Leafless thetaCSP := by
  rintro ⟨x, y, -, -, hxy, hedge, hiso⟩
  have hmem : (x, y) = ((0 : ℕ), (2 : ℕ)) ∨ (x, y) = ((2 : ℕ), (1 : ℕ)) ∨
      (x, y) = ((0 : ℕ), (3 : ℕ)) ∨ (x, y) = ((3 : ℕ), (1 : ℕ)) ∨
      (x, y) = ((0 : ℕ), (1 : ℕ)) := by
    simpa [thetaCSP, Finset.mem_insert] using hedge
  have hx : ∀ z w : ℕ, (z, w) ∈ thetaCSP.Edges → (z, w) ≠ (x, y) → z ≠ x ∧ w ≠ x :=
    fun z w h h' => hiso (z, w) h h'
  rcases hmem with h | h | h | h | h <;>
    (have h1 : x = ((x, y) : ℕ × ℕ).1 := rfl) <;> rw [h] at h1 <;> subst h1
  · have := (hx 0 3 (by decide) (by rw [h]; decide)).1
    exact this rfl
  · have := (hx 0 2 (by decide) (by rw [h]; decide)).2
    exact this rfl
  · have := (hx 0 2 (by decide) (by rw [h]; decide)).1
    exact this rfl
  · have := (hx 0 3 (by decide) (by rw [h]; decide)).2
    exact this rfl
  · have := (hx 0 2 (by decide) (by rw [h]; decide)).1
    exact this rfl

/-- The fully balanced affine transfer data of the theta example: all tree relations and all
fundamental non-tree relations are the identity. -/
def thetaAffine : AffineTreeData where
  verts := {0, 1, 2, 3}
  root := 0
  parent := fun v => if v = 1 then 2 else 0
  tcoef := fun _ => 1
  tconst := fun _ => 0
  depth := fun v => if v = 0 then 0 else if v = 1 then 2 else 1
  alpha := fun _ => 1
  beta := fun _ => 0
  nonTree := {(1, 3), (1, 0)}
  ncoef := fun _ => 1
  nconst := fun _ => 0

theorem thetaAffine_certified : thetaAffine.Certified := by
  constructor
  · decide
  · rfl
  · rfl
  · intro v hv _
    fin_cases hv <;> decide
  · intro v hv hne
    fin_cases hv <;> simp_all [thetaAffine]
  · intro v _ _; simp [thetaAffine]
  · intro v _ _; simp [thetaAffine]
  · intro e he
    fin_cases he <;> decide

theorem thetaAffine_fullyBalanced : thetaAffine.FullyBalanced := by
  intro e he
  fin_cases he <;>
    simp [AffineTreeData.edgeCoef, AffineTreeData.edgeConst, thetaAffine]

/-- The unconditional rejection of balanced theta kernels. -/
def ThetaBalancedRejection : Prop :=
  ∀ (I : ContactCSP) (D : AffineTreeData), I.excess = 2 → Leafless I → D.Certified →
    D.FullyBalanced → (∀ v ∈ I.V, ∃ b : Bool, I.dom v b = true) → ¬ I.Sat

/-- **`thetaBalancedRejection_false`.**  `KERNEL-PROVED` firewall.  A theta (`β = 2`) topology
with balanced affine transfers and locally feasible relations need **not** be contradictory:
the explicit abstract example above satisfies all the hypotheses and is satisfiable. -/
theorem thetaBalancedRejection_false : ¬ ThetaBalancedRejection := by
  intro h
  exact h thetaCSP thetaAffine thetaCSP_excess thetaCSP_leafless thetaAffine_certified
    thetaAffine_fullyBalanced (fun v _ => ⟨true, rfl⟩) thetaCSP_sat

end AnchoredV2
end Erdos287
