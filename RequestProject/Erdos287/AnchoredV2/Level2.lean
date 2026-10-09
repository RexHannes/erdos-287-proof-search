import RequestProject.Erdos287.AnchoredV2.Capacity

/-!
# Anchored V2 — the Level-2 fractional interface

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

This is **not** a general LP library: only the finite data needed for *pair marginals* is
defined.  For every contact edge `e` with endpoint blocks `(v, w)` a Level-2 fractional witness
carries finite nonnegative rational weights `μ e (X, Y)` on pairs of local states, supported on
pairs that are admissible on both sides and cover the edge, with total mass `1` on every edge
and with **consistent one-block marginals** across all edges incident to a block.

Proved here: integral feasibility implies Level-2 fractional feasibility (`level2_of_feasible`,
by taking Dirac weights), hence Level-2 infeasibility is a *sound rejection certificate*
(`not_feasible_of_not_level2`).  The converse is **not** claimed.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV2

namespace PortSystem

variable {E : Type*} [DecidableEq E]

/-- The marginal of the pair distribution on the edge `e` at the block `u`, evaluated on the
local state `B`. -/
def margAt (S : PortSystem E) (μ : E → Finset E × Finset E → ℚ) (e : E) (u : ℕ)
    (B : Finset E) : ℚ :=
  if (S.ep e).1 = u then ∑ Y ∈ S.L (S.ep e).2, μ e (B, Y)
  else ∑ X ∈ S.L (S.ep e).1, μ e (X, B)

/-- The block `u` is incident to the contact edge `e`. -/
def Incident (S : PortSystem E) (e : E) (u : ℕ) : Prop := (S.ep e).1 = u ∨ (S.ep e).2 = u

/-- **Level-2 fractional feasibility**: finite nonnegative rational weights on admissible
covering pairs, of total mass one on every edge, with consistent one-block marginals. -/
def Level2FractionalFeasible (S : PortSystem E) : Prop :=
  ∃ μ : E → Finset E × Finset E → ℚ,
    (∀ e P, 0 ≤ μ e P) ∧
    (∀ e ∈ S.Edges, ∀ X Y, μ e (X, Y) ≠ 0 →
      X ∈ S.L (S.ep e).1 ∧ Y ∈ S.L (S.ep e).2 ∧ (e ∈ X ∨ e ∈ Y)) ∧
    (∀ e ∈ S.Edges, ∑ X ∈ S.L (S.ep e).1, ∑ Y ∈ S.L (S.ep e).2, μ e (X, Y) = 1) ∧
    (∀ u ∈ S.Blocks, ∀ e ∈ S.Edges, ∀ e' ∈ S.Edges, S.Incident e u → S.Incident e' u →
      ∀ B ∈ S.L u, S.margAt μ e u B = S.margAt μ e' u B)

/-- **`level2_of_feasible`.**  Integral feasibility implies Level-2 fractional feasibility:
the Dirac weights of an integral solution form a Level-2 witness. -/
theorem level2_of_feasible {S : PortSystem E} (hwf : S.WellFormed) (h : S.Feasible) :
    S.Level2FractionalFeasible := by
  classical
  obtain ⟨β, hβ, hcov⟩ := h
  refine ⟨fun e P => (if P.1 = β (S.ep e).1 then (1 : ℚ) else 0) *
    (if P.2 = β (S.ep e).2 then (1 : ℚ) else 0), ?_, ?_, ?_, ?_⟩
  · intro e P
    by_cases h1 : P.1 = β (S.ep e).1 <;> by_cases h2 : P.2 = β (S.ep e).2 <;>
      simp [h1, h2]
  · intro e he X Y hne
    have h1 : X = β (S.ep e).1 := by
      by_contra hc; simp [hc] at hne
    have h2 : Y = β (S.ep e).2 := by
      by_contra hc; simp [hc] at hne
    subst h1; subst h2
    exact ⟨hβ _ (hwf e he).1, hβ _ (hwf e he).2, hcov e he⟩
  · intro e he
    have h1 : β (S.ep e).1 ∈ S.L (S.ep e).1 := hβ _ (hwf e he).1
    have h2 : β (S.ep e).2 ∈ S.L (S.ep e).2 := hβ _ (hwf e he).2
    simp [Finset.sum_ite_eq', h1, h2]
  · have key : ∀ e ∈ S.Edges, ∀ u : ℕ, S.Incident e u → ∀ B : Finset E,
        S.margAt (fun e P => (if P.1 = β (S.ep e).1 then (1 : ℚ) else 0) *
          (if P.2 = β (S.ep e).2 then (1 : ℚ) else 0)) e u B
          = (if B = β u then (1 : ℚ) else 0) := by
      intro e he u hu B
      have h1 : β (S.ep e).1 ∈ S.L (S.ep e).1 := hβ _ (hwf e he).1
      have h2 : β (S.ep e).2 ∈ S.L (S.ep e).2 := hβ _ (hwf e he).2
      unfold PortSystem.margAt
      by_cases hc : (S.ep e).1 = u
      · rw [if_pos hc]
        simp only [← Finset.mul_sum, Finset.sum_ite_eq', if_pos h2, mul_one, hc]
      · rw [if_neg hc]
        have hc2 : (S.ep e).2 = u := by
          rcases hu with h | h
          · exact absurd h hc
          · exact h
        simp only [← Finset.sum_mul, Finset.sum_ite_eq', if_pos h1, one_mul, hc2]
    intro u _ e he e' he' hu hu' B _
    rw [key e he u hu B, key e' he' u hu' B]

/-- **`not_feasible_of_not_level2`.**  Level-2 fractional infeasibility is a sound rejection
certificate for integral feasibility.  (The converse is **not** claimed.) -/
theorem not_feasible_of_not_level2 {S : PortSystem E} (hwf : S.WellFormed)
    (h : ¬ S.Level2FractionalFeasible) : ¬ S.Feasible :=
  fun hf => h (level2_of_feasible hwf hf)

end PortSystem

end AnchoredV2
end Erdos287
