import RequestProject.Erdos287.Anchored.CycleRank

/-!
# Anchored V2 — port systems and the weighted capacity function

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

A **port system** is the finite combinatorial abstraction of an arithmetic block structure:

* a finite set of *blocks* (arithmetic layers) `Blocks`;
* a finite set of *contact edges* `Edges`, each with an ordered pair of endpoint blocks `ep e`;
* for every block `v` a finite *complete local relation* `L v`, a finite set of admissible
  sets of incident edges that the block *covers* (`β_{v,e} = 1` iff `e ∈ B` for the chosen
  `B ∈ L v`).

A port system is **feasible** when there is a global choice `β v ∈ L v` for every block such
that every contact edge is covered by at least one of its endpoints (the OR edge condition).

For nonnegative edge weights `λ` the **capacity** of a block is

`C_v(λ) = max_{B ∈ L v} ∑_{e ∈ B} λ e`

(`0` when the local relation is empty).  This file proves the capacity is monotone under
shrinkage of local relations, and the elementary sound inequality

`Feasible → ∑_e λ e ≤ ∑_v C_v(λ)`.

No LP duality and no converse is used or claimed.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV2

/-- A finite port system: blocks, contact edges with endpoint blocks, and the complete finite
local relation of each block. -/
structure PortSystem (E : Type*) where
  /-- the arithmetic blocks -/
  Blocks : Finset ℕ
  /-- the contact edges -/
  Edges : Finset E
  /-- the two endpoint blocks of a contact edge -/
  ep : E → ℕ × ℕ
  /-- the complete finite local relation of each block -/
  L : ℕ → Finset (Finset E)

namespace PortSystem

variable {E : Type*}

/-- Every contact edge has both endpoints among the blocks. -/
def WellFormed (S : PortSystem E) : Prop :=
  ∀ e ∈ S.Edges, (S.ep e).1 ∈ S.Blocks ∧ (S.ep e).2 ∈ S.Blocks

/-- **Integral feasibility**: a global choice of one admissible local state per block covering
every contact edge. -/
def Feasible (S : PortSystem E) : Prop :=
  ∃ β : ℕ → Finset E, (∀ v ∈ S.Blocks, β v ∈ S.L v) ∧
    ∀ e ∈ S.Edges, e ∈ β (S.ep e).1 ∨ e ∈ β (S.ep e).2

/-- The weighted capacity of a block: the maximum weight of a coverable port set. -/
def cap (S : PortSystem E) (lam : E → ℚ) (v : ℕ) : ℚ :=
  if h : (S.L v).Nonempty then (S.L v).sup' h (fun B => ∑ e ∈ B, lam e) else 0

theorem cap_eq_sup' (S : PortSystem E) (lam : E → ℚ) {v : ℕ} (h : (S.L v).Nonempty) :
    S.cap lam v = (S.L v).sup' h (fun B => ∑ e ∈ B, lam e) := by
  unfold cap
  exact dif_pos h

theorem cap_eq_zero (S : PortSystem E) (lam : E → ℚ) {v : ℕ} (h : ¬ (S.L v).Nonempty) :
    S.cap lam v = 0 := by
  unfold cap
  exact dif_neg h

theorem cap_of_empty (S : PortSystem E) (lam : E → ℚ) {v : ℕ} (h : S.L v = ∅) :
    S.cap lam v = 0 := by
  have hne : ¬ (S.L v).Nonempty := by rw [h]; exact Finset.not_nonempty_empty
  exact S.cap_eq_zero lam hne

/-- Every admissible local state has weight at most the capacity. -/
theorem le_cap (S : PortSystem E) (lam : E → ℚ) {v : ℕ} {B : Finset E} (hB : B ∈ S.L v) :
    ∑ e ∈ B, lam e ≤ S.cap lam v := by
  have hne : (S.L v).Nonempty := ⟨B, hB⟩
  rw [S.cap_eq_sup' lam hne]
  exact Finset.le_sup' (f := fun B => ∑ e ∈ B, lam e) hB

/-- With nonnegative weights the capacity is nonnegative. -/
theorem cap_nonneg (S : PortSystem E) {lam : E → ℚ} (hlam : ∀ e, 0 ≤ lam e) (v : ℕ) :
    0 ≤ S.cap lam v := by
  by_cases h : (S.L v).Nonempty
  · obtain ⟨B, hB⟩ := h
    exact le_trans (Finset.sum_nonneg fun e _ => hlam e) (S.le_cap lam hB)
  · rw [S.cap_eq_zero lam h]

/-- **`cap_mono`.**  `KERNEL-PROVED`.  Shrinking the local relation cannot increase the
capacity (nonnegative weights). -/
theorem cap_mono {S S' : PortSystem E} {lam : E → ℚ} (hlam : ∀ e, 0 ≤ lam e) {v : ℕ}
    (hsub : S'.L v ⊆ S.L v) : S'.cap lam v ≤ S.cap lam v := by
  by_cases h : (S'.L v).Nonempty
  · rw [S'.cap_eq_sup' lam h]
    refine Finset.sup'_le h _ ?_
    intro B hB
    exact S.le_cap lam (hsub hB)
  · rw [S'.cap_eq_zero lam h]
    exact S.cap_nonneg hlam v

/-- **`capacity_sound`.**  `KERNEL-PROVED`.  The elementary weighted capacity inequality: if a
port system is feasible then for every nonnegative edge weighting the total edge weight is at
most the total block capacity. -/
theorem capacity_sound {S : PortSystem E} (hwf : S.WellFormed) (hfeas : S.Feasible)
    {lam : E → ℚ} (hlam : ∀ e, 0 ≤ lam e) :
    ∑ e ∈ S.Edges, lam e ≤ ∑ v ∈ S.Blocks, S.cap lam v := by
  classical
  obtain ⟨β, hβ, hcov⟩ := hfeas
  have step1 : ∑ e ∈ S.Edges, lam e
      ≤ ∑ v ∈ S.Blocks, ∑ e ∈ S.Edges, (if e ∈ β v then lam e else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum ?_
    intro e he
    obtain ⟨h1, h2⟩ := hwf e he
    rcases hcov e he with hc | hc
    · refine le_trans ?_ (Finset.single_le_sum
        (f := fun v => if e ∈ β v then lam e else 0) (fun v _ => ?_) h1)
      · simp [hc]
      · by_cases hh : e ∈ β v <;> simp [hh, hlam e]
    · refine le_trans ?_ (Finset.single_le_sum
        (f := fun v => if e ∈ β v then lam e else 0) (fun v _ => ?_) h2)
      · simp [hc]
      · by_cases hh : e ∈ β v <;> simp [hh, hlam e]
  refine le_trans step1 (Finset.sum_le_sum ?_)
  intro v hv
  refine le_trans ?_ (S.le_cap lam (hβ v hv))
  rw [← Finset.sum_filter]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun e _ _ => hlam e)
  intro e he
  exact (Finset.mem_filter.1 he).2

end PortSystem

end AnchoredV2
end Erdos287
