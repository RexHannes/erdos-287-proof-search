import RequestProject.Erdos287.ResearchBankV9.CircularGraph

/-!
# Erdős #287 — Research Bank V9 §3D: graph-selective occupancy

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Finite combinatorial theorem (kernel-proved, `occupancy_forces_edge`): if each graph vertex
receives at most `m` cells, every independent set has at most `r + 1` vertices, and at least
`(r + 1) m + 1` cells are occupied, then two occupied cells sit on adjacent vertices.

Programme parameterization (`occupancy_programme`): with `a = (r + 1) m` and
`Q = ⌈A a⌉ + 1` placed cells (`A ≥ 1`), if at most `Q − (a + 1)` cells are lost, the surviving
`a + 1` cells force a useful edge.  Specialization to the circular graph `G(n, r)`, `n > 3r`:
`circular_occupancy`.
-/

open scoped BigOperators

namespace Erdos287
namespace ResearchBankV9
namespace Occupancy

/-- **Graph-selective occupancy.** -/
theorem occupancy_forces_edge {V κ : Type*} [DecidableEq V] (Adj : V → V → Prop)
    (r m : ℕ) (hα : ∀ S : Finset V, (∀ x ∈ S, ∀ y ∈ S, ¬ Adj x y) → S.card ≤ r + 1)
    (cells : Finset κ) (f : κ → V) (hm : ∀ v, (cells.filter fun c => f c = v).card ≤ m)
    (hcells : (r + 1) * m + 1 ≤ cells.card) :
    ∃ c₁ ∈ cells, ∃ c₂ ∈ cells, Adj (f c₁) (f c₂) := by
  by_contra hno
  push_neg at hno
  have hind : ∀ x ∈ cells.image f, ∀ y ∈ cells.image f, ¬ Adj x y := by
    simp only [Finset.mem_image]
    rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩
    exact hno c₁ hc₁ c₂ hc₂
  have hT := hα _ hind
  have hsum : cells.card ≤ (cells.image f).card * m := by
    rw [Finset.card_eq_sum_card_image f cells]
    calc ∑ v ∈ cells.image f, (cells.filter fun c => f c = v).card
        ≤ ∑ _v ∈ cells.image f, m := Finset.sum_le_sum fun v _ => hm v
      _ = (cells.image f).card * m := by simp
  have : (cells.image f).card * m ≤ (r + 1) * m := Nat.mul_le_mul_right m hT
  omega

/-- **Programme parameterization.**  With `a = (r + 1) m` and `Q = ⌈A a⌉ + 1` placed cells
(`A ≥ 1`), losing at most `Q − (a + 1)` cells still forces a useful edge. -/
theorem occupancy_programme {V κ : Type*} [DecidableEq V] (Adj : V → V → Prop)
    (r m : ℕ) (hα : ∀ S : Finset V, (∀ x ∈ S, ∀ y ∈ S, ¬ Adj x y) → S.card ≤ r + 1)
    (A : ℚ) (hA : 1 ≤ A) (placed survivors : Finset κ) (hsub : survivors ⊆ placed)
    (hQ : placed.card = ⌈A * ((r + 1) * m : ℕ)⌉.toNat + 1)
    (hloss : placed.card - survivors.card ≤ placed.card - ((r + 1) * m + 1))
    (f : κ → V) (hm : ∀ v, (survivors.filter fun c => f c = v).card ≤ m) :
    ∃ c₁ ∈ survivors, ∃ c₂ ∈ survivors, Adj (f c₁) (f c₂) := by
  have hQa : (r + 1) * m + 1 ≤ placed.card := by
    rw [hQ]
    generalize (r + 1) * m = N
    have h0 : (0 : ℚ) ≤ N := by positivity
    have h1 : (N : ℚ) ≤ A * N := by nlinarith
    have h3 : ((N : ℤ) : ℚ) ≤ ⌈A * (N : ℚ)⌉ := by
      have := Int.le_ceil (A * (N : ℚ)); push_cast; linarith
    have h2 : (N : ℤ) ≤ ⌈A * (N : ℚ)⌉ := by exact_mod_cast h3
    omega
  have hsc := Finset.card_le_card hsub
  exact occupancy_forces_edge Adj r m hα survivors f hm (by omega)

/-- **Occupancy on the circular annulus graph `G(n, r)`** (`n > 3r`): `(r+1) m + 1` cells on
vertices of `[0, n)`, at most `m` per vertex, force two cells at circular distance `≥ r + 1`. -/
theorem circular_occupancy {n : ℤ} {r m : ℕ} (hn : 3 * (r : ℤ) < n) {κ : Type*}
    (cells : Finset κ) (f : κ → ℤ) (hf : ∀ c ∈ cells, f c ∈ CircularGraph.V n)
    (hm : ∀ v, (cells.filter fun c => f c = v).card ≤ m)
    (hcells : (r + 1) * m + 1 ≤ cells.card) :
    ∃ c₁ ∈ cells, ∃ c₂ ∈ cells, CircularGraph.Adj n r (f c₁) (f c₂) := by
  classical
  -- restrict the graph to the vertex set `[0, n)` via the relation `Adj'`
  let Adj' : ℤ → ℤ → Prop := fun x y =>
    x ∉ CircularGraph.V n ∨ y ∉ CircularGraph.V n ∨ CircularGraph.Adj n r x y
  have hα : ∀ S : Finset ℤ, (∀ x ∈ S, ∀ y ∈ S, ¬ Adj' x y) → S.card ≤ r + 1 := by
    intro S hS
    have hsub : S ⊆ CircularGraph.V n := by
      intro x hx
      have := hS x hx x hx
      simp only [Adj', not_or, not_not] at this
      exact this.1
    have hind : CircularGraph.Indep n r S := by
      refine ⟨hsub, fun s hs t ht => ?_⟩
      have := hS s hs t ht
      simp only [Adj', not_or] at this
      exact (CircularGraph.near_iff (by omega) (by positivity) (by omega) s t).1 this.2.2
    have := CircularGraph.indep_card_le (by positivity) hn hind
    omega
  obtain ⟨c₁, h₁, c₂, h₂, hadj⟩ := occupancy_forces_edge Adj' r m hα cells f hm hcells
  refine ⟨c₁, h₁, c₂, h₂, ?_⟩
  rcases hadj with h | h | h
  · exact absurd (hf c₁ h₁) h
  · exact absurd (hf c₂ h₂) h
  · exact h

end Occupancy
end ResearchBankV9
end Erdos287
