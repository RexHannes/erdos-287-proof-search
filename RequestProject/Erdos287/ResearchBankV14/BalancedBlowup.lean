import RequestProject.Erdos287.ResearchBankV14.BalancedKernelParameters
import RequestProject.Erdos287.ResearchBankV14.MacroGraph11

/-!
# Erdős #287 — Research Bank V14 §A3: the balanced blow-up

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The `K = 2^4170` coordinates `Fin K` are split into 11 cells by `cell i = i mod 11`.

* `cellCount_eq` — for every length `n`, the residue class `r` among `0, …, n−1` has
  `n / 11 + [r < n mod 11]` elements (general, by induction; no enumeration);
* `cells_balanced` — any two cells of `Fin K` differ in size by at most `1`;
  `cellSize_K` — concretely (`K ≡ 1 mod 11`) cell `0` has `⌊K/11⌋ + 1` coordinates, every other
  cell `⌊K/11⌋`;
* `blowup` — the blow-up graph on `Fin K`: `i ~ j` iff their cells are adjacent in `G(11,2)`;
  `no_edge_in_cell` (no edges inside cells) and `blowup_adj_iff` (complete bipartite between
  adjacent macro-cells);
* `blowupColouring` — the 4-colouring of `G(11,2)` lifts to the blow-up.

Everything is symbolic: `Fin K` is only a type, the `2^4170` vertices are never enumerated.
-/

namespace Erdos287
namespace ResearchBankV14
namespace BalancedBlowup

open BalancedKernelParameters MacroGraph11

/-- Number of `i < n` with `i ≡ r (mod 11)`. -/
def cellCount (n r : ℕ) : ℕ := ((Finset.range n).filter fun i => i % 11 = r).card

/-- **Balanced count formula** (general `n`). -/
theorem cellCount_eq (r : ℕ) (hr : r < 11) :
    ∀ n, cellCount n r = n / 11 + if r < n % 11 then 1 else 0 := by
  intro n
  induction n with
  | zero => simp [cellCount]
  | succ n ih =>
    have hstep : cellCount (n + 1) r = cellCount n r + if n % 11 = r then 1 else 0 := by
      unfold cellCount
      rw [Finset.range_add_one, Finset.filter_insert]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (by simp)]
      · rfl
    rw [hstep, ih]
    split_ifs <;> omega

/-- The cell of a coordinate. -/
def cell (i : Fin K) : Fin 11 := ⟨i.val % 11, Nat.mod_lt _ (by norm_num)⟩

/-- Size of cell `r` in `Fin K`. -/
def cellSize (r : Fin 11) : ℕ := (Finset.univ.filter fun i : Fin K => cell i = r).card

theorem cellSize_eq_count (r : Fin 11) : cellSize r = cellCount K r.val := by
  unfold cellSize cellCount
  have hmap : (Finset.univ.filter fun i : Fin K => cell i = r).map Fin.valEmbedding =
      (Finset.range K).filter fun i => i % 11 = r.val := by
    ext i
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_range, cell]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j.isLt, by rw [← hj]⟩
    · rintro ⟨hi, hr⟩
      exact ⟨⟨i, hi⟩, Fin.ext hr, rfl⟩
  rw [← hmap, Finset.card_map]

/-- **Concrete cell sizes** (`K ≡ 1 mod 11`). -/
theorem cellSize_K (r : Fin 11) : cellSize r = K / 11 + if r.val = 0 then 1 else 0 := by
  rw [cellSize_eq_count, cellCount_eq r.val r.isLt, K_mod_11]
  congr 1
  split_ifs <;> omega

/-- **The partition is balanced.** -/
theorem cells_balanced (r s : Fin 11) : cellSize r ≤ cellSize s + 1 := by
  rw [cellSize_K, cellSize_K]; split_ifs <;> omega

theorem cellSize_sum : ∑ r : Fin 11, cellSize r = K := by
  simp only [cellSize_K, Finset.sum_add_distrib]
  have h := Nat.div_add_mod K 11
  rw [K_mod_11] at h
  simp
  omega

/-- **The blow-up graph** on the `K` coordinates. -/
def blowup : SimpleGraph (Fin K) := G11.comap cell

instance : DecidableRel blowup.Adj := fun i j =>
  inferInstanceAs (Decidable (G11.Adj (cell i) (cell j)))

/-- Complete bipartite between adjacent macro-cells (and nothing else). -/
theorem blowup_adj_iff (i j : Fin K) : blowup.Adj i j ↔ G11.Adj (cell i) (cell j) := Iff.rfl

/-- **No edges inside cells.** -/
theorem no_edge_in_cell {i j : Fin K} (h : cell i = cell j) : ¬ blowup.Adj i j := by
  rw [blowup_adj_iff, h]; exact G11.loopless.irrefl _

/-- **The 4-colouring lifts to the blow-up.** -/
def blowupColouring : blowup.Coloring (Fin 4) :=
  SimpleGraph.Coloring.mk (fun i => col4 (cell i)) fun {_ _} h => col4_proper _ _ h

theorem blowupColouring_apply (i : Fin K) : blowupColouring i = col4 (cell i) := rfl

end BalancedBlowup
end ResearchBankV14
end Erdos287
