import RequestProject.Erdos287.ResearchBankV16.RouteCParameters
import RequestProject.Erdos287.ResearchBankV16.MacroGraph26

/-!
# Erdős #287 — Research Bank V16 §1: the symbolic balanced blow-up of `G(26,7)`

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The `K = 2^82650` coordinates `Fin K` are split into 26 macro-groups by `group i = i mod 26`.

Kernel-proved (LEAN BANK), entirely symbolic (`Fin K` is only a type; no coordinate is ever
enumerated):
* `groupCount_eq` — for every `n`, the residue class `r` among `0,…,n−1` has
  `n / 26 + [r < n mod 26]` elements (general induction);
* `groupSize_K` — since `K ≡ 12 (mod 26)`, groups `0,…,11` have `⌊K/26⌋ + 1` coordinates and
  groups `12,…,25` have `⌊K/26⌋`;
* `groups_balanced` — any two groups differ in size by at most one; `groupSize_sum` — they
  partition `Fin K`;
* `blowup`, `blowup_adj_iff`, `no_edge_in_group` — complete bipartite between adjacent groups,
  nothing inside a group;
* `blowupColouring` — the 4-colouring lifts;
* `blowup_occupied_eight_forces_edge` — a set of coordinates meeting at least eight groups
  contains a blow-up edge.
-/

namespace Erdos287
namespace ResearchBankV16
namespace BalancedBlowup26

open RouteCParameters MacroGraph26

/-- Number of `i < n` with `i ≡ r (mod 26)`. -/
def groupCount (n r : ℕ) : ℕ := ((Finset.range n).filter fun i => i % 26 = r).card

/-- **Balanced count formula** (general `n`). -/
theorem groupCount_eq (r : ℕ) (hr : r < 26) :
    ∀ n, groupCount n r = n / 26 + if r < n % 26 then 1 else 0 := by
  intro n
  induction n with
  | zero => simp [groupCount]
  | succ n ih =>
    have hstep : groupCount (n + 1) r = groupCount n r + if n % 26 = r then 1 else 0 := by
      unfold groupCount
      rw [Finset.range_add_one, Finset.filter_insert]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (by simp)]
      · rfl
    rw [hstep, ih]
    split_ifs <;> omega

/-- The macro-group of a coordinate. -/
def group (i : Fin K) : ZMod 26 := (i.val : ZMod 26)

theorem group_val (i : Fin K) : (group i).val = i.val % 26 := by
  unfold group; rw [ZMod.val_natCast]

/-- Size of group `r`. -/
def groupSize (r : ZMod 26) : ℕ := (Finset.univ.filter fun i : Fin K => group i = r).card

theorem groupSize_eq_count (r : ZMod 26) : groupSize r = groupCount K r.val := by
  unfold groupSize groupCount
  have hmap : (Finset.univ.filter fun i : Fin K => group i = r).map Fin.valEmbedding =
      (Finset.range K).filter fun i => i % 26 = r.val := by
    ext i
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j.isLt, by rw [← group_val, hj]⟩
    · rintro ⟨hi, hr⟩
      refine ⟨⟨i, hi⟩, ?_, rfl⟩
      apply ZMod.val_injective
      rw [group_val]; exact hr
  rw [← hmap, Finset.card_map]

/-- **Concrete group sizes** (`K ≡ 12 mod 26`). -/
theorem groupSize_K (r : ZMod 26) : groupSize r = K / 26 + if r.val < 12 then 1 else 0 := by
  rw [groupSize_eq_count, groupCount_eq r.val (ZMod.val_lt r), K_mod_26]

/-- **The partition is balanced.** -/
theorem groups_balanced (r s : ZMod 26) : groupSize r ≤ groupSize s + 1 := by
  rw [groupSize_K, groupSize_K]; split_ifs <;> omega

theorem card_small_groups :
    (Finset.univ.filter fun r : ZMod 26 => r.val < 12).card = 12 := by decide

theorem groupSize_sum : ∑ r : ZMod 26, groupSize r = K := by
  simp only [groupSize_K, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    ZMod.card, smul_eq_mul]
  rw [← Finset.sum_filter, Finset.sum_const, card_small_groups, smul_eq_mul]
  have h := Nat.div_add_mod K 26
  rw [K_mod_26] at h
  omega

/-- **The blow-up graph** on the `K` coordinates. -/
def blowup : SimpleGraph (Fin K) := G26.comap group

instance : DecidableRel blowup.Adj := fun i j =>
  inferInstanceAs (Decidable (G26.Adj (group i) (group j)))

theorem blowup_adj_iff (i j : Fin K) : blowup.Adj i j ↔ G26.Adj (group i) (group j) := Iff.rfl

/-- **No edges inside a group.** -/
theorem no_edge_in_group {i j : Fin K} (h : group i = group j) : ¬ blowup.Adj i j := by
  rw [blowup_adj_iff, h]; exact G26.loopless.irrefl _

/-- **The 4-colouring lifts to the blow-up.** -/
def blowupColouring : blowup.Coloring (Fin 4) :=
  SimpleGraph.Coloring.mk (fun i => col4 (group i)) fun {_ _} h => col4_proper _ _ h

/-- A coordinate set meeting at least eight groups contains a blow-up edge. -/
theorem blowup_occupied_eight_forces_edge (T : Finset (Fin K)) (hT : 8 ≤ (T.image group).card) :
    ∃ i ∈ T, ∃ j ∈ T, blowup.Adj i j := by
  obtain ⟨r, hr, s, hs, hrs⟩ := occupied_eight_forces_edge _ hT
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hr
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hs
  exact ⟨i, hi, j, hj, hrs⟩

end BalancedBlowup26
end ResearchBankV16
end Erdos287
