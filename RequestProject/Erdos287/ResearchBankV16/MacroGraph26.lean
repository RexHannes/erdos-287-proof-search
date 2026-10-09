import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Coloring

/-!
# Erdős #287 — Research Bank V16 §1: the Route-C macro graph `G(26,7)`

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`G(26,7)` is the circulant graph on `ZMod 26` in which `u ~ v` iff the circular distance of
`u` and `v` is at least `7`.

Kernel-proved (LEAN BANK):
* `adj_translate` — adjacency is translation invariant (definitional: it depends on `u − v`);
* `indep_card_le_seven` — every independent set has at most seven vertices.  The proof is the
  general mathematical one: translate an independent set so that it contains `0`; then every
  element has circular offset in `[-6, 6]`, any two offsets differ by at most `6`, so the offsets
  lie in one seven-point arc (`Finset.Icc lo (lo + 6)`) — no enumeration of subsets;
* `alpha_eq_seven` — `α(G(26,7)) = 7` (the arc `{0,…,6}` is independent);
* `properColouring` — the proper 4-colouring `{0..6}, {7..13}, {14..20}, {21..25}`;
* `occupied_eight_forces_edge` — at least eight occupied macro-groups force an occupied edge;
* `adj_oriented_range` — for adjacent `r, s` with `r < s` (as naturals): `7 ≤ s − r ≤ 19`.
-/

namespace Erdos287
namespace ResearchBankV16
namespace MacroGraph26

/-- Circular distance of `w` from `0` in `ZMod 26`. -/
def d26 (w : ZMod 26) : ℕ := min w.val (26 - w.val)

theorem d26_neg : ∀ w : ZMod 26, d26 (-w) = d26 w := by decide

theorem d26_zero : d26 0 = 0 := by decide

/-- **The Route-C macro graph `G(26,7)`.** -/
def G26 : SimpleGraph (ZMod 26) where
  Adj u v := 7 ≤ d26 (u - v)
  symm := fun u v (h : 7 ≤ d26 (u - v)) => show 7 ≤ d26 (v - u) by
    rw [← neg_sub, d26_neg]; exact h
  loopless := ⟨fun u (h : 7 ≤ d26 (u - u)) => by rw [sub_self, d26_zero] at h; omega⟩

instance : DecidableRel G26.Adj := fun u v => inferInstanceAs (Decidable (7 ≤ d26 (u - v)))

theorem adj_iff (u v : ZMod 26) : G26.Adj u v ↔ 7 ≤ d26 (u - v) := Iff.rfl

/-- Adjacency is translation invariant. -/
theorem adj_translate (u v c : ZMod 26) : G26.Adj (u - c) (v - c) ↔ G26.Adj u v := by
  rw [adj_iff, adj_iff, sub_sub_sub_cancel_right]

/-- An independent set of `G(26,7)`. -/
def IsIndep (S : Finset (ZMod 26)) : Prop := ∀ x ∈ S, ∀ y ∈ S, ¬ G26.Adj x y

/-- Signed circular offset in `[-12, 13]`. -/
def off (w : ZMod 26) : ℤ := if w.val ≤ 13 then (w.val : ℤ) else (w.val : ℤ) - 26

theorem off_injective : Function.Injective off := by
  intro x y h; revert x y; decide

/-- Finite local fact (26 × 26 cases): two vertices non-adjacent to `0` and to each other have
offsets differing by at most `6`. -/
theorem off_close : ∀ x y : ZMod 26, ¬ G26.Adj 0 x → ¬ G26.Adj 0 y → ¬ G26.Adj x y →
    off x - off y ≤ 6 := by decide

/-- Translating an independent set keeps it independent. -/
theorem indep_translate {S : Finset (ZMod 26)} (hS : IsIndep S) (c : ZMod 26) :
    IsIndep (S.image fun x => x - c) := by
  intro x hx y hy
  obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hy
  rw [adj_translate]; exact hS _ hx' _ hy'

/-- An independent set containing `0` has at most seven elements (seven-point arc). -/
theorem indep_card_le_seven_of_zero {T : Finset (ZMod 26)} (hT : IsIndep T) (h0 : (0 : ZMod 26) ∈ T) :
    T.card ≤ 7 := by
  have hne : (T.image off).Nonempty := ⟨off 0, Finset.mem_image_of_mem _ h0⟩
  set lo := (T.image off).min' hne
  have hsub : T.image off ⊆ Finset.Icc lo (lo + 6) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.1 (Finset.min'_mem _ hne)
    refine Finset.mem_Icc.2 ⟨Finset.min'_le _ _ hz, ?_⟩
    have := off_close x y (hT _ h0 _ hx) (hT _ h0 _ hy) (hT _ hx _ hy)
    change off y = lo at hyeq
    omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ off_injective, Int.card_Icc] at hcard
  have : (lo + 6 + 1 - lo).toNat = 7 := by omega
  omega

/-- **`α(G(26,7)) ≤ 7`** (general proof: rotate to contain `0`, then a seven-point arc). -/
theorem indep_card_le_seven (S : Finset (ZMod 26)) (hS : IsIndep S) : S.card ≤ 7 := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
  · simp
  have hinj : Function.Injective fun x : ZMod 26 => x - x0 := sub_left_injective
  have h := indep_card_le_seven_of_zero (indep_translate hS x0)
    (Finset.mem_image.2 ⟨x0, hx0, sub_self x0⟩)
  rwa [Finset.card_image_of_injective _ hinj] at h

/-- The arc `{0,…,6}` is independent. -/
theorem arc_indep : IsIndep {0, 1, 2, 3, 4, 5, 6} := by unfold IsIndep; decide

/-- **`α(G(26,7)) = 7`.** -/
theorem alpha_eq_seven :
    (∃ S : Finset (ZMod 26), IsIndep S ∧ S.card = 7) ∧
      ∀ S : Finset (ZMod 26), IsIndep S → S.card ≤ 7 :=
  ⟨⟨{0, 1, 2, 3, 4, 5, 6}, arc_indep, by decide⟩, indep_card_le_seven⟩

/-- Colour map `r ↦ ⌊r/7⌋`. -/
def col4 (r : ZMod 26) : Fin 4 := ⟨r.val / 7, by have := r.val_lt; omega⟩

theorem col4_classes :
    (Finset.univ.filter fun r : ZMod 26 => col4 r = 0) = {0, 1, 2, 3, 4, 5, 6} ∧
    (Finset.univ.filter fun r : ZMod 26 => col4 r = 1) = {7, 8, 9, 10, 11, 12, 13} ∧
    (Finset.univ.filter fun r : ZMod 26 => col4 r = 2) = {14, 15, 16, 17, 18, 19, 20} ∧
    (Finset.univ.filter fun r : ZMod 26 => col4 r = 3) = {21, 22, 23, 24, 25} := by decide

theorem col4_proper : ∀ r s : ZMod 26, G26.Adj r s → col4 r ≠ col4 s := by decide

/-- **The explicit proper 4-colouring of `G(26,7)`.** -/
def properColouring : G26.Coloring (Fin 4) :=
  SimpleGraph.Coloring.mk col4 fun {r s} h => col4_proper r s h

/-- **Occupancy**: at least eight occupied macro-groups force an occupied macro-edge. -/
theorem occupied_eight_forces_edge (S : Finset (ZMod 26)) (hS : 8 ≤ S.card) :
    ∃ r ∈ S, ∃ s ∈ S, G26.Adj r s := by
  by_contra h
  push_neg at h
  have := indep_card_le_seven S h
  omega

/-- Oriented adjacency range: adjacent groups `r < s` satisfy `7 ≤ s − r ≤ 19`. -/
theorem adj_oriented_range : ∀ r s : ZMod 26, G26.Adj r s → r.val < s.val →
    7 ≤ (s.val : ℤ) - r.val ∧ (s.val : ℤ) - r.val ≤ 19 := by decide

end MacroGraph26
end ResearchBankV16
end Erdos287
