import Mathlib

/-!
# Erdős #287 — Research Bank V26 §4.5: product interval boxing

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Dyadicization alone does NOT remove the product constraint `x < m₁⋯m_k ≤ 2x`.  We use
multiplicative boxes of ratio `1 + h` (`h = log^{-B} x`):
`B = ∏_i [L_i, L_i(1+h))`.  A box is INTERIOR if `x < ∏ L_i` and `∏ L_i (1+h)^k ≤ 2x`,
EXTERIOR if `∏ L_i (1+h)^k ≤ x` or `2x < ∏ L_i`, and BOUNDARY otherwise.

**LEAN BANK.**
* `interior_rectangular` — on an interior box the product cutoff is identically `1`, so the
  constraint is RECTANGULAR there;
* `exterior_zero` — on an exterior box it is identically `0`;
* `box_decomposition` — exact decomposition of the cut sum into interior rectangular sums plus
  ONE sum over the UNION of boundary boxes.

**EXTERNAL PROVIDER.**
* `ProductBoundaryProvider` — the analytic boundary estimate
  `O(x √h log^C x + x^{1/2} log^C x)` for the union of boundary products.

**LEAN CONDITIONAL.**
* `product_boxing_conditional` — the cut sum equals the interior rectangular sums up to the
  provider bound, applied ONCE (no factor `#boxes`).
* `boundary_bound_not_multiplied` (regression) — multiplying by the number of boxes would give a
  strictly larger bound as soon as there are two boundary boxes.
-/

namespace Erdos287
namespace ResearchBankV26
namespace ProductIntervalBoxes

open Finset

variable {k : ℕ}

/-- A multiplicative box of ratio `1 + h` with lower corner `L`. -/
structure MulBox (k : ℕ) where
  lower : Fin k → ℝ
  pos : ∀ i, 0 < lower i

/-- Membership in the half-open box `∏ [L_i, L_i (1+h))`. -/
def MulBox.Mem (B : MulBox k) (h : ℝ) (m : Fin k → ℝ) : Prop :=
  ∀ i, B.lower i ≤ m i ∧ m i < B.lower i * (1 + h)

/-- The product cutoff `1_{x < ∏ m_i ≤ 2x}`. -/
noncomputable def productCut (x : ℝ) (m : Fin k → ℝ) : ℝ :=
  if x < ∏ i, m i ∧ ∏ i, m i ≤ 2 * x then 1 else 0

def Interior (B : MulBox k) (h x : ℝ) : Prop :=
  x < ∏ i, B.lower i ∧ (∏ i, B.lower i) * (1 + h) ^ k ≤ 2 * x

def Exterior (B : MulBox k) (h x : ℝ) : Prop :=
  (∏ i, B.lower i) * (1 + h) ^ k ≤ x ∨ 2 * x < ∏ i, B.lower i

theorem prod_bounds (B : MulBox k) {h : ℝ} {m : Fin k → ℝ} (hm : B.Mem h m) :
    ∏ i, B.lower i ≤ ∏ i, m i ∧ ∏ i, m i ≤ (∏ i, B.lower i) * (1 + h) ^ k := by
  constructor
  · exact Finset.prod_le_prod (fun i _ => (B.pos i).le) fun i _ => (hm i).1
  · calc ∏ i, m i ≤ ∏ i, B.lower i * (1 + h) :=
          Finset.prod_le_prod (fun i _ => (B.pos i).le.trans (hm i).1) fun i _ => (hm i).2.le
      _ = (∏ i, B.lower i) * (1 + h) ^ k := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Interior boxes are rectangular** (LEAN BANK). -/
theorem interior_rectangular (B : MulBox k) {h x : ℝ} (hB : Interior B h x) {m : Fin k → ℝ}
    (hm : B.Mem h m) : productCut x m = 1 := by
  obtain ⟨h1, h2⟩ := prod_bounds B hm
  unfold productCut
  rw [if_pos ⟨lt_of_lt_of_le hB.1 h1, h2.trans hB.2⟩]

/-- **Exterior boxes contribute nothing** (LEAN BANK). -/
theorem exterior_zero (B : MulBox k) {h x : ℝ} (hB : Exterior B h x) {m : Fin k → ℝ}
    (hm : B.Mem h m) : productCut x m = 0 := by
  obtain ⟨h1, h2⟩ := prod_bounds B hm
  unfold productCut
  rw [if_neg]
  rintro ⟨hx1, hx2⟩
  rcases hB with hB | hB
  · linarith
  · linarith

/-- Boxing data at one scale: tuples `S`, coefficient `c`, box assignment and classification
(`0` interior, `1` exterior, `2` boundary). -/
structure BoxingData (k : ℕ) (ι : Type) [DecidableEq ι] where
  h : ℝ
  x : ℝ
  S : Finset (Fin k → ℝ)
  c : (Fin k → ℝ) → ℝ
  box : ι → MulBox k
  boxOf : (Fin k → ℝ) → ι
  mem : ∀ m ∈ S, (box (boxOf m)).Mem h m
  cls : ι → Fin 3
  hint : ∀ i, cls i = 0 → Interior (box i) h x
  hext : ∀ i, cls i = 1 → Exterior (box i) h x

variable {ι : Type} [DecidableEq ι]

/-- The cut sum `Σ_{m ∈ S} c(m) 1_{x < ∏ m ≤ 2x}`. -/
noncomputable def BoxingData.cutSum (D : BoxingData k ι) : ℝ :=
  ∑ m ∈ D.S, D.c m * productCut D.x m

/-- The interior rectangular sums `Σ_{interior B} Σ_{m ∈ B} c(m)` (no cutoff). -/
noncomputable def BoxingData.interiorSum (D : BoxingData k ι) : ℝ :=
  ∑ i ∈ (D.S.image D.boxOf).filter (fun i => D.cls i = 0),
    ∑ m ∈ D.S.filter (fun m => D.boxOf m = i), D.c m

/-- The ONE sum over the union of boundary boxes. -/
noncomputable def BoxingData.boundarySum (D : BoxingData k ι) : ℝ :=
  ∑ m ∈ D.S.filter (fun m => D.cls (D.boxOf m) = 2), D.c m * productCut D.x m

/-- **Exact box decomposition** (LEAN BANK). -/
theorem box_decomposition (D : BoxingData k ι) : D.cutSum = D.interiorSum + D.boundarySum := by
  classical
  unfold BoxingData.cutSum BoxingData.interiorSum BoxingData.boundarySum
  have hsplit : ∀ m ∈ D.S, D.c m * productCut D.x m =
      (if D.cls (D.boxOf m) = 0 then D.c m else 0) +
        (if D.cls (D.boxOf m) = 2 then D.c m * productCut D.x m else 0) := by
    intro m hm
    have hm' := D.mem m hm
    rcases (show ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 by decide) (D.cls (D.boxOf m)) with
      h0 | h1 | h2
    · rw [if_pos h0, if_neg (by rw [h0]; decide), interior_rectangular _ (D.hint _ h0) hm']
      ring
    · rw [if_neg (by rw [h1]; decide), if_neg (by rw [h1]; decide),
        exterior_zero _ (D.hext _ h1) hm']
      ring
    · rw [if_neg (by rw [h2]; decide), if_pos h2]; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  rw [Finset.sum_filter]
  rw [← Finset.sum_fiberwise_of_maps_to (s := D.S) (t := D.S.image D.boxOf) (g := D.boxOf)
    (fun m hm => Finset.mem_image_of_mem _ hm)]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [(Finset.mem_filter.1 hm).2, if_pos hi]
  · refine Finset.sum_eq_zero fun m hm => ?_
    rw [(Finset.mem_filter.1 hm).2, if_neg hi]

/-- **Product-boundary provider** (EXTERNAL PROVIDER; never constructed): the union of boundary
products is estimated ONCE. -/
structure ProductBoundaryProvider (D : ℝ → BoxingData k ι) (C : ℝ) : Prop where
  bound : ∃ x0 : ℝ, ∀ x ≥ x0,
    |(D x).boundarySum| ≤ (D x).x * Real.sqrt (D x).h * Real.log (D x).x ^ C +
      Real.sqrt (D x).x * Real.log (D x).x ^ C

/-- **Product boxing** (LEAN CONDITIONAL on `ProductBoundaryProvider`). -/
theorem product_boxing_conditional {D : ℝ → BoxingData k ι} {C : ℝ}
    (P : ProductBoundaryProvider D C) :
    ∃ x0 : ℝ, ∀ x ≥ x0, |(D x).cutSum - (D x).interiorSum| ≤
      (D x).x * Real.sqrt (D x).h * Real.log (D x).x ^ C +
        Real.sqrt (D x).x * Real.log (D x).x ^ C := by
  obtain ⟨x0, hx0⟩ := P.bound
  refine ⟨x0, fun x hx => ?_⟩
  rw [box_decomposition, add_sub_cancel_left]
  exact hx0 x hx

/-- **Regression: the boundary error must not be multiplied by the number of boxes.**  With two
or more boundary boxes and a positive error the multiplied bound is strictly larger. -/
theorem boundary_bound_not_multiplied {E : ℝ} (hE : 0 < E) {nb : ℕ} (hnb : 2 ≤ nb) :
    E < (nb : ℝ) * E := by
  have : (2 : ℝ) ≤ nb := by exact_mod_cast hnb
  nlinarith

end ProductIntervalBoxes
end ResearchBankV26
end Erdos287
