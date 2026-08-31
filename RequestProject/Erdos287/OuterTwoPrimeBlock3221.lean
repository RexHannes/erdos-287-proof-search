import Mathlib
import RequestProject.Erdos287.BalancedSeven3221Grouping
import RequestProject.Erdos287.PhysicalLogBudget3221

/-!
# V21, Phase 9 — prime-density ownership and the outer two-prime block

`3221-OUTER-TWOPRIME-L2-45 : ALGEBRAIC PASS + EXTERNAL DENSITY INPUT (UNINHABITED)`

## §1.  No prime-density double spending

The seven physical prime labels are partitioned once and for all between the **outer**
two-prime block and the **inner** five-box transform, using the repository's own
`1 + 2 + 2 + 2` grouping (`Erdos287.Grouping3221.blockE/blockM/blockN/blockL`):

```
OuterBoxes = blockM = {1,2}          InnerBoxes = blockE ∪ blockN ∪ blockL = {0,3,4,5,6}
```

`outerInnerBox_disjoint`, `outerInnerBox_cover`, `sevenBox_partition_cardinality` and
`primeDensity_no_double_spending` are finite `decide` facts: no `Y/log Y` density can be
charged twice.  A **parametric** version (`parametricOwnership_*`) is provided as well, so
that a different physical assignment can be plugged in without re-deriving the firewall.

## §2.  The outer two-prime coefficient

`alphaOuter` is the literal labelled convolution `α(m) = ∑_{p_i p_j = m} ω_i(p_i) ω_j(p_j)`,
with the labelled (not unlabelled) convention made explicit: `alphaOuter_labelled_swap`
records the label symmetry, and the representation multiplicity is handled by the exact
`L¹` bound `alphaOuter_l1_le` (each labelled pair contributes to exactly one `m`).

`outerL2_of_sup_and_l1` is the Lean-proved `L²`-from-`L^∞`-and-`L¹` step;
`OuterTwoPrimeL2Normalization3221Input` is the *external* prime-density interface
`∑_m |α(m)|² ≤ C · M / log² X`, which is **not inhabited** and, in particular, is not
derived from the abstract factorial polarisation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators

namespace Erdos287
namespace V21Outer

open Erdos287.Grouping3221

/-! ## §1. Ownership of the seven prime labels -/

/-- The outer two-prime block labels (the physical `blockM`). -/
def outerBoxes : Finset (Fin 7) := blockM

/-- The inner five-box labels. -/
def innerBoxes : Finset (Fin 7) := blockE ∪ blockN ∪ blockL

theorem outerBoxes_eq : outerBoxes = ({1, 2} : Finset (Fin 7)) := rfl

theorem innerBoxes_eq : innerBoxes = ({0, 3, 4, 5, 6} : Finset (Fin 7)) := by decide

/-- **`outerInnerBox_disjoint`.**  `LEAN_PROVED_FINITE`. -/
theorem outerInnerBox_disjoint : Disjoint outerBoxes innerBoxes := by decide

/-- **`outerInnerBox_cover`.**  `LEAN_PROVED_FINITE`. -/
theorem outerInnerBox_cover : outerBoxes ∪ innerBoxes = Finset.univ := by decide

/-- **`sevenBox_partition_cardinality`.**  `LEAN_PROVED_FINITE`.  `2 + 5 = 7`. -/
theorem sevenBox_partition_cardinality :
    outerBoxes.card = 2 ∧ innerBoxes.card = 5 ∧ outerBoxes.card + innerBoxes.card = 7 := by
  decide

/-- **`primeDensity_no_double_spending`.**  `LEAN_PROVED_FINITE`.

Every one of the seven physical prime labels is charged to exactly one side. -/
theorem primeDensity_no_double_spending (i : Fin 7) :
    (i ∈ outerBoxes ∧ i ∉ innerBoxes) ∨ (i ∈ innerBoxes ∧ i ∉ outerBoxes) := by
  revert i; decide

/-! ### Parametric ownership (for a different physical assignment) -/

/-- The parametric firewall: for any outer selection, the complementary inner selection is
disjoint from it, covers the seven labels, and has complementary cardinality. -/
theorem parametricOwnership (Outer : Finset (Fin 7)) :
    Disjoint Outer (Finset.univ \ Outer) ∧
      Outer ∪ (Finset.univ \ Outer) = Finset.univ ∧
      Outer.card + (Finset.univ \ Outer).card = 7 := by
  refine ⟨Finset.disjoint_sdiff, ?_, ?_⟩
  · rw [Finset.union_sdiff_self_eq_union, Finset.union_eq_right.mpr (Finset.subset_univ _)]
  · have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ Outer)
    rw [Finset.card_univ, Fintype.card_fin] at h
    omega

/-! ## §2. The outer two-prime coefficient -/

variable {P1 P2 : Finset ℕ} {w1 w2 : ℕ → ℂ}

/-- The literal labelled outer coefficient `α(m) = ∑_{p_i p_j = m} ω_i(p_i) ω_j(p_j)`. -/
noncomputable def alphaOuter (P1 P2 : Finset ℕ) (w1 w2 : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ p ∈ P1, ∑ r ∈ P2, if p * r = m then w1 p * w2 r else 0

/-- **`alphaOuter_labelled_swap`.**  `LEAN_PROVED`.

The labelling convention is explicit: swapping the two labels swaps the boxes and the
weights.  (In particular the `p_i = p_j` terms are *not* silently halved.) -/
theorem alphaOuter_labelled_swap (P1 P2 : Finset ℕ) (w1 w2 : ℕ → ℂ) (m : ℕ) :
    alphaOuter P1 P2 w1 w2 m = alphaOuter P2 P1 w2 w1 m := by
  rw [alphaOuter, alphaOuter, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun p _ => ?_
  by_cases h : p * r = m
  · rw [if_pos h, if_pos (by rw [mul_comm]; exact h), mul_comm]
  · rw [if_neg h, if_neg (by rw [mul_comm]; exact h)]

/-- **`alphaOuter_l1_le`.**  `LEAN_PROVED_FINITE`.

Exact representation multiplicity: each labelled pair `(p, r)` contributes to exactly one
`m`, so the `L¹` mass of `α` is at most the product of the two box `L¹` masses. -/
theorem alphaOuter_l1_le (P1 P2 Mbox : Finset ℕ) (w1 w2 : ℕ → ℂ) :
    ∑ m ∈ Mbox, ‖alphaOuter P1 P2 w1 w2 m‖
      ≤ (∑ p ∈ P1, ‖w1 p‖) * ∑ r ∈ P2, ‖w2 r‖ := by
  classical
  have hpt : ∀ m ∈ Mbox, ‖alphaOuter P1 P2 w1 w2 m‖
      ≤ ∑ p ∈ P1, ∑ r ∈ P2, (if p * r = m then ‖w1 p‖ * ‖w2 r‖ else 0) := by
    intro m _
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p _ => ?_)
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun r _ => ?_)
    by_cases h : p * r = m
    · rw [if_pos h, if_pos h, norm_mul]
    · rw [if_neg h, if_neg h, norm_zero]
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [Finset.sum_comm]
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => Finset.sum_comm)) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  rw [Finset.sum_ite_eq Mbox (p * r) (fun _ => ‖w1 p‖ * ‖w2 r‖)]
  by_cases h : p * r ∈ Mbox
  · rw [if_pos h]
  · rw [if_neg h]
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- **`outerL2_of_sup_and_l1`.**  `LEAN_PROVED_FINITE`.

The finite `L² ≤ L^∞ · L¹` step for the outer coefficient. -/
theorem outerL2_of_sup_and_l1 (Mbox : Finset ℕ) (f : ℕ → ℂ) {A B : ℝ}
    (hA : 0 ≤ A) (hsup : ∀ m ∈ Mbox, ‖f m‖ ≤ A) (hl1 : ∑ m ∈ Mbox, ‖f m‖ ≤ B) :
    ∑ m ∈ Mbox, ‖f m‖ ^ 2 ≤ A * B := by
  have h1 : ∑ m ∈ Mbox, ‖f m‖ ^ 2 ≤ ∑ m ∈ Mbox, A * ‖f m‖ := by
    refine Finset.sum_le_sum fun m hm => ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_right (hsup m hm) (norm_nonneg _)
  have h2 : ∑ m ∈ Mbox, A * ‖f m‖ = A * ∑ m ∈ Mbox, ‖f m‖ := by rw [Finset.mul_sum]
  have h3 : A * ∑ m ∈ Mbox, ‖f m‖ ≤ A * B := mul_le_mul_of_nonneg_left hl1 hA
  linarith [h1, h2.le, h2.ge, h3]

/-! ## §3. The external outer-density interface — `UNINHABITED` -/

/-- **`OuterTwoPrimeL2Normalization3221Input`** — `SOURCE_OPEN / UNINHABITED`.

The physical outer two-prime `L²` normalisation `∑_m |α(m)|² ≤ C · M / log² X`.  Its source
is the literal Ford-generated `ω` slots, which are not present in the repository, and it is
**not** derived from the abstract factorial polarisation. -/
structure OuterTwoPrimeL2Normalization3221Input (P1 P2 Mbox : Finset ℕ) (w1 w2 : ℕ → ℂ)
    (M X Couter : ℝ) : Prop where
  /-- **The open density estimate.** -/
  l2_bound : ∑ m ∈ Mbox, ‖alphaOuter P1 P2 w1 w2 m‖ ^ 2 ≤ Couter * M / (Real.log X) ^ 2

/-- **`outerL2_input_of_sup_and_l1`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

Sup bound **+** `L¹` bound **+** a budget inequality ⇒ the outer `L²` interface.  The two
prime-density antecedents are exactly the ones that stay open. -/
theorem outerL2_input_of_sup_and_l1 (P1 P2 Mbox : Finset ℕ) (w1 w2 : ℕ → ℂ)
    {M X Couter A B : ℝ} (hA : 0 ≤ A)
    (hsup : ∀ m ∈ Mbox, ‖alphaOuter P1 P2 w1 w2 m‖ ≤ A)
    (hl1 : ∑ m ∈ Mbox, ‖alphaOuter P1 P2 w1 w2 m‖ ≤ B)
    (hbudget : A * B ≤ Couter * M / (Real.log X) ^ 2) :
    OuterTwoPrimeL2Normalization3221Input P1 P2 Mbox w1 w2 M X Couter :=
  ⟨le_trans (outerL2_of_sup_and_l1 Mbox _ hA hsup hl1) hbudget⟩

/-- **`outerTwoPrimeL2_not_automatic`.**  `LEAN_PROVED`. -/
theorem outerTwoPrimeL2_not_automatic :
    ∃ (P1 P2 Mbox : Finset ℕ) (w1 w2 : ℕ → ℂ) (M X Couter : ℝ),
      ¬ OuterTwoPrimeL2Normalization3221Input P1 P2 Mbox w1 w2 M X Couter := by
  refine ⟨{1}, {1}, {1}, fun _ => 1, fun _ => 1, 0, Real.exp 1, 0, ?_⟩
  intro h
  have h1 := h.l2_bound
  have halpha : alphaOuter ({1} : Finset ℕ) ({1} : Finset ℕ) (fun _ => (1 : ℂ))
      (fun _ => (1 : ℂ)) 1 = 1 := by
    rw [alphaOuter, Finset.sum_singleton, Finset.sum_singleton]
    norm_num
  rw [Finset.sum_singleton, halpha] at h1
  norm_num at h1

end V21Outer
end Erdos287
