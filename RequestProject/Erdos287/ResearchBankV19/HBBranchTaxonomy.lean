import Mathlib

/-!
# Erdős #287 — Research Bank V19 §8: the structural HB branch taxonomy

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Only the genuinely structural taxonomy is formalized (exponent form: a factor `x^{e_i}`).

Kernel-proved (LEAN BANK):
* `three_large_impossible` — three factors with exponent `> 2/5` cannot occur when the total
  exponent is `≤ 1 + η`, `η < 1/5`;
* `three_large_impossible_mul` — multiplicative form: `a, b, c > x^{2/5}`, `abc ≤ x^{1+η}`, `x > 1`,
  `η < 1/5` is impossible;
* `large_count_le_two` — for any finite factorization with nonnegative exponents and total
  `≤ 1 + η`, at most two exponents exceed `2/5`;
* `typeII_partial_sum` — if every exponent is in `[0, 2/5]` and the total is `≥ 3/10`, some
  partial product has exponent in `[3/10, 7/10]` (a Type-II sub-product);
* `classify`, **`taxonomy_complete`** — every factorization is Type-II (no large factor, with a
  Type-II sub-product), one-large-factor, or two-large-factor.

**Not claimed:** that any coloured branch matches its analytic provider.
-/

namespace Erdos287
namespace ResearchBankV19
namespace HBBranchTaxonomy

theorem three_large_impossible {e₁ e₂ e₃ η : ℝ} (h₁ : 2 / 5 < e₁) (h₂ : 2 / 5 < e₂)
    (h₃ : 2 / 5 < e₃) (hsum : e₁ + e₂ + e₃ ≤ 1 + η) (hη : η < 1 / 5) : False := by
  linarith

theorem three_large_impossible_mul {x a b c η : ℝ} (hx : 1 < x) (ha : x ^ (2 / 5 : ℝ) < a)
    (hb : x ^ (2 / 5 : ℝ) < b) (hc : x ^ (2 / 5 : ℝ) < c) (habc : a * b * c ≤ x ^ (1 + η))
    (hη : η < 1 / 5) : False := by
  have hx0 : 0 < x := by linarith
  have hp : 0 < x ^ (2 / 5 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have h1 : x ^ (2 / 5 : ℝ) * x ^ (2 / 5 : ℝ) * x ^ (2 / 5 : ℝ) < a * b * c := by
    have hab : x ^ (2 / 5 : ℝ) * x ^ (2 / 5 : ℝ) < a * b := mul_lt_mul'' ha hb hp.le hp.le
    exact mul_lt_mul'' hab hc (by positivity) hp.le
  have h2 : x ^ (2 / 5 : ℝ) * x ^ (2 / 5 : ℝ) * x ^ (2 / 5 : ℝ) = x ^ (6 / 5 : ℝ) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; norm_num
  have h3 : x ^ (1 + η) < x ^ (6 / 5 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hx (by linarith)
  linarith

/-- The large factors. -/
noncomputable def large {k : ℕ} (e : Fin k → ℝ) : Finset (Fin k) :=
  Finset.univ.filter fun i => 2 / 5 < e i

theorem large_count_le_two {k : ℕ} (e : Fin k → ℝ) (hnn : ∀ i, 0 ≤ e i) {η : ℝ}
    (hsum : ∑ i, e i ≤ 1 + η) (hη : η < 1 / 5) : (large e).card ≤ 2 := by
  classical
  by_contra h
  push_neg at h
  have hne : (large e).Nonempty := Finset.card_pos.1 (by omega)
  have hlt : ∑ _i ∈ large e, (2 / 5 : ℝ) < ∑ i ∈ large e, e i :=
    Finset.sum_lt_sum_of_nonempty hne fun i hi => (Finset.mem_filter.1 hi).2
  have hsub : ∑ i ∈ large e, e i ≤ ∑ i, e i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hnn i
  rw [Finset.sum_const, nsmul_eq_mul] at hlt
  have hc : (3 : ℝ) ≤ (large e).card := by exact_mod_cast h
  linarith

/-- **Type-II partial sum** (sequence form). -/
theorem typeII_partial_sum (e : ℕ → ℝ) (k : ℕ) (hb : ∀ i < k, 0 ≤ e i ∧ e i ≤ 2 / 5)
    (htot : 3 / 10 ≤ ∑ i ∈ Finset.range k, e i) :
    ∃ j ≤ k, 3 / 10 ≤ ∑ i ∈ Finset.range j, e i ∧ ∑ i ∈ Finset.range j, e i ≤ 7 / 10 := by
  classical
  have hex : ∃ j, 3 / 10 ≤ ∑ i ∈ Finset.range j, e i := ⟨k, htot⟩
  set j := Nat.find hex
  have hj : 3 / 10 ≤ ∑ i ∈ Finset.range j, e i := Nat.find_spec hex
  have hjk : j ≤ k := Nat.find_min' hex htot
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0] at hj
    simp at hj; linarith
  obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hprev : ¬ 3 / 10 ≤ ∑ i ∈ Finset.range j', e i :=
    Nat.find_min hex (show j' < Nat.find hex by omega)
  refine ⟨j' + 1, by omega, by rw [← hj']; exact hj, ?_⟩
  rw [Finset.sum_range_succ]
  have := (hb j' (by omega)).2
  push_neg at hprev
  linarith

/-- The three structural HB branches. -/
inductive HBBranch
  | typeII
  | oneLarge
  | twoLarge
  deriving DecidableEq, Repr

/-- Classification by the number of large factors. -/
def classify (count : ℕ) : HBBranch :=
  match count with
  | 0 => .typeII
  | 1 => .oneLarge
  | _ => .twoLarge

/-- **Taxonomy completeness.** -/
theorem taxonomy_complete {k : ℕ} (e : Fin k → ℝ) (hnn : ∀ i, 0 ≤ e i) {η : ℝ}
    (hsum : ∑ i, e i ≤ 1 + η) (hη : η < 1 / 5) :
    ((large e).card = 0 ∧ classify (large e).card = .typeII) ∨
    ((large e).card = 1 ∧ classify (large e).card = .oneLarge) ∨
    ((large e).card = 2 ∧ classify (large e).card = .twoLarge) := by
  have h := large_count_le_two e hnn hsum hη
  interval_cases hc : (large e).card <;> simp [classify]

end HBBranchTaxonomy
end ResearchBankV19
end Erdos287
