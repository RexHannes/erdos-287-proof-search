import Mathlib
import RequestProject.Erdos287.FixedCertificateFordData

/-!
# The singleton reduction — rational parameter ledger and the smooth-vector lemma (V13)

This file contains the two *unconditional* ingredients of the canonical-singleton
reduction:

1. **Part D — the rational parameter ledger.**  Every deterministic inequality used by
   the singleton argument is kernel-checked from the exact rational
   `ν₀ = 16623/100000` (the value already banked as `Erdos287.FordData.nu0`) and the
   shrink parameter `ε` constrained by `0 < ε < ν₀/100`, with
   `σ = ν₀ − 2ε`.  No floating point is used anywhere: all statements are inequalities
   in the ordered field `ℝ` whose numerical content is discharged by `norm_num` on exact
   rationals.

2. **Part C — the normalised smooth-vector lemma.**  A purely combinatorial statement:
   a vector of positive normalised logarithmic sizes summing to `1`, each of size at most
   `σ`, always has a nonempty sub-sum in the Type-II window `[ε, ε+σ]`.  The proof is the
   elementary two-case argument (a large coordinate is used alone; otherwise the first
   partial sum to cross `ε` overshoots by less than `ε ≤ σ`).  There is no asymptotic
   notation and no analytic input.

## Honesty statement

Nothing here mentions, uses, or presupposes any analytic estimate.  The parameter `ε` is
never given a numerical value: every theorem is universally quantified over the admissible
range.

## Main results

* `sigma_pos`, `epsilon_lt_sigma`, `epsilon_lt_sigma_div_three`, `sigma_lt_one_sixth`,
  `two_sigma_div_three_lt_one`, `sigma_lt_epsilon_add_sigma`, `two_sigma_lt_one`,
  `sigma_le_nu0`, `seven_mul_sigma_gt_one` — the ledger;
* `exists_subset_sum_in_typeII_window` — the smooth-vector lemma;
* `exists_singleton_subset_sum_in_typeII_window` — its singleton special case, which is
  the case actually used downstream.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace Singleton

/-! ## Part D — the rational parameter ledger -/

/-- The central parameter `ν₀ = 0.16623` as a real number.  It is the image of the banked
exact rational `Erdos287.FordData.nu0`. -/
noncomputable def nu0R : ℝ := 16623 / 100000

/-- The ledger constant really is the cast of the banked rational parameter. -/
theorem nu0R_eq_cast_nu0 : ((FordData.nu0 : ℚ) : ℝ) = nu0R := by
  norm_num [FordData.nu0, nu0R]

theorem nu0R_pos : 0 < nu0R := by norm_num [nu0R]

/-- `σ = ν₀ − 2ε`, the smooth-support exponent of the `k = 0`, `J = ∅` branch. -/
noncomputable def sigmaOf (eps : ℝ) : ℝ := nu0R - 2 * eps

/-- The admissible range of the shrink parameter: `0 < ε < ν₀/100`. -/
def AdmissibleEps (eps : ℝ) : Prop := 0 < eps ∧ eps < nu0R / 100

theorem admissibleEps_pos {eps : ℝ} (h : AdmissibleEps eps) : 0 < eps := h.1

theorem admissibleEps_lt {eps : ℝ} (h : AdmissibleEps eps) : eps < nu0R / 100 := h.2

/-- The admissible range is nonempty (so the ledger is not vacuous). -/
theorem admissibleEps_nonempty : AdmissibleEps (1 / 1000000) := by
  constructor <;> norm_num [nu0R]

/-- `σ > 0`. -/
theorem sigma_pos {eps : ℝ} (h : AdmissibleEps eps) : 0 < sigmaOf eps := by
  obtain ⟨h0, h1⟩ := h
  simp only [sigmaOf, nu0R] at *
  linarith

/-- `σ ≤ ν₀`, with equality only in the (excluded) limit `ε = 0`. -/
theorem sigma_le_nu0 {eps : ℝ} (h : AdmissibleEps eps) : sigmaOf eps ≤ nu0R := by
  have := h.1
  simp only [sigmaOf]
  linarith

/-- `ε < σ`. -/
theorem epsilon_lt_sigma {eps : ℝ} (h : AdmissibleEps eps) : eps < sigmaOf eps := by
  obtain ⟨h0, h1⟩ := h
  simp only [sigmaOf, nu0R] at *
  linarith

/-- **Hostile check 1.**  `ε < ν₀/100` really does imply `ε < σ/3`: it is equivalent to
`5ε < ν₀`, and `ε < ν₀/100` gives `5ε < ν₀/20 < ν₀`. -/
theorem epsilon_lt_sigma_div_three {eps : ℝ} (h : AdmissibleEps eps) :
    eps < sigmaOf eps / 3 := by
  obtain ⟨h0, h1⟩ := h
  simp only [sigmaOf, nu0R] at *
  linarith

/-- **Hostile check 2.**  `σ < 1/6` is *strict* with the exact rational `ν₀`:
`16623/100000 < 1/6 ↔ 99738 < 100000`. -/
theorem sigma_lt_one_sixth {eps : ℝ} (h : AdmissibleEps eps) : sigmaOf eps < 1 / 6 := by
  have h0 := h.1
  simp only [sigmaOf, nu0R]
  linarith

/-- Even without the shrink, the *unshrunk* parameter is below `1/6`. -/
theorem nu0R_lt_one_sixth : nu0R < 1 / 6 := by norm_num [nu0R]

/-- `2σ/3 < 1`. -/
theorem two_sigma_div_three_lt_one {eps : ℝ} (h : AdmissibleEps eps) :
    2 * sigmaOf eps / 3 < 1 := by
  have := sigma_lt_one_sixth h
  linarith

/-- `2σ < 1` — the bound actually used to rule out `s = r = 1` without invoking the
terminal convention. -/
theorem two_sigma_lt_one {eps : ℝ} (h : AdmissibleEps eps) : 2 * sigmaOf eps < 1 := by
  have := sigma_lt_one_sixth h
  linarith

/-- `σ < ε + σ`. -/
theorem sigma_lt_epsilon_add_sigma {eps : ℝ} (h : AdmissibleEps eps) :
    sigmaOf eps < eps + sigmaOf eps := by
  have := h.1
  linarith

/-- `6σ < 1`: hence a fragmentation into pieces of size `≤ σ` summing to `1` needs at
least seven pieces. -/
theorem six_sigma_lt_one {eps : ℝ} (h : AdmissibleEps eps) : 6 * sigmaOf eps < 1 := by
  have := sigma_lt_one_sixth h
  linarith

/-- `1 < 7σ`: the complementary bound, giving the *exact* seven-piece threshold. -/
theorem seven_mul_sigma_gt_one {eps : ℝ} (h : AdmissibleEps eps) : 1 < 7 * sigmaOf eps := by
  obtain ⟨h0, h1⟩ := h
  simp only [sigmaOf, nu0R] at *
  linarith

/-- `σ/3 < σ`. -/
theorem sigma_div_three_lt_sigma {eps : ℝ} (h : AdmissibleEps eps) :
    sigmaOf eps / 3 < sigmaOf eps := by
  have := sigma_pos h
  linarith

/-- `ε ≤ 1`, needed by the smooth-vector lemma. -/
theorem epsilon_le_one {eps : ℝ} (h : AdmissibleEps eps) : eps ≤ 1 := by
  have := h.2
  simp only [nu0R] at this
  linarith

/-! ## Part C — the normalised smooth-vector lemma

The statement is purely combinatorial: the index set is `Finset.range n` and the candidate
sub-sums are over arbitrary subsets, so nothing about the underlying arithmetic objects is
used. -/

/-- **The normalised smooth-vector lemma.**  Let `z₀, …, z_{n−1}` be positive reals with
`∑ zᵢ = 1` and `zᵢ ≤ σ` for all `i`, and let `0 < ε < σ` with `ε ≤ 1`.  Then some nonempty
subset of indices has sub-sum in the Type-II window `[ε, ε+σ]`.

The proof is the elementary two-case argument:

1. if some `zᵢ ≥ ε`, that singleton already works, since `zᵢ ≤ σ ≤ ε + σ`;
2. if every `zᵢ < ε`, take the shortest prefix whose sum reaches `ε`; the previous prefix
   is `< ε` and the extra term is `< ε`, so the sum is `< 2ε ≤ ε + σ`.

The positivity hypothesis `hzpos` is used only for the last (bonus) conclusion
`0 < ∑_{i∈S} zᵢ`; the window statement itself does not need it. -/
theorem exists_subset_sum_in_typeII_window
    {n : ℕ} {z : ℕ → ℝ} {eps sigma : ℝ}
    (hzpos : ∀ i ∈ Finset.range n, 0 < z i)
    (hzle : ∀ i ∈ Finset.range n, z i ≤ sigma)
    (hsum : ∑ i ∈ Finset.range n, z i = 1)
    (heps : 0 < eps) (hes : eps ≤ sigma) (heps1 : eps ≤ 1) :
    ∃ S : Finset ℕ, S.Nonempty ∧ S ⊆ Finset.range n ∧
      eps ≤ ∑ i ∈ S, z i ∧ ∑ i ∈ S, z i ≤ eps + sigma ∧ 0 < ∑ i ∈ S, z i := by
  classical
  suffices h : ∃ S : Finset ℕ, S.Nonempty ∧ S ⊆ Finset.range n ∧
      eps ≤ ∑ i ∈ S, z i ∧ ∑ i ∈ S, z i ≤ eps + sigma by
    obtain ⟨S, hne, hsub, h1, h2⟩ := h
    exact ⟨S, hne, hsub, h1, h2, Finset.sum_pos (fun i hi => hzpos i (hsub hi)) hne⟩
  by_cases hbig : ∃ i ∈ Finset.range n, eps ≤ z i
  · -- Case 1: a single large coordinate suffices.
    obtain ⟨i, hi, hzi⟩ := hbig
    refine ⟨{i}, ⟨i, Finset.mem_singleton_self i⟩, ?_, ?_, ?_⟩
    · simpa using hi
    · simpa using hzi
    · have : z i ≤ sigma := hzle i hi
      simp only [Finset.sum_singleton]
      linarith
  · -- Case 2: every coordinate is below `ε`; use the first crossing prefix.
    push_neg at hbig
    have hsmall : ∀ i ∈ Finset.range n, z i < eps := hbig
    have hexists : ∃ j, eps ≤ ∑ i ∈ Finset.range j, z i := ⟨n, by rw [hsum]; exact heps1⟩
    set j := Nat.find hexists with hj
    have hjspec : eps ≤ ∑ i ∈ Finset.range j, z i := Nat.find_spec hexists
    have hjle : j ≤ n := Nat.find_le (by rw [hsum]; exact heps1)
    have hjne : j ≠ 0 := by
      intro h0
      rw [h0] at hjspec
      simp at hjspec
      linarith
    obtain ⟨m, hm⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    have hmin : ¬ (eps ≤ ∑ i ∈ Finset.range m, z i) := by
      rw [hj] at hm
      exact Nat.find_min hexists (by omega)
    push_neg at hmin
    have hmn : m < n := by omega
    have hzm : z m < eps := hsmall m (Finset.mem_range.2 hmn)
    refine ⟨Finset.range j, ⟨m, Finset.mem_range.2 (by omega)⟩, ?_, hjspec, ?_⟩
    · intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    · rw [hm, Finset.sum_range_succ]
      linarith

/-- The singleton special case, which is what the canonical-singleton theorem actually
uses: a coordinate already in `(ε, ε+σ]` gives a one-element Type-II set. -/
theorem exists_singleton_subset_sum_in_typeII_window
    {z sigma eps : ℝ} (h1 : eps < z) (h2 : z ≤ sigma) (heps : 0 < eps) :
    eps < z ∧ z ≤ eps + sigma := ⟨h1, by linarith⟩

end Singleton
end Erdos287
