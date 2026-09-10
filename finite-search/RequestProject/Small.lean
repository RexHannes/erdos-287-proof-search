import RequestProject.Pairs

/-!
# Small maxima

Window pairs covering `8 ≤ M ≤ 50`, and an exhaustive finite check for `M ≤ 7`.

* `M ∈ [8, 14]`  : `x = 7`,  `x + 1 = 8 = 2 ^ 3`.
* `M ∈ [14, 26]` : `x = 13`, `x + 1 = 14 = 2 · 7`.
* `M ∈ [26, 50]` : `x = 25 = 5 ^ 2`, `x + 1 = 26 = 2 · 13`.
* `M ≤ 7`        : a direct enumeration of all subsets of `{2, …, 7}`.
-/

namespace Erdos287

open Finset

set_option maxRecDepth 10000

/-- Window pair `(7, 8)`, valid for `8 ≤ M ≤ 14`. -/
theorem windowPairSupply_seven {M : ℕ} (h1 : 8 ≤ M) (h2 : M ≤ 14) : WindowPairSupply M := by
  refine ⟨7, 7, 1, 2, 2, 2, 3, 1, 1, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · refine forbiddenPP_of_sum_lt (S := 3) (by norm_num) one_pos (by norm_num) ?_ (by norm_num)
      (by decide) (by decide) (by norm_num)
    norm_num; omega
  · norm_num
  · refine forbiddenPP_of_sum_lt (S := 1) (by norm_num) (by norm_num) (by norm_num) ?_
      (by norm_num) (by decide) (by decide) (by norm_num)
    norm_num; omega
  · norm_num

/-- Window pair `(13, 14)`, valid for `14 ≤ M ≤ 26`. -/
theorem windowPairSupply_thirteen {M : ℕ} (h1 : 14 ≤ M) (h2 : M ≤ 26) : WindowPairSupply M := by
  refine ⟨13, 13, 1, 2, 2, 7, 1, 3, 6, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · refine forbiddenPP_of_sum_lt (S := 3) (by norm_num) one_pos (by norm_num) ?_ (by norm_num)
      (by decide) (by decide) (by norm_num)
    norm_num; omega
  · norm_num
  · refine ⟨by norm_num, one_pos, ?_, by norm_num, by decide, by decide, by decide⟩
    norm_num; omega
  · norm_num

/-- Window pair `(25, 26)`, valid for `26 ≤ M ≤ 50`. -/
theorem windowPairSupply_twentyfive {M : ℕ} (h1 : 26 ≤ M) (h2 : M ≤ 50) : WindowPairSupply M := by
  refine ⟨25, 5, 2, 2, 2, 13, 1, 3, 6, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · refine forbiddenPP_of_sum_lt (S := 3) (by norm_num) (by norm_num) (by norm_num) ?_
      (by norm_num) (by decide) (by decide) (by norm_num)
    norm_num; omega
  · norm_num
  · refine forbiddenPP_of_sum_lt (S := 11) (by norm_num) one_pos (by norm_num) ?_ (by norm_num)
      (by decide) (by decide) (by norm_num)
    norm_num; omega
  · norm_num

/-- Window pair `(46, 47)`, valid for `47 ≤ M ≤ 92`.  `46 = 2 · 23` (window `4` for `23`),
`47` is prime (window `1`). -/
theorem windowPairSupply_46 {M : ℕ} (h1 : 47 ≤ M) (h2 : M ≤ 92) : WindowPairSupply M := by
  refine ⟨46, 23, 1, 4, 12, 47, 1, 1, 1, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, one_pos, ?_, by norm_num, by decide, by decide, by decide⟩
    norm_num; omega
  · norm_num
  · refine forbiddenPP_of_sum_lt (S := 1) (by norm_num) one_pos (by norm_num) ?_ (by norm_num)
      (by decide) (by decide) (by norm_num)
    norm_num; omega
  · norm_num

/-- Window pair `(82, 83)`, valid for `83 ≤ M ≤ 164`.  `82 = 2 · 41` (window `4` for `41`),
`83` is prime (window `1`). -/
theorem windowPairSupply_82 {M : ℕ} (h1 : 83 ≤ M) (h2 : M ≤ 164) : WindowPairSupply M := by
  refine ⟨82, 41, 1, 4, 12, 83, 1, 1, 1, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · refine forbiddenPP_of_sum_lt (S := 25) (by norm_num) one_pos (by norm_num) ?_ (by norm_num)
      (by decide) (by decide) (by norm_num)
    norm_num; omega
  · norm_num
  · refine forbiddenPP_of_sum_lt (S := 1) (by norm_num) one_pos (by norm_num) ?_ (by norm_num)
      (by decide) (by decide) (by norm_num)
    norm_num; omega
  · norm_num

/-- Window pair `(158, 159)`, valid for `159 ≤ M ≤ 316`.  `158 = 2 · 79` (window `4` for `79`),
`159 = 3 · 53` (window `5` for `53`). -/
theorem windowPairSupply_158 {M : ℕ} (h1 : 159 ≤ M) (h2 : M ≤ 316) : WindowPairSupply M := by
  refine ⟨158, 79, 1, 4, 12, 53, 1, 5, 60, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · refine forbiddenPP_of_sum_lt (S := 25) (by norm_num) one_pos (by norm_num) ?_ (by norm_num)
      (by decide) (by decide) (by norm_num)
    norm_num; omega
  · norm_num
  · refine ⟨by norm_num, one_pos, ?_, by norm_num, by decide, by decide, by decide⟩
    norm_num; omega
  · norm_num

/-- Exhaustive check: no subset of `{2, …, 7}` is a counterexample. -/
theorem base_check : ∀ A ∈ (Finset.Icc 2 7).powerset,
    ¬ ((∑ n ∈ A, 420 / n) = 420 ∧ 2 ≤ A.card ∧
      ∀ a ∈ A, (∃ b ∈ A, a < b) → (a + 1 ∈ A ∨ a + 2 ∈ A)) := by decide

/-- No counterexample has maximum at most `7`. -/
theorem no_counterexample_le_seven {A : Finset ℕ} (h : Erdos287Counterexample A)
    (hM : A.max' h.nonempty ≤ 7) : False := by
  obtain ⟨hgt1, hcard, hsum, hgap⟩ := id h
  have hAM : ∀ n ∈ A, n ≤ 7 := fun n hn => le_trans (Finset.le_max' _ n hn) hM
  have hsub : A ⊆ Finset.Icc 2 7 := fun n hn =>
    Finset.mem_Icc.2 ⟨hgt1 n hn, hAM n hn⟩
  have hdvd : ∀ n ∈ A, n ∣ 420 := by
    intro n hn
    have h1 := hgt1 n hn
    have h2 := hAM n hn
    interval_cases n <;> norm_num
  have hnat : (∑ n ∈ A, 420 / n) = 420 := by
    have hQ : ((∑ n ∈ A, 420 / n : ℕ) : ℚ) = ((420 : ℕ) : ℚ) := by
      push_cast
      calc ∑ n ∈ A, ((420 / n : ℕ) : ℚ) = ∑ n ∈ A, (420 : ℚ) / n := by
            refine Finset.sum_congr rfl fun n hn => ?_
            have hn0 : ((n : ℚ)) ≠ 0 := by
              have := hgt1 n hn
              positivity
            exact_mod_cast Nat.cast_div (hdvd n hn) hn0
        _ = 420 * ∑ n ∈ A, (1 : ℚ) / n := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
        _ = 420 := by rw [hsum, mul_one]
    exact_mod_cast hQ
  exact base_check A (Finset.mem_powerset.2 hsub) ⟨hnat, hcard, hgap⟩

end Erdos287
