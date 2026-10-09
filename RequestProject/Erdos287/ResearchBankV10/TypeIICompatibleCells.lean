import Mathlib

/-!
# Erdős #287 — Research Bank V10 §G: the compatible-cell Type-II count

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The repaired residue-cell saving.  **This is finite combinatorics, not a Kloosterman theorem**:
it is a counting input to the (external) analytic Type-II estimate.

Setting: `k ≠ 0`, `K = |k|`, `d = C·q₁·q₂ > 0`; detector geometry
`n₁ ≡ α (mod K)`, `n₂ ≡ α (mod K d)`.

* `compatibleAlpha_card_eq_d` — for fixed `n₁` (and `k`), the number of `α`-classes modulo `K d`
  compatible with `n₁ (mod K)` is **exactly `d`**, not `K d`;
* `compatibleAlpha_card_eq_d_int` — the same with `k : ℤ`, `k ≠ 0`, `d = C q₁ q₂`;
* `old_count_fails_2_3` / `old_count_fails` — hostile fixtures with `K > 1`: the old count `K d`
  is wrong;
* `detector_n2_determined` — once `α` is fixed modulo `K d`, `n₂` is determined modulo `K d` and is
  automatically compatible with `n₁` modulo `K`;
* `outer_cell_ratio` / `outer_total_comparison` — the outer-cell comparison and the symbolic
  prefactor improvement `old_count / new_count = K`.
-/

namespace Erdos287
namespace ResearchBankV10
namespace TypeIICompatibleCells

open Finset

/-- The compatible `α`-classes modulo `K d` for a fixed `n₁`. -/
def compatibleAlpha (K d n₁ : ℕ) : Finset ℕ :=
  (range (K * d)).filter (fun α => α % K = n₁ % K)

/-- **The compatible-cell count is exactly `d`.** -/
theorem compatibleAlpha_card_eq_d {K : ℕ} (hK : 0 < K) (d n₁ : ℕ) :
    (compatibleAlpha K d n₁).card = d := by
  unfold compatibleAlpha
  suffices h : (range d).card = ((range (K * d)).filter (fun α => α % K = n₁ % K)).card by
    rw [← h, card_range]
  refine Finset.card_nbij' (fun j => n₁ % K + K * j) (fun α => α / K) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [coe_range, Set.mem_Iio, coe_filter, mem_range, Set.mem_setOf_eq] at *
    have hm : n₁ % K < K := Nat.mod_lt _ hK
    refine ⟨by nlinarith, ?_⟩
    rw [Nat.add_mul_mod_self_left, Nat.mod_mod]
  · intro α hα
    simp only [coe_range, Set.mem_Iio, coe_filter, mem_range, Set.mem_setOf_eq] at *
    exact Nat.div_lt_of_lt_mul hα.1
  · intro j _
    have hm : n₁ % K < K := Nat.mod_lt _ hK
    simp only
    rw [Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt hm, zero_add]
  · intro α hα
    simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hα
    simp only
    rw [← hα.2]; exact Nat.mod_add_div α K

/-- Integer form: `k ≠ 0`, `d = C q₁ q₂`. -/
theorem compatibleAlpha_card_eq_d_int {k : ℤ} (hk : k ≠ 0) (C q₁ q₂ n₁ : ℕ) :
    (compatibleAlpha k.natAbs (C * q₁ * q₂) n₁).card = C * q₁ * q₂ :=
  compatibleAlpha_card_eq_d (Int.natAbs_pos.2 hk) _ _

/-- **Hostile fixture** `k = 2`, `C = q₁ = 1`, `q₂ = 3`: the compatible count is `3 = d`, and the
old count `|k|·d = 6` is wrong. -/
theorem old_count_fails_2_3 :
    (compatibleAlpha 2 3 0).card = 3 ∧ (compatibleAlpha 2 3 0).card ≠ 2 * 3 := by
  decide

/-- **Hostile fixture (general)**: whenever `K > 1` and `d > 0`, the old count `K d` is wrong. -/
theorem old_count_fails {K d : ℕ} (hK : 1 < K) (hd : 0 < d) (n₁ : ℕ) :
    (compatibleAlpha K d n₁).card ≠ K * d := by
  rw [compatibleAlpha_card_eq_d (by omega)]
  intro h
  have : 1 * d < K * d := Nat.mul_lt_mul_of_pos_right hK hd
  omega

/-- **Detector geometry**: `n₂ ≡ α (mod K d)` forces `n₂ ≡ α (mod K)`; so if `α` is compatible with
`n₁` then so is `n₂`, and `n₂` is determined modulo `K d` by `α`. -/
theorem detector_n2_determined {K d α n₁ n₂ : ℕ} (hα : α % K = n₁ % K)
    (h2 : n₂ % (K * d) = α % (K * d)) : n₂ % K = n₁ % K := by
  have h3 : n₂ % (K * d) % K = n₂ % K := Nat.mod_mul_right_mod n₂ K d
  have h4 : α % (K * d) % K = α % K := Nat.mod_mul_right_mod α K d
  rw [← h3, h2, h4, hα]

/-- **Symbolic prefactor improvement**: `old_count / new_count = K`. -/
theorem outer_cell_ratio {K d : ℕ} (hK : 0 < K) (hd : 0 < d) (n₁ : ℕ) :
    ((K * d : ℕ) : ℚ) / (compatibleAlpha K d n₁).card = K := by
  rw [compatibleAlpha_card_eq_d hK]
  have : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast; field_simp

/-- **Outer-cell comparison** over a finite family of nonzero `k`: the old total `∑ |k| d`
dominates the new total `∑ d = #k · d`; with all `|k| = K₀` it is exactly `K₀` times larger. -/
theorem outer_total_comparison (ks : Finset ℤ) (hks : ∀ k ∈ ks, k ≠ 0) (d n₁ : ℕ) :
    ∑ k ∈ ks, (compatibleAlpha k.natAbs d n₁).card = ks.card * d ∧
    ks.card * d ≤ ∑ k ∈ ks, k.natAbs * d := by
  constructor
  · rw [Finset.sum_congr rfl fun k hk => compatibleAlpha_card_eq_d (Int.natAbs_pos.2 (hks k hk)) d n₁]
    simp
  · rw [← Finset.sum_mul]
    apply Nat.mul_le_mul_right
    calc ks.card = ∑ _k ∈ ks, 1 := by simp
      _ ≤ ∑ k ∈ ks, k.natAbs := Finset.sum_le_sum fun k hk => Int.natAbs_pos.2 (hks k hk)

theorem outer_total_uniform (ks : Finset ℤ) {K₀ : ℕ} (hK : ∀ k ∈ ks, k.natAbs = K₀) (d : ℕ) :
    ∑ k ∈ ks, k.natAbs * d = K₀ * (ks.card * d) := by
  rw [Finset.sum_congr rfl fun k hk => by rw [hK k hk]]
  simp; ring

end TypeIICompatibleCells
end ResearchBankV10
end Erdos287
