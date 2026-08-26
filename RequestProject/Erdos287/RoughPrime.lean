import RequestProject.Erdos287.Window

/-!
# Erdős Problem #287 — the rough-prime top-layer exclusion

Let `A ⊆ [1, M]` be a finite set of positive integers with `∑_{a∈A} 1/a = 1`, let `ℓ`
be a prime with `ℓ² > M`, and `j = ⌊M/ℓ⌋ ≥ 1`.  If

`ℓ > j · lcm(1, …, j)`,

then no element of `A` is divisible by `ℓ`.

This is a coarser but easier-to-certify companion of `primePower_window_exclusion`:
instead of the sharp numerator bound `C j`, it uses the crude bound
`C j ≤ j · lcm(1,…,j)` (proved here as `C_le_j_mul_lcm`).  Because
`primePower_window_exclusion` already handles the top-`ℓ`-layer for any exponent, the
hypothesis `ℓ² > M` is not needed for the proof (it is kept because the problem states
it: under `ℓ² > M` the maximal `ℓ`-adic valuation of any element is exactly `1`).
-/

open scoped BigOperators

set_option maxHeartbeats 4000000

namespace Erdos287

/-- The least common multiple of `{1, …, j}`. -/
def lcmUpTo (j : ℕ) : ℕ := (Finset.Icc 1 j).lcm id

/-
`lcm(1,…,j)` is positive.
-/
theorem lcmUpTo_pos (j : ℕ) : 0 < lcmUpTo j := by
  exact Nat.pos_of_dvd_of_pos ( Finset.lcm_dvd fun x hx => Finset.dvd_prod_of_mem _ hx ) ( Finset.prod_pos fun x hx => Finset.mem_Icc.mp hx |>.1 )

/-
A `U/D` rational has reduced numerator at most `U`.
-/
theorem num_div_nat_le (U D : ℕ) : ((U : ℚ) / (D : ℚ)).num ≤ (U : ℤ) := by
  by_cases hD : D = 0 <;> by_cases hU : U = 0 <;> simp_all +decide [ Rat.div_def' ];
  simp_all +decide [ Rat.mkRat_def ];
  exact_mod_cast Nat.div_le_self _ _

/-
**Crude numerator bound for a subset.** For `S ⊆ {1,…,j}`, the reduced
numerator of `∑_{s∈S} 1/s` is at most `j · lcm(1,…,j)`.
-/
theorem num_le_j_mul_lcm {j : ℕ} (S : Finset ℕ)
    (hsub : S ⊆ Finset.Icc 1 j) :
    (∑ s ∈ S, (1 : ℚ) / s).num ≤ (j : ℤ) * (lcmUpTo j : ℤ) := by
  -- Let $D = \text{lcm}(1, \ldots, j)$.
  set D := lcmUpTo j;
  -- Then $\sum_{s \in S} \frac{1}{s} = \frac{U}{D}$ where $U = \sum_{s \in S} \frac{D}{s}$.
  set U := ∑ s ∈ S, D / s
  have h_sum : (∑ s ∈ S, (1 : ℚ) / s) = (U : ℚ) / D := by
    rw [ Nat.cast_sum, Finset.sum_div _ _ _ ];
    refine Finset.sum_congr rfl fun x hx => ?_;
    rw [ Nat.cast_div ( show x ∣ D from Finset.dvd_lcm ( hsub hx ) ) ( by norm_cast; linarith [ Finset.mem_Icc.mp ( hsub hx ) ] ) ] ; ring;
    rw [ mul_assoc, mul_inv_cancel₀ ( Nat.cast_ne_zero.mpr <| ne_of_gt <| lcmUpTo_pos j ), mul_one ];
  -- Then $(∑ s ∈ S, (1 : ℚ) / s).num ≤ U$ by num_div_nat_le.
  have h_num_le_U : (∑ s ∈ S, (1 : ℚ) / s).num ≤ U := by
    exact h_sum.symm ▸ num_div_nat_le _ _;
  exact h_num_le_U.trans ( mod_cast le_trans ( Finset.sum_le_sum fun _ _ => Nat.div_le_self _ _ ) ( by norm_num; nlinarith [ show S.card ≤ j from le_trans ( Finset.card_le_card hsub ) ( by simp ) ] ) )

/-
**Crude bound `C j ≤ j · lcm(1,…,j)`.**
-/
theorem C_le_j_mul_lcm (j : ℕ) : C j ≤ (j : ℤ) * (lcmUpTo j : ℤ) := by
  by_cases hj : 1 ≤ j;
  · obtain ⟨ S, _, hsub, hval ⟩ := C_attained j hj ; exact hval ▸ num_le_j_mul_lcm S hsub;
  · interval_cases j ; decide

/-
**Rough-prime top-layer exclusion.** If `A ⊆ [1,M]` has `∑ 1/a = 1`, `ℓ` is prime
with `ℓ² > M` and `j = ⌊M/ℓ⌋ ≥ 1`, and `ℓ > j · lcm(1,…,j)`, then no element of `A` is
divisible by `ℓ`.

The hypothesis `hℓ2 : M < ℓ²` is part of the stated problem but is not used by the
proof (see the module docstring).
-/
theorem roughPrime_topLayer_empty
    (A : Finset ℕ) (M ℓ : ℕ) (hℓ : ℓ.Prime)
    (hpos : ∀ a ∈ A, 0 < a)
    (hAM : ∀ a ∈ A, a ≤ M)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1)
    (hℓ2 : M < ℓ ^ 2)
    (hj : 1 ≤ M / ℓ)
    (hbig : (M / ℓ) * lcmUpTo (M / ℓ) < ℓ) :
    ∀ a ∈ A, ¬ ℓ ∣ a := by
  convert primePower_window_exclusion A M ℓ 1 hℓ hpos hAM hsum ( by norm_num ) ( by
    nlinarith [ Nat.div_mul_le_self M ℓ ] ) ( by
    refine' lt_of_le_of_lt ( C_le_j_mul_lcm _ ) _;
    grind +splitImp ) using 1;
  norm_num

end Erdos287