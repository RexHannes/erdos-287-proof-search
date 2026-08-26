import RequestProject.Erdos287.Cnum
import RequestProject.Erdos287.Window

/-!
# Erdős Problem #287 — a universal (non-enumerative) numerator threshold

The exact numerator maximum `C j` requires enumerating all subsets of `{1,…,j}`.  For a
threshold usable at large `j` we replace it by the closed-form upper bound

`L(j) = lcm(1,…,j) · (1 + ⌈log j⌉)`,

which dominates every subset numerator (`numerator_le_numBound`) and hence `C j`
(`C_le_numBound`).  This yields `window_exclusion_universal`, a version of
`primePower_window_exclusion` with the universal threshold instead of exact `C`.
-/

open scoped BigOperators

set_option maxHeartbeats 4000000

namespace Erdos287

/-- `lcm(1,…,j)`. -/
def lcmUpto (j : ℕ) : ℕ := (Finset.Icc 1 j).lcm id

lemma lcmUpto_pos (j : ℕ) : 0 < lcmUpto j := by
  exact Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) )

lemma dvd_lcmUpto {s j : ℕ} (h : s ∈ Finset.Icc 1 j) : s ∣ lcmUpto j := by
  exact Finset.dvd_lcm h

/-
`harmonic` written as a sum over `{1,…,j}`.
-/
lemma harmonic_eq_sum_Icc (j : ℕ) :
    harmonic j = ∑ s ∈ Finset.Icc 1 j, (1 : ℚ) / s := by
  erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ harmonic ];
  norm_num [ Finset.sum_range_succ' ]

/-! ## The harmonic numerator bound (target 1) -/

/-
**Numerator ≤ lcm · harmonic.**  For every nonempty `S ⊆ {1,…,j}`, the reduced
numerator of `∑_{s∈S} 1/s` is at most `lcm(1,…,j) · H_j`.
-/
theorem numerator_le_lcm_mul_harmonic {j : ℕ} {S : Finset ℕ}
    (hsub : S ⊆ Finset.Icc 1 j) :
    ((∑ s ∈ S, (1 : ℚ) / s).num : ℚ) ≤ (lcmUpto j : ℚ) * harmonic j := by
  -- Let `L := lcmUpto j` (so `0 < L` by `lcmUpto_pos`) and `q := ∑ s ∈ S, (1:ℚ)/s`, `P := ∑ s ∈ S, (L/s : ℕ)`.
  set L := lcmUpto j
  have hLpos : 0 < L := lcmUpto_pos j
  set q := ∑ s ∈ S, (1 : ℚ) / s
  set P := ∑ s ∈ S, (L / s : ℕ);
  -- Step A: `q = (P : ℚ) / (L : ℚ)`.
  have hq : q = (P : ℚ) / L := by
    simp +zetaDelta at *;
    rw [ Finset.sum_div _ _ _ ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ Nat.cast_div ( dvd_lcmUpto <| hsub hx ) ( by norm_cast; linarith [ Finset.mem_Icc.mp <| hsub hx ] ) ] ; ring ; norm_num [ hLpos.ne' ] ;
  -- Step B: `q.num ≤ (P : ℤ)`.
  have hq_num : q.num ≤ P := by
    rw [ hq, div_eq_mul_inv ];
    erw [ Rat.mul_num ] ; norm_num [ hLpos.ne' ];
    norm_num [ Int.sign_eq_one_of_pos, hLpos ];
    exact_mod_cast Nat.div_le_self _ _;
  -- Step C: `(P : ℚ) ≤ (L:ℚ) * harmonic j`.
  have hP_le : (P : ℚ) ≤ L * harmonic j := by
    have hP_le : (P : ℚ) = L * q := by
      rw [ hq, mul_div_cancel₀ _ ( by positivity ) ];
    rw [hP_le];
    exact mul_le_mul_of_nonneg_left ( by rw [ harmonic_eq_sum_Icc ] ; exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity ) ( Nat.cast_nonneg _ );
  exact le_trans ( mod_cast hq_num ) hP_le

/-- The universal integer threshold `L(j) = lcm(1,…,j) · (1 + ⌈log j⌉)`. -/
noncomputable def numBound (j : ℕ) : ℤ := (lcmUpto j : ℤ) * (1 + ⌈Real.log j⌉)

/-
**Usable integer bound.**  For every `S ⊆ {1,…,j}`, the reduced numerator of
`∑_{s∈S} 1/s` is at most `numBound j = lcm(1,…,j) · (1 + ⌈log j⌉)`.
-/
theorem numerator_le_numBound {j : ℕ} {S : Finset ℕ}
    (hsub : S ⊆ Finset.Icc 1 j) :
    (∑ s ∈ S, (1 : ℚ) / s).num ≤ numBound j := by
  have h_cast : ((∑ s ∈ S, (1 : ℚ) / s).num : ℝ) ≤ (lcmUpto j : ℝ) * (1 + Real.log j) := by
    have h_cast : ((∑ s ∈ S, (1 : ℚ) / s).num : ℝ) ≤ (lcmUpto j : ℝ) * harmonic j := by
      convert numerator_le_lcm_mul_harmonic hsub using 1;
      norm_cast;
    refine le_trans h_cast ?_;
    gcongr;
    convert harmonic_le_one_add_log j using 1;
  exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast [ numBound ] ; nlinarith [ Int.le_ceil ( Real.log j ), show ( lcmUpto j : ℝ ) ≥ 0 by positivity ] )

/-
The exact maximum `C j` is dominated by the universal threshold.
-/
theorem C_le_numBound (j : ℕ) : C j ≤ numBound j := by
  by_cases hj : 1 ≤ j;
  · obtain ⟨ S, hS₁, hS₂, hS₃ ⟩ := C_attained j hj ; exact hS₃ ▸ numerator_le_numBound hS₂;
  · interval_cases j;
    unfold C numBound; norm_num;

/-! ## Universal window exclusion (target 2) -/

/-
**Universal prime-power window exclusion.**  Same conclusion as
`primePower_window_exclusion`, but with the universal threshold `numBound` in place of
the exact numerator maximum `C`.
-/
theorem window_exclusion_universal
    (A : Finset ℕ) (M p e : ℕ) (hp : p.Prime)
    (hpos : ∀ a ∈ A, 0 < a)
    (hAM : ∀ a ∈ A, a ≤ M)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1)
    (he : 1 ≤ e)
    (hpL : numBound (M / p ^ e) < (p : ℤ)) :
    ∀ a ∈ A, ¬ (p ^ e ∣ a) := by
  intro a ha hpa
  by_cases hqM : p ^ e ≤ M;
  · exact absurd ( primePower_window_exclusion A M p e hp hpos hAM hsum he hqM ( lt_of_le_of_lt ( C_le_numBound _ ) hpL ) a ha hpa ) ( by norm_num );
  · linarith [ Nat.le_of_dvd ( hpos a ha ) hpa, hAM a ha ]

end Erdos287