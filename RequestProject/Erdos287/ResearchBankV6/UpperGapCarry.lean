import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V6: the upper-gap same-trace cofactor–carry kernel

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

This file is pure kernel mathematics: every theorem below is proved, with no external input and
no uninhabited interface.

Setting.  Fix an upper bound `M`, a lower endpoint `a`, and a prime row `p`.  The *allowed
cofactors* of the row are the `j` with `a ≤ p * j ≤ M`; the *height* of the row is
`N_p = ⌊M / p⌋`, and `L_N = lcm (1, …, N)`.  A selection (`no-00` trace) is a Boolean function
`ε` on the physical denominators `n = p * j`.

* `rowNumerator` is the exact integer row numerator `T_p = ∑_j ε_{pj} · L_N / j`;
* `rowMass` is the exact rational row mass `∑_j ε_{pj} / (p j)`;
* `rowMass_eq_div` : `∑_j ε_{pj}/(pj) = T_p / (p L_N)`;
* `prime_removed_iff_dvd_rowNumerator` : the prime `p` disappears from the row denominator
  (i.e. the row mass is an integer multiple of `1 / L_N`, equivalently its reduced denominator
  divides `L_N`) **iff** `p ∣ T_p`;
* `rowMass_eq_carry_div` : when `p ∣ T_p`, with the carry `k_p = T_p / p`, the exact identity
  `∑_j ε_{pj}/(pj) = k_p / L_N`;
* `carry_height_aggregation` : the exact height aggregation
  `∑_{p} ∑_j ε_{pj}/(pj) = ∑_N K_N / L_N` with `K_N = ∑_{p : ⌊M/p⌋ = N} k_p`.

A deliberate **counterfixture** (`rowNumerator_range_substitution_counterfixture`) records that the
selected/truncated cofactor range may *not* be silently replaced by `1, …, N`.
-/

namespace Erdos287
namespace ResearchBankV6
namespace UpperGap

open Finset

/-! ## 1.  `L_N = lcm (1, …, N)` -/

/-- `lcmUpto N = lcm (1, 2, …, N)`. -/
def lcmUpto (N : ℕ) : ℕ := (Finset.Icc 1 N).lcm id

@[simp] theorem lcmUpto_zero : lcmUpto 0 = 1 := rfl

/-- `lcm (1, …, N)` is positive. -/
theorem lcmUpto_pos (N : ℕ) : 0 < lcmUpto N := by
  refine Nat.pos_of_ne_zero fun h => ?_
  rw [lcmUpto, Finset.lcm_eq_zero_iff] at h
  obtain ⟨x, hx, hx0⟩ := h
  simp [Finset.mem_Icc] at hx
  simp at hx0
  omega

/-- Every `1 ≤ j ≤ N` divides `lcm (1, …, N)`. -/
theorem dvd_lcmUpto {j N : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ N) : j ∣ lcmUpto N := by
  have := Finset.dvd_lcm (f := (id : ℕ → ℕ)) (b := j) (s := Finset.Icc 1 N)
    (Finset.mem_Icc.2 ⟨h1, h2⟩)
  simpa [lcmUpto] using this

/-! ## 2.  Rows, allowed cofactors, heights -/

/-- The height of the prime row `p` inside `[a, M]`: `N_p = ⌊M / p⌋`. -/
def height (M p : ℕ) : ℕ := M / p

/-- The **actual** allowed cofactors of the row `p` in the window `[a, M]`: the `j ≥ 1` with
`a ≤ p j ≤ M`.  No truncation or completion to `1, …, N` is performed. -/
def allowedCofactors (a M p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (M / p)).filter (fun j => a ≤ p * j)

theorem mem_allowedCofactors {a M p j : ℕ} :
    j ∈ allowedCofactors a M p ↔ (1 ≤ j ∧ j ≤ M / p) ∧ a ≤ p * j := by
  simp [allowedCofactors, Finset.mem_filter, Finset.mem_Icc, and_assoc]

/-- The allowed cofactors really are cofactors of denominators in the window. -/
theorem allowedCofactors_window {a M p j : ℕ} (hj : j ∈ allowedCofactors a M p) :
    a ≤ p * j ∧ p * j ≤ M := by
  rw [mem_allowedCofactors] at hj
  exact ⟨hj.2, by
    have := hj.1.2
    calc p * j ≤ p * (M / p) := Nat.mul_le_mul_left _ this
      _ ≤ M := Nat.mul_div_le M p⟩

/-- The allowed cofactors all divide `L_{N_p}`. -/
theorem allowedCofactors_dvd_lcm {a M p j : ℕ} (hj : j ∈ allowedCofactors a M p) :
    j ∣ lcmUpto (height M p) := by
  rw [mem_allowedCofactors] at hj
  exact dvd_lcmUpto hj.1.1 hj.1.2

/-! ## 3.  Exact row numerator and row mass -/

/-- The exact integer row numerator `T_p = ∑_j ε_{pj} · L_N / j`, taken over an arbitrary finite
set `J` of cofactors (in the application `J = allowedCofactors a M p`) and at height `N`. -/
def rowNumerator (N p : ℕ) (J : Finset ℕ) (ε : ℕ → Bool) : ℕ :=
  ∑ j ∈ J, if ε (p * j) then lcmUpto N / j else 0

/-- The exact rational row mass `∑_j ε_{pj} / (p j)`. -/
def rowMass (p : ℕ) (J : Finset ℕ) (ε : ℕ → Bool) : ℚ :=
  ∑ j ∈ J, if ε (p * j) then (1 : ℚ) / (p * j) else 0

/-- **Exact row identity.**  `∑_j ε_{pj}/(p j) = T_p / (p L_N)`, for any cofactor set all of whose
members are in `[1, N]`. -/
theorem rowMass_eq_div {N p : ℕ} {J : Finset ℕ} {ε : ℕ → Bool} (hp : 0 < p)
    (hJ : ∀ j ∈ J, 1 ≤ j ∧ j ≤ N) :
    rowMass p J ε = (rowNumerator N p J ε : ℚ) / (p * lcmUpto N) := by
  have hL : (0:ℚ) < (lcmUpto N : ℚ) := by exact_mod_cast lcmUpto_pos N
  have hp' : (0:ℚ) < (p : ℚ) := by exact_mod_cast hp
  rw [rowNumerator, rowMass, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro j hj
  obtain ⟨hj1, hj2⟩ := hJ j hj
  have hjd : j ∣ lcmUpto N := dvd_lcmUpto hj1 hj2
  have hjpos : (0:ℚ) < (j:ℚ) := by exact_mod_cast hj1
  by_cases h : ε (p * j)
  · simp only [h, if_true]
    have : ((lcmUpto N / j : ℕ) : ℚ) = (lcmUpto N : ℚ) / (j : ℚ) := by
      rw [Nat.cast_div hjd (by positivity)]
    rw [this]
    field_simp
  · simp [h]

/-! ## 4.  Denominator entry ⇔ divisibility of the row numerator -/

/-- A rational has reduced denominator dividing `L` exactly when it is an integer multiple of
`1 / L`. -/
theorem den_dvd_iff {q : ℚ} {L : ℕ} (hL : 0 < L) : q.den ∣ L ↔ ∃ k : ℤ, q = (k : ℚ) / L := by
  constructor
  · rintro ⟨c, hc⟩
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · simp [h] at hc; omega
      · exact h
    refine ⟨q.num * c, ?_⟩
    have hq : q * (q.den : ℚ) = (q.num : ℚ) := Rat.mul_den_eq_num q
    have hL' : (L : ℚ) ≠ 0 := by positivity
    rw [eq_div_iff hL']
    push_cast [hc]
    rw [← mul_assoc, hq]
  · rintro ⟨k, rfl⟩
    have := Rat.den_dvd k (L : ℤ)
    rw [Rat.divInt_eq_div] at this
    exact_mod_cast this

/-- **Denominator-entry equivalence.**  For a row with cofactors in `[1, N]`, the prime `p` is
removed from the row denominator — i.e. the row mass is an integral multiple of `1 / L_N` —
**iff** `p` divides the exact integer row numerator `T_p`. -/
theorem prime_removed_iff_dvd_rowNumerator {N p : ℕ} {J : Finset ℕ} {ε : ℕ → Bool} (hp : 0 < p)
    (hJ : ∀ j ∈ J, 1 ≤ j ∧ j ≤ N) :
    (∃ k : ℤ, rowMass p J ε = (k : ℚ) / lcmUpto N) ↔ p ∣ rowNumerator N p J ε := by
  have hL : (0:ℚ) < (lcmUpto N : ℚ) := by exact_mod_cast lcmUpto_pos N
  have hp' : (0:ℚ) < (p : ℚ) := by exact_mod_cast hp
  rw [rowMass_eq_div hp hJ]
  constructor
  · rintro ⟨k, hk⟩
    rw [div_eq_div_iff (by positivity) (by positivity)] at hk
    have hcancel : (rowNumerator N p J ε : ℚ) = (k : ℚ) * p :=
      mul_right_cancel₀ (ne_of_gt hL) (by linarith [hk] )
    have hz : ((rowNumerator N p J ε : ℤ) : ℚ) = ((k * p : ℤ) : ℚ) := by push_cast; exact hcancel
    have hzz : (rowNumerator N p J ε : ℤ) = k * p := by exact_mod_cast hz
    have hdvd : (p : ℤ) ∣ (rowNumerator N p J ε : ℤ) := ⟨k, by rw [hzz]; ring⟩
    exact_mod_cast hdvd
  · rintro ⟨c, hc⟩
    refine ⟨(c : ℤ), ?_⟩
    rw [hc]
    push_cast
    field_simp

/-! ## 5.  The carry -/

/-- The carry `k_p = T_p / p` of a row whose prime has been removed. -/
def carry (N p : ℕ) (J : Finset ℕ) (ε : ℕ → Bool) : ℕ := rowNumerator N p J ε / p

/-- **Exact carry identity.**  If `p ∣ T_p` then `∑_j ε_{pj}/(p j) = k_p / L_N`. -/
theorem rowMass_eq_carry_div {N p : ℕ} {J : Finset ℕ} {ε : ℕ → Bool} (hp : 0 < p)
    (hJ : ∀ j ∈ J, 1 ≤ j ∧ j ≤ N) (hdvd : p ∣ rowNumerator N p J ε) :
    rowMass p J ε = (carry N p J ε : ℚ) / lcmUpto N := by
  obtain ⟨c, hc⟩ := hdvd
  have hcar : carry N p J ε = c := by
    rw [carry, hc, Nat.mul_div_cancel_left _ hp]
  have hL : (0:ℚ) < (lcmUpto N : ℚ) := by exact_mod_cast lcmUpto_pos N
  have hp' : (0:ℚ) < (p : ℚ) := by exact_mod_cast hp
  rw [rowMass_eq_div hp hJ, hcar, hc]
  push_cast
  field_simp

/-! ## 6.  Height classes and the exact aggregation identity -/

/-- The height class `𝒫_N = {p ∈ P : ⌊M/p⌋ = N}` of the current upper-gap prime set `P`. -/
def heightClass (M : ℕ) (P : Finset ℕ) (N : ℕ) : Finset ℕ := P.filter (fun p => height M p = N)

/-- The set of heights actually occurring in `P`. -/
def heights (M : ℕ) (P : Finset ℕ) : Finset ℕ := P.image (height M)

/-- The aggregate carry `K_N = ∑_{p ∈ 𝒫_N} k_p` at height `N`. -/
def aggregateCarry (M : ℕ) (P : Finset ℕ) (J : ℕ → Finset ℕ) (ε : ℕ → Bool) (N : ℕ) : ℕ :=
  ∑ p ∈ heightClass M P N, carry N p (J p) ε

/-- **Exact height aggregation.**  With `N_p = ⌊M/p⌋`, `L_N = lcm(1,…,N)`, `k_p = T_p/p` and
`K_N = ∑_{⌊M/p⌋ = N} k_p`,

`∑_{p ∈ P} ∑_j ε_{pj}/(p j) = ∑_N K_N / L_N`,

where `P` is the (finite) set of upper-gap prime rows, each row uses its own actual cofactor set
`J p` (all members in `[1, ⌊M/p⌋]`), and every row has its prime removed (`p ∣ T_p`). -/
theorem carry_height_aggregation {M : ℕ} {P : Finset ℕ} {J : ℕ → Finset ℕ} {ε : ℕ → Bool}
    (hpos : ∀ p ∈ P, 0 < p)
    (hJ : ∀ p ∈ P, ∀ j ∈ J p, 1 ≤ j ∧ j ≤ height M p)
    (hdvd : ∀ p ∈ P, p ∣ rowNumerator (height M p) p (J p) ε) :
    ∑ p ∈ P, rowMass p (J p) ε
      = ∑ N ∈ heights M P, (aggregateCarry M P J ε N : ℚ) / lcmUpto N := by
  have hrow : ∀ p ∈ P, rowMass p (J p) ε
      = (carry (height M p) p (J p) ε : ℚ) / lcmUpto (height M p) := by
    intro p hp
    exact rowMass_eq_carry_div (hpos p hp) (hJ p hp) (hdvd p hp)
  rw [Finset.sum_congr rfl hrow]
  have hmaps : ∀ p ∈ P, height M p ∈ heights M P := by
    intro p hp; exact Finset.mem_image_of_mem _ hp
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun p => (carry (height M p) p (J p) ε : ℚ) / lcmUpto (height M p))]
  refine Finset.sum_congr rfl ?_
  intro N _
  rw [aggregateCarry, Nat.cast_sum, Finset.sum_div, heightClass]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have : height M p = N := (Finset.mem_filter.1 hp).2
  rw [this]

/-! ## 7.  Counterfixture: the cofactor range may not be silently completed -/

/-- **COUNTERFIXTURE.**  Replacing the actual (selected / truncated) cofactor range by the full
range `1, …, N` is *not* harmless: here `N = 2`, `p = 5`, all bits on, `J = {1}` versus
`J' = {1,2}`, and the two exact row numerators differ. -/
theorem rowNumerator_range_substitution_counterfixture :
    rowNumerator 2 5 {1} (fun _ => true) ≠ rowNumerator 2 5 (Finset.Icc 1 2) (fun _ => true) := by
  decide

/-- The two row masses differ as well, so the substitution changes the exact rational mass. -/
theorem rowMass_range_substitution_counterfixture :
    rowMass 5 {1} (fun _ => true) ≠ rowMass 5 (Finset.Icc 1 2) (fun _ => true) := by
  norm_num [rowMass, show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) from rfl]

end UpperGap
end ResearchBankV6
end Erdos287
