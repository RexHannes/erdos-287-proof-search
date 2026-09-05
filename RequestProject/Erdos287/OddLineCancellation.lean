import Mathlib
import RequestProject.Erdos287.Reflection

/-!
# Erdős #287 effectivity — the odd line cancellations (§12, §13)

```
FULL ODD DISCRETE CANCELLATION    : KERNEL-PROVED
CONTINUOUS COEFFICIENT CONVOLUTION: KERNEL-PROVED
DOWNSTREAM CANCELLATION           : KERNEL-PROVED (conditional, as requested)
```

## §12  The discrete line

After the substitution `w = d·n` the coefficient attached to `w` is

    [B(w) − B1] · ∑_{d ∣ w, 2∤d} μ(d),

which vanishes for **every** `w`: if the odd part of `w` exceeds `1` the Möbius sum is
`0`, and otherwise `w` is a power of `2` and `B(w) − B1 = 0` (special case A of §9).
Hence the compactly supported `W`-sum vanishes identically.

## §13  The continuous coefficient

With `mOdd(n) = μ(n)1_{2∤n}/n` and the multiplicative `r` determined by
`r(pʲ) = −1/(pʲ(p−1))` at odd primes (and `r(2ʲ) = 0`), Dirichlet convolution gives

    μ(n)1_{2∤n}/φ(n) = (mOdd ⋆ r)(n)      (`muOddOverPhi_eq_mOdd_conv_r`).

The analytic statement `∑ mOdd = 0` is **not** proved here; the downstream
cancellation is proved *conditionally* on it (and on the Cauchy-product identity),
exactly as requested.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos287
namespace Effectivity

/-! ## §12  Full odd discrete line cancellation -/

/-- Only divisors of the odd radical contribute to an odd-divisor Möbius sum. -/
theorem sum_odd_divisors_moebius {w : ℕ} (hw : w ≠ 0) :
    (∑ d ∈ w.divisors with ¬ (2 ∣ d), moebius d) = ∑ d ∈ (radOdd w).divisors, moebius d := by
  classical
  refine (Finset.sum_subset ?_ ?_).symm
  · intro d hd
    rw [Nat.mem_divisors] at hd
    exact Finset.mem_filter.2
      ⟨Nat.mem_divisors.2 ⟨hd.1.trans (radOdd_dvd w), hw⟩, odd_of_dvd_radOdd hd.1⟩
  · intro d hd hnot
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdw, _⟩, hodd⟩ := hd
    by_cases hsq : Squarefree d
    · exact absurd (Nat.mem_divisors.2
        ⟨dvd_radOdd_of_odd_squarefree hw hdw hsq hodd, (radOdd_pos w).ne'⟩) hnot
    · exact moebius_eq_zero_of_not_squarefree hsq

/-- **`oddLine_coefficient_zero`.**  `KERNEL-PROVED`.  The coefficient attached to `w` after
the substitution `w = d·n` vanishes for every `w`:

    [B(w) − B1] · ∑_{d ∣ w, 2∤d} μ(d) = 0. -/
theorem oddLine_coefficient_zero (B1 : ℚ) (w : ℕ) :
    (B B1 w - B1) * ∑ d ∈ w.divisors with ¬ (2 ∣ d), ((moebius d : ℤ) : ℚ) = 0 := by
  classical
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.2 (radOdd_pos w).ne') with h1 | h1
  · -- `rad_odd(w) = 1`: the source coefficient itself vanishes (special case A)
    rw [radOdd_one_source_vanishes B1 h1.symm, zero_mul]
  · -- `rad_odd(w) > 1`: the odd Möbius sum vanishes
    have : (∑ d ∈ w.divisors with ¬ (2 ∣ d), ((moebius d : ℤ) : ℚ)) = 0 := by
      have h := sum_odd_divisors_moebius (w := w) hw
      have h2 := sum_moebius_divisors_eq_zero h1
      rw [h2] at h
      calc (∑ d ∈ w.divisors with ¬ (2 ∣ d), ((moebius d : ℤ) : ℚ))
          = (((∑ d ∈ w.divisors with ¬ (2 ∣ d), moebius d : ℤ) : ℚ)) := by push_cast; ring
        _ = 0 := by rw [h]; norm_num
    rw [this, mul_zero]

/-- **`oddLine_Wsum_zero`.**  `KERNEL-PROVED`.  Passing to the compactly supported `W`-sum:
the whole odd line cancels for any finite window and any weight. -/
theorem oddLine_Wsum_zero (B1 : ℚ) (Wt : ℕ → ℚ) (S : Finset ℕ) :
    ∑ w ∈ S, ((B B1 w - B1) * ∑ d ∈ w.divisors with ¬ (2 ∣ d), ((moebius d : ℤ) : ℚ)) * Wt w
      = 0 := by
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [oddLine_coefficient_zero B1 w, zero_mul]

/-! ## §13  The continuous coefficient convolution -/

/-- `mOdd(n) = μ(n)·1_{2∤n}/n`. -/
noncomputable def mOdd : ArithmeticFunction ℝ :=
  ⟨fun n => if 2 ∣ n then 0 else (moebius n : ℝ) / (n : ℝ), by simp⟩

/-- The multiplicative `r` with `r(pʲ) = −1/(pʲ(p−1))` at odd primes and `r(2ʲ) = 0`. -/
noncomputable def rConv : ArithmeticFunction ℝ :=
  ⟨fun n => if 2 ∣ n then 0
    else (-1) ^ n.primeFactors.card / ((n : ℝ) * ∏ p ∈ n.primeFactors, ((p : ℝ) - 1)), by simp⟩

/-- `μ(n)·1_{2∤n}/φ(n)`. -/
noncomputable def muOddOverPhi : ArithmeticFunction ℝ :=
  ⟨fun n => if 2 ∣ n then 0 else (moebius n : ℝ) / (n.totient : ℝ), by simp⟩

@[simp] lemma mOdd_apply (n : ℕ) :
    mOdd n = if 2 ∣ n then 0 else (moebius n : ℝ) / (n : ℝ) := rfl

@[simp] lemma rConv_apply (n : ℕ) :
    rConv n = if 2 ∣ n then 0
      else (-1) ^ n.primeFactors.card / ((n : ℝ) * ∏ p ∈ n.primeFactors, ((p : ℝ) - 1)) := rfl

@[simp] lemma muOddOverPhi_apply (n : ℕ) :
    muOddOverPhi n = if 2 ∣ n then 0 else (moebius n : ℝ) / (n.totient : ℝ) := rfl

lemma isMultiplicative_mOdd : mOdd.IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp, ?_⟩
  intro m n hm hn hmn
  by_cases h2 : 2 ∣ m * n
  · rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h | h <;> simp [h2, h]
  · have hm2 : ¬ 2 ∣ m := fun h => h2 (h.mul_right n)
    have hn2 : ¬ 2 ∣ n := fun h => h2 (Dvd.dvd.mul_left h m)
    rw [mOdd_apply, mOdd_apply, mOdd_apply, if_neg h2, if_neg hm2, if_neg hn2,
      isMultiplicative_moebius.map_mul_of_coprime hmn]
    push_cast
    field_simp

lemma isMultiplicative_rConv : rConv.IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp, ?_⟩
  intro m n hm hn hmn
  by_cases h2 : 2 ∣ m * n
  · rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h | h <;> simp [h2, h]
  · have hm2 : ¬ 2 ∣ m := fun h => h2 (h.mul_right n)
    have hn2 : ¬ 2 ∣ n := fun h => h2 (Dvd.dvd.mul_left h m)
    have hpf : (m * n).primeFactors = m.primeFactors ∪ n.primeFactors :=
      Nat.primeFactors_mul hm hn
    have hdisj : Disjoint m.primeFactors n.primeFactors := hmn.disjoint_primeFactors
    rw [rConv_apply, rConv_apply, rConv_apply, if_neg h2, if_neg hm2, if_neg hn2, hpf,
      Finset.card_union_of_disjoint hdisj, Finset.prod_union hdisj, pow_add]
    push_cast
    field_simp

lemma isMultiplicative_muOddOverPhi : muOddOverPhi.IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp, ?_⟩
  intro m n hm hn hmn
  by_cases h2 : 2 ∣ m * n
  · rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h | h <;> simp [h2, h]
  · have hm2 : ¬ 2 ∣ m := fun h => h2 (h.mul_right n)
    have hn2 : ¬ 2 ∣ n := fun h => h2 (Dvd.dvd.mul_left h m)
    rw [muOddOverPhi_apply, muOddOverPhi_apply, muOddOverPhi_apply, if_neg h2, if_neg hm2,
      if_neg hn2, isMultiplicative_moebius.map_mul_of_coprime hmn, Nat.totient_mul hmn]
    push_cast
    field_simp

/-- The convolution on a prime power, written as a sum over exponents. -/
lemma conv_prime_pow (f g : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    (f * g) (p ^ j) = ∑ i ∈ Finset.range (j + 1), f (p ^ i) * g (p ^ (j - i)) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b),
    Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [Nat.pow_div (by omega) hp.pos]

lemma rConv_prime_pow {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (j : ℕ) (hj : 1 ≤ j) :
    rConv (p ^ j) = -1 / ((p : ℝ) ^ j * ((p : ℝ) - 1)) := by
  have hodd : ¬ 2 ∣ p ^ j := by
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
    exact h2 (((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 this).symm)
  rw [rConv_apply, if_neg hodd, Nat.primeFactors_prime_pow (by omega) hp]
  simp

lemma mOdd_prime_pow_eq_zero {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : 2 ≤ j) :
    mOdd (p ^ j) = 0 := by
  rw [mOdd_apply]
  split
  · rfl
  · rw [moebius_eq_zero_of_not_squarefree]
    · simp
    · intro hsq
      have := hsq p ⟨p ^ (j - 2), by rw [← pow_two, ← pow_add]; congr 1; omega⟩
      exact hp.one_lt.ne' (Nat.isUnit_iff.1 this)

/-- **`muOddOverPhi_eq_mOdd_conv_r`.**  `KERNEL-PROVED`.  The prime-power local identity
gives the Dirichlet convolution identity

    μ(n)·1_{2∤n}/φ(n) = (mOdd ⋆ r)(n). -/
theorem muOddOverPhi_eq_mOdd_conv_r : muOddOverPhi = mOdd * rConv := by
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ isMultiplicative_muOddOverPhi _
    (isMultiplicative_mOdd.mul isMultiplicative_rConv)]
  intro p j hp
  rw [conv_prime_pow _ _ hp j]
  rcases eq_or_ne p 2 with rfl | h2
  · -- `p = 2`
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · rw [muOddOverPhi_apply, if_pos (dvd_pow_self 2 (by omega))]
      refine (Finset.sum_eq_zero fun i hi => ?_).symm
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [rConv_apply, if_pos (dvd_pow_self 2 (by simp; omega))]
        ring
      · rw [mOdd_apply, if_pos (dvd_pow_self 2 (by omega))]
        ring
  · -- `p` odd
    have hpodd : ¬ 2 ∣ p ^ j ∨ j = 0 := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · right; rfl
      · left
        intro h
        exact h2 (((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
          (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h)).symm)
    have hp1 : ((p : ℝ) - 1) ≠ 0 := by
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
      intro h; linarith [sub_eq_zero.1 h]
    have hp0 : (p : ℝ) ≠ 0 := by
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
      intro h; rw [h] at this; linarith
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    -- reduce the convolution sum to the terms `i = 0, 1`
    have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (j + 1) := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rw [Finset.mem_range]
      rcases hi with rfl | rfl <;> omega
    have hzero : ∀ i ∈ Finset.range (j + 1), i ∉ ({0, 1} : Finset ℕ) →
        mOdd (p ^ i) * rConv (p ^ (j - i)) = 0 := by
      intro i _ hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      push_neg at hi
      rw [mOdd_prime_pow_eq_zero hp (by omega), zero_mul]
    rw [← Finset.sum_subset hsub hzero, Finset.sum_insert (by simp), Finset.sum_singleton]
    have hodd : ¬ 2 ∣ p ^ j := by
      rcases hpodd with h | h
      · exact h
      · omega
    have hmu1 : mOdd (p ^ 1) = -1 / (p : ℝ) := by
      have hnd : ¬ 2 ∣ p ^ 1 := by
        rw [pow_one]
        intro h
        exact h2 (((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm)
      rw [mOdd_apply, if_neg hnd, pow_one, moebius_apply_prime hp]
      push_cast
      ring
    have hm1 : mOdd 1 = 1 := isMultiplicative_mOdd.map_one
    have hr1 : rConv 1 = 1 := isMultiplicative_rConv.map_one
    have hmp : mOdd p = -1 / (p : ℝ) := by simpa using hmu1
    rw [muOddOverPhi_apply, if_neg hodd]
    rcases eq_or_lt_of_le (show 1 ≤ j from hj) with hj1 | hj2
    · -- `j = 1`
      have hrp : rConv p = -1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
        simpa using rConv_prime_pow hp h2 1 (le_refl 1)
      have hphi : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
        have h1p : 1 ≤ p := hp.one_lt.le
        push_cast [Nat.cast_sub h1p]
        ring
      have hpnd : ¬ (2 : ℕ) ∣ p := by
        intro h
        exact h2 (((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm)
      rw [← hj1]
      norm_num
      simp only [if_neg hpnd, hp.primeFactors, Finset.prod_singleton, Finset.card_singleton]
      rw [Nat.totient_prime hp, moebius_apply_prime hp, hphi]
      field_simp
      ring
    · -- `j ≥ 2`
      have hjj : 2 ≤ j := hj2
      have hmu0 : moebius (p ^ j) = 0 :=
        moebius_eq_zero_of_not_squarefree (by
          intro hsq
          have := hsq p ⟨p ^ (j - 2), by rw [← pow_two, ← pow_add]; congr 1; omega⟩
          exact hp.one_lt.ne' (Nat.isUnit_iff.1 this))
      have hpj : (p : ℝ) ^ j = (p : ℝ) ^ (j - 1) * (p : ℝ) := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hmu0]
      simp only [Nat.sub_zero, pow_zero, hm1, one_mul, Int.cast_zero, zero_div, pow_one, hmp]
      rw [rConv_prime_pow hp h2 j (by omega), rConv_prime_pow hp h2 (j - 1) (by omega), hpj]
      field_simp
      ring

/-! ### The conditional downstream cancellation -/

/-- **`downstream_cancellation_of_sum_mOdd_zero`.**  `KERNEL-PROVED` as an implication.
Conditional on the analytic input `∑ mOdd = 0` (and on the Cauchy-product identity for the
convolution, which is *not* asserted here):

    ∑ μ(d)·1_{2∤d}·(1/φ(d) − B1/d) = 0. -/
theorem downstream_cancellation_of_sum_mOdd_zero (B1 : ℝ)
    (hmul : ∑' n : ℕ, ((mOdd * rConv) n) = (∑' n : ℕ, mOdd n) * ∑' n : ℕ, rConv n)
    (h0 : ∑' n : ℕ, mOdd n = 0)
    (hs1 : Summable fun n : ℕ => muOddOverPhi n)
    (hs2 : Summable fun n : ℕ => mOdd n) :
    ∑' n : ℕ, (muOddOverPhi n - B1 * mOdd n) = 0 := by
  have hphi : ∑' n : ℕ, muOddOverPhi n = 0 := by
    rw [show (fun n : ℕ => muOddOverPhi n) = fun n : ℕ => (mOdd * rConv) n by
      rw [muOddOverPhi_eq_mOdd_conv_r], hmul, h0, zero_mul]
  rw [Summable.tsum_sub hs1 (hs2.mul_left B1), hphi, tsum_mul_left, h0]
  ring

end Effectivity
end Erdos287
