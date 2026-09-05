import Mathlib
import RequestProject.Erdos287.OddHalfDivisor

/-!
# Erdős #287 effectivity — half-divisor reflection (§9)

```
HALF-DIVISOR REFLECTION (strict form)     : KERNEL-PROVED
HALF-DIVISOR REFLECTION (non-strict form) : KERNEL-PROVED
SPECIAL CASE A  (r = 1 ⇒ B(w) − B1 = 0)   : KERNEL-PROVED
SPECIAL CASE B  (μ(w) = +1 ⇒ H_1^odd = 0) : KERNEL-PROVED
```

With `r = rad_odd(w)` and `r > 1`,

    H_c^odd(w) =  μ(r) ∑_{e ∣ r,  w e² >  c r²} μ(e)
               = −μ(r) ∑_{e ∣ r,  w e² ≤  c r²} μ(e).

The boundary is **strict on one side and non-strict on the other**: the two forms
are complementary halves of `∑_{e ∣ r} μ(e) = 0`, so the case `w e² = c r²`
belongs to the second sum only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos287
namespace Effectivity

/-! ## §9.1  Reduction of the chart to the odd radical -/

lemma w_ne_zero_of_one_lt_radOdd {w : ℕ} (hr : 1 < radOdd w) : w ≠ 0 := by
  rintro rfl
  simp [radOdd, oddPrimeFactors] at hr

/-- Only divisors of the odd radical contribute to `H_c^odd`. -/
theorem Hodd_eq_sum_radOdd_divisors {c w : ℕ} (hw : w ≠ 0) :
    Hodd c w = ∑ d ∈ (radOdd w).divisors with (c * d ^ 2 < w), moebius d := by
  classical
  refine (Finset.sum_subset ?_ ?_).symm
  · intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdr, _⟩, hlt⟩ := hd
    refine Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨hdr.trans (radOdd_dvd w), hw⟩, ?_, hlt⟩
    exact odd_of_dvd_radOdd hdr
  · intro d hd hnot
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdw, _⟩, hodd, hlt⟩ := hd
    by_cases hsq : Squarefree d
    · exact absurd (Finset.mem_filter.2
        ⟨Nat.mem_divisors.2 ⟨dvd_radOdd_of_odd_squarefree hw hdw hsq hodd,
          (radOdd_pos w).ne'⟩, hlt⟩) hnot
    · exact moebius_eq_zero_of_not_squarefree hsq

/-! ## §9.2  The reflection `d ↦ r/d` -/

/-- For `e ∣ r` with `r` squarefree, `μ(r/e) = μ(r)·μ(e)`. -/
lemma moebius_div_of_squarefree {r e : ℕ} (hr : Squarefree r) (he : e ∣ r) :
    moebius (r / e) = moebius r * moebius e := by
  obtain ⟨f, rfl⟩ := he
  have hcop : Nat.Coprime e f := (Nat.squarefree_mul_iff.1 hr).1
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (by rintro rfl; simp at hr)),
    isMultiplicative_moebius.map_mul_of_coprime hcop]
  have : moebius e * moebius e = 1 := by
    have hsq : Squarefree e := (Nat.squarefree_mul_iff.1 hr).2.1
    have := moebius_sq_eq_one_of_squarefree hsq
    nlinarith [this]
  calc moebius f = 1 * moebius f := (one_mul _).symm
    _ = (moebius e * moebius e) * moebius f := by rw [this]
    _ = moebius e * moebius f * moebius e := by ring

/-- **`halfDivisor_reflection_strict`.**  `KERNEL-PROVED`.  For `r = rad_odd(w) > 1`,

    H_c^odd(w) = μ(r) ∑_{e ∣ r, w e² > c r²} μ(e). -/
theorem halfDivisor_reflection_strict {c w : ℕ} (hr : 1 < radOdd w) :
    Hodd c w
      = moebius (radOdd w) * ∑ e ∈ (radOdd w).divisors with (c * radOdd w ^ 2 < w * e ^ 2),
          moebius e := by
  classical
  set r := radOdd w with hrdef
  have hw : w ≠ 0 := w_ne_zero_of_one_lt_radOdd hr
  have hr0 : r ≠ 0 := (radOdd_pos w).ne'
  have hrsq : Squarefree r := radOdd_squarefree w
  rw [Hodd_eq_sum_radOdd_divisors hw]
  rw [Finset.sum_filter, Finset.sum_filter, Finset.mul_sum]
  rw [← Nat.sum_div_divisors r (fun d => if c * d ^ 2 < w then moebius d else 0)]
  refine Finset.sum_congr rfl fun e he => ?_
  have hedvd : e ∣ r := (Nat.mem_divisors.1 he).1
  have he0 : 0 < e := Nat.pos_of_mem_divisors he
  obtain ⟨f, hrf⟩ := id hedvd
  have hrde : r / e = f := by rw [hrf]; exact Nat.mul_div_cancel_left f he0
  have hcond : (c * (r / e) ^ 2 < w) ↔ (c * r ^ 2 < w * e ^ 2) := by
    rw [hrde, hrf, show c * (e * f) ^ 2 = c * f ^ 2 * e ^ 2 by ring]
    exact (Nat.mul_lt_mul_right (by positivity : 0 < e ^ 2)).symm
  rw [moebius_div_of_squarefree hrsq hedvd]
  by_cases hlt : c * r ^ 2 < w * e ^ 2
  · rw [if_pos (hcond.2 hlt), if_pos hlt]
  · rw [if_neg (fun h => hlt (hcond.1 h)), if_neg hlt, mul_zero]

/-- `∑_{e ∣ r} μ(e) = 0` for `r > 1`. -/
lemma sum_moebius_divisors_eq_zero {r : ℕ} (hr : 1 < r) : ∑ e ∈ r.divisors, moebius e = 0 := by
  have h := coe_mul_zeta_apply (f := (moebius : ArithmeticFunction ℤ)) (x := r)
  rw [moebius_mul_coe_zeta] at h
  rw [← h, one_apply, if_neg (by omega)]

/-- **`halfDivisor_reflection_nonstrict`.**  `KERNEL-PROVED`.  The complementary form,

    H_c^odd(w) = −μ(r) ∑_{e ∣ r, w e² ≤ c r²} μ(e),

with the boundary case `w e² = c r²` belonging to *this* sum. -/
theorem halfDivisor_reflection_nonstrict {c w : ℕ} (hr : 1 < radOdd w) :
    Hodd c w
      = - moebius (radOdd w) * ∑ e ∈ (radOdd w).divisors with (w * e ^ 2 ≤ c * radOdd w ^ 2),
          moebius e := by
  classical
  set r := radOdd w with hrdef
  have hr1 : 1 < r := hr
  have hsplit :
      (∑ e ∈ r.divisors with (c * r ^ 2 < w * e ^ 2), moebius e)
        + ∑ e ∈ r.divisors with ¬ (c * r ^ 2 < w * e ^ 2), moebius e = 0 := by
    rw [Finset.sum_filter_add_sum_filter_not]
    exact sum_moebius_divisors_eq_zero hr1
  have hnot : ∀ e : ℕ, ¬ (c * r ^ 2 < w * e ^ 2) ↔ (w * e ^ 2 ≤ c * r ^ 2) := by
    intro e; omega
  rw [halfDivisor_reflection_strict (c := c) hr]
  have : (∑ e ∈ r.divisors with (c * r ^ 2 < w * e ^ 2), moebius e)
      = - ∑ e ∈ r.divisors with (w * e ^ 2 ≤ c * r ^ 2), moebius e := by
    rw [show (∑ e ∈ r.divisors with (w * e ^ 2 ≤ c * r ^ 2), moebius e)
        = ∑ e ∈ r.divisors with ¬ (c * r ^ 2 < w * e ^ 2), moebius e from
      Finset.sum_congr (by ext e; simp [hnot e]) fun _ _ => rfl]
    omega
  rw [this]; ring

/-! ## §9.3  Special case A : `r = 1` -/

lemma oddPrimeFactors_eq_empty_of_radOdd_one {w : ℕ} (h : radOdd w = 1) :
    oddPrimeFactors w = ∅ := by
  by_contra hne
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.2 hne
  have hdvd : p ∣ radOdd w := Finset.dvd_prod_of_mem _ hp
  rw [h] at hdvd
  exact (oddPrimeFactors_prime hp).one_lt.ne' (Nat.dvd_one.1 hdvd)

/-- **`radOdd_one_source_vanishes`** (special case A).  `KERNEL-PROVED`.
If `rad_odd(w) = 1` then the source coefficient `B(w) − B1` vanishes. -/
theorem radOdd_one_source_vanishes (B1 : ℚ) {w : ℕ} (h : radOdd w = 1) :
    B B1 w - B1 = 0 := by
  rw [B, B0, oddPrimeFactors_eq_empty_of_radOdd_one h, Finset.prod_empty, mul_one, sub_self]

/-! ## §9.4  Special case B : `c = 1`, `w` odd squarefree with `μ(w) = +1` -/

lemma radOdd_of_odd_squarefree {w : ℕ} (hodd : ¬ (2 ∣ w)) (hsq : Squarefree w) : radOdd w = w := by
  have h2 : (2 : ℕ) ∉ w.primeFactors := fun h => hodd (Nat.dvd_of_mem_primeFactors h)
  rw [radOdd, oddPrimeFactors, Finset.erase_eq_of_notMem h2,
    Nat.prod_primeFactors_of_squarefree hsq]

/-- **`halfDivisor_vanishes_of_moebius_one`** (special case B).  `KERNEL-PROVED`.
For `w` odd and squarefree with `μ(w) = +1`, `H_1^odd(w) = 0`. -/
theorem halfDivisor_vanishes_of_moebius_one {w : ℕ} (hodd : ¬ (2 ∣ w)) (hsq : Squarefree w)
    (hmu : moebius w = 1) : Hodd 1 w = 0 := by
  classical
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.2 hsq.ne_zero) with h1 | h1
  · -- `w = 1`
    rw [Hodd, ← h1]
    norm_num [Finset.filter_singleton]
  · have hrad : radOdd w = w := radOdd_of_odd_squarefree hodd hsq
    have hr : 1 < radOdd w := by rw [hrad]; exact h1
    have hw0 : 0 < w := hsq.ne_zero.bot_lt
    -- the non-strict reflection, with `μ(w) = 1`
    have hrefl := halfDivisor_reflection_nonstrict (c := 1) hr
    rw [hrad, hmu] at hrefl
    -- there is no divisor `e` of `w` with `w·e² = w²`, since `w` is squarefree and `w > 1`
    have hbdry : ∀ e ∈ w.divisors, (w * e ^ 2 ≤ 1 * w ^ 2) ↔ (1 * e ^ 2 < w) := by
      intro e he
      have hedvd : e ∣ w := (Nat.mem_divisors.1 he).1
      have hne : w * e ^ 2 ≠ 1 * w ^ 2 := by
        intro hEq
        have he2 : e ^ 2 = w := by
          have : w * e ^ 2 = w * w := by simpa [pow_two] using hEq
          exact Nat.eq_of_mul_eq_mul_left hw0 this
        have : ¬ Squarefree w := by
          rw [← he2]
          intro hcon
          have := hcon e (by rw [pow_two])
          have he1 : e = 1 := Nat.isUnit_iff.1 this
          rw [he1] at he2
          omega
        exact this hsq
      constructor
      · intro h
        have : w * e ^ 2 < 1 * w ^ 2 := lt_of_le_of_ne h hne
        nlinarith [hw0]
      · intro h
        nlinarith [hw0]
    have hset : (w.divisors.filter (fun e => w * e ^ 2 ≤ 1 * w ^ 2))
        = w.divisors.filter (fun e => 1 * e ^ 2 < w) := by
      apply Finset.filter_congr
      intro e he
      simpa using hbdry e he
    rw [hset] at hrefl
    -- and the chart itself is the same sum, since every divisor of odd `w` is odd
    have hchart : Hodd 1 w = ∑ e ∈ w.divisors with (1 * e ^ 2 < w), moebius e := by
      rw [Hodd]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      apply Finset.filter_congr
      intro e he
      have hedvd : e ∣ w := (Nat.mem_divisors.1 he).1
      have : ¬ (2 ∣ e) := fun h => hodd (h.trans hedvd)
      simp [this]
    rw [hchart] at hrefl ⊢
    linarith [hrefl]

end Effectivity
end Erdos287
