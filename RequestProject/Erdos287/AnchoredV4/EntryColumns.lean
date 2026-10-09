import RequestProject.Erdos287.AnchoredV4.ConditionalExactEndgame

/-!
# Anchored V4 — exact column arithmetic of the transition problem

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

This module converts the *analytic-looking* descent condition

`den (S − ∑_{n ∈ E} 1/n) ∣ 2 L h'`

into an **exact integer congruence** on the chosen positions, which is the honest finite form of
the global transition problem:

`numerator_at P S − ∑_{n ∈ E} (P / n) ≡ 0 (mod r)`,  where `P = 2 L h`, `P = r · P'`.

The two principal results are

* `den_dvd_quotient_iff` — the exact equivalence between a smaller denominator lattice and an
  integer divisibility of the numerator;
* `descent_congruence_iff` — its application to one descent move, so that the descent is a finite
  linear congruence over the physical positions;

together with the exact **component splitting** `dvd_mul_iff_of_coprime`, which is the reason the
single congruence modulo `r` decomposes into one constraint per active prime-power component, and
the explicit warning `column_sum_not_rowwise` that solving the global congruence does **not**
require solving it position-block by position-block.
-/

namespace Erdos287
namespace AnchoredV4

/-- The integer numerator of a rational at a common denominator `P` (well defined when
`x.den ∣ P`). -/
noncomputable def numeratorAt (P : ℕ) (x : ℚ) : ℤ := (x * P).num

lemma mul_natCast_eq_numeratorAt {P : ℕ} {x : ℚ} (hx : x.den ∣ P) :
    x * P = (numeratorAt P x : ℚ) := by
  obtain ⟨z, hz⟩ := (den_dvd_iff_mul_natCast_isInt x P).1 hx
  rw [numeratorAt, hz]
  simp

/-- **Exact descent criterion.**  For `P = r * P'` and `x` in the `P` lattice, `x` lies in the
smaller `P'` lattice exactly when `r` divides the numerator of `x` at `P`. -/
theorem den_dvd_quotient_iff {P P' r : ℕ} (hr : 0 < r) (hP : P = r * P') {x : ℚ}
    (hx : x.den ∣ P) : x.den ∣ P' ↔ (r : ℤ) ∣ numeratorAt P x := by
  have hk : x * P = (numeratorAt P x : ℚ) := mul_natCast_eq_numeratorAt hx
  have hr0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne'
  rw [den_dvd_iff_mul_natCast_isInt]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have : x * P = (r : ℚ) * (x * P') := by rw [hP]; push_cast; ring
    rw [hk, hz] at this
    exact_mod_cast this
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have h1 : (r : ℚ) * (x * P') = (numeratorAt P x : ℚ) := by
      rw [← hk, hP]; push_cast; ring
    rw [hz] at h1
    have : (r : ℚ) * (x * P') = (r : ℚ) * (z : ℚ) := by rw [h1]; push_cast; ring
    exact mul_left_cancel₀ hr0 this

/-- **The descent move as a finite linear congruence.**  Omitting the fresh positions `E` from a
word of value `S` lands in the smaller lattice `P'` exactly when the integer congruence holds. -/
theorem descent_congruence_iff {P P' r : ℕ} (hr : 0 < r) (hP : P = r * P') {S : ℚ}
    (hS : S.den ∣ P) {E : Finset ℕ} (hE : ∀ n ∈ E, n ≠ 0 ∧ n ∣ P) (hPne : P ≠ 0) :
    (S - recipSum E).den ∣ P' ↔
      (r : ℤ) ∣ numeratorAt P S - ∑ n ∈ E, (weight P n : ℤ) := by
  have hrec : recipSum E = (∑ n ∈ E, (weight P n : ℚ)) / P := recipSum_eq_weightSum hPne hE
  have hPQ : (P : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hPne
  have hden : (S - recipSum E).den ∣ P := by
    rw [den_dvd_iff_mul_natCast_isInt]
    refine ⟨numeratorAt P S - ∑ n ∈ E, (weight P n : ℤ), ?_⟩
    rw [sub_mul, hrec, div_mul_cancel₀ _ hPQ, mul_natCast_eq_numeratorAt hS]
    push_cast
    ring
  have hnum : numeratorAt P (S - recipSum E) = numeratorAt P S - ∑ n ∈ E, (weight P n : ℤ) := by
    have h1 : (S - recipSum E) * P = ((numeratorAt P S - ∑ n ∈ E, (weight P n : ℤ) : ℤ) : ℚ) := by
      rw [sub_mul, hrec, div_mul_cancel₀ _ hPQ, mul_natCast_eq_numeratorAt hS]
      push_cast
      ring
    rw [numeratorAt, h1]
    exact Rat.num_intCast _
  rw [den_dvd_quotient_iff hr hP hden, hnum]

/-- **Component splitting.**  A congruence modulo a product of coprime prime-power components is
exactly the conjunction of the component congruences: the global constraint decomposes into one
constraint per active component. -/
theorem dvd_mul_iff_of_coprime {r₁ r₂ : ℕ} (h : Nat.Coprime r₁ r₂) (x : ℤ) :
    ((r₁ * r₂ : ℕ) : ℤ) ∣ x ↔ (r₁ : ℤ) ∣ x ∧ (r₂ : ℤ) ∣ x := by
  constructor
  · intro hx
    exact ⟨dvd_trans (by exact_mod_cast Dvd.intro _ rfl) hx,
      dvd_trans (by exact_mod_cast Dvd.intro_left _ rfl) hx⟩
  · rintro ⟨h1, h2⟩
    have hcop : IsCoprime (r₁ : ℤ) (r₂ : ℤ) := Int.isCoprime_iff_gcd_eq_one.2 (by simpa using h)
    push_cast
    exact hcop.mul_dvd h1 h2

/-- **Global, not rowwise.**  A single global congruence can be solved by a set of positions no
sub-block of which solves it: the column compiler is allowed to use cancellations that are
invisible to any per-block treatment.  Explicit witness: modulo `5`, the positions with weights
`2` and `3` jointly hit the target `0`, while neither alone does. -/
theorem column_sum_not_rowwise :
    ((5 : ℤ) ∣ ((2 : ℤ) + 3)) ∧ ¬ ((5 : ℤ) ∣ (2 : ℤ)) ∧ ¬ ((5 : ℤ) ∣ (3 : ℤ)) := by
  refine ⟨by decide, by decide, by decide⟩

end AnchoredV4
end Erdos287
