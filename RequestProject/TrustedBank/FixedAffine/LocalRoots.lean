import Mathlib

/-!
# Trusted bank — local roots of a linear form

Generic finite algebra used by the local-admissibility and local-root-count theorems:

* a linear form `a * n + b` over a finite field has exactly one root when `a ≠ 0`,
  and no root when `a = 0 ≠ b`;
* over `ℤ`, a linear form with coprime coefficients cannot have two roots modulo a
  prime `p ≥ 3` at distance `≤ 2`.

No analytic statement occurs here.
-/

open scoped BigOperators

namespace TrustedBank
namespace LocalRoots

section FiniteField

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The root set of `n ↦ a n + b` inside a finite field. -/
def linRoots (a b : K) : Finset K := Finset.univ.filter (fun n => a * n + b = 0)

/-- With nonzero leading coefficient, the root set is the singleton `{-b/a}`. -/
theorem linRoots_of_ne_zero {a b : K} (ha : a ≠ 0) : linRoots a b = {-b / a} := by
  ext n
  simp only [linRoots, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    field_simp
    linear_combination h
  · rintro rfl
    field_simp
    ring

/-- With nonzero leading coefficient, there is exactly one root. -/
theorem linRoots_card_of_ne_zero {a b : K} (ha : a ≠ 0) : (linRoots a b).card = 1 := by
  rw [linRoots_of_ne_zero ha, Finset.card_singleton]

/-- With zero leading coefficient and nonzero constant term, there is no root. -/
theorem linRoots_of_eq_zero {a b : K} (ha : a = 0) (hb : b ≠ 0) : linRoots a b = ∅ := by
  ext n
  simp only [linRoots, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    iff_false, ha, zero_mul, zero_add]
  exact hb

end FiniteField

/-- **Two nearby roots are impossible.**  If `a, b` are coprime integers, `p ≥ 3` is a
prime, and `p` divides `a n₁ + b` and `a n₂ + b` for two distinct integers with
`|n₁ - n₂| ≤ 2`, we get a contradiction. -/
theorem no_two_nearby_roots {a b : ℤ} (hab : IsCoprime a b) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 ≤ p) {n₁ n₂ : ℤ} (hne : n₁ ≠ n₂) (hclose : |n₁ - n₂| ≤ 2)
    (h₁ : (p : ℤ) ∣ a * n₁ + b) (h₂ : (p : ℤ) ∣ a * n₂ + b) : False := by
  have hdiff : (p : ℤ) ∣ a * (n₁ - n₂) := by
    have := dvd_sub h₁ h₂
    simpa [mul_sub] using this
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpp.dvd_mul.1 hdiff with hpa | hpn
  · -- `p ∣ a`, hence `p ∣ b`, contradicting coprimality
    have hpb : (p : ℤ) ∣ b := by
      have : (p : ℤ) ∣ a * n₁ := hpa.mul_right _
      simpa using dvd_sub h₁ this
    obtain ⟨x, y, hxy⟩ := hab
    have : (p : ℤ) ∣ 1 := hxy ▸ dvd_add (hpa.mul_left x) (hpb.mul_left y)
    have := Int.le_of_dvd one_pos this
    have : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
    omega
  · have hne0 : n₁ - n₂ ≠ 0 := sub_ne_zero.2 hne
    have hle := Int.le_of_dvd (abs_pos.2 hne0) ((dvd_abs _ _).2 hpn)
    have : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
    omega

end LocalRoots
end TrustedBank
