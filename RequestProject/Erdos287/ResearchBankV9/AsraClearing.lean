import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V9 §4G: rational-root bilinear clearing

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

For a rational root `ρ = v/u` with `u ∣ U` (`U = lcm` of the root denominators) and
`gcd(U, q) = 1`, the congruence `m n ≡ ρ (mod q)` (i.e. `q ∣ u m n − v`) is equivalent to the
cleared congruence `(U m) n ≡ U ρ (mod q)` (i.e. `q ∣ (U m) n − (U/u) v`) (`clearing_iff`).
Kernel-proved:

* the transformed coefficient `α'(m') = α(m'/U)` if `U ∣ m'`, else `0` (`alphaT`), its support
  condition `U ∣ m'` (`alphaT_support`) and **divisor-bound preservation** (`alphaT_divisor_bound`);
* the transformed base progression `m' n ≡ U p₀ (mod U B)` (`base_progression_iff`);
* **firewall** (`fixed_denominator_does_not_delete_base`): a pair satisfying the cleared root
  congruence need not satisfy the base progression, so a fixed denominator does **not** permit
  deleting the base progression.
-/

namespace Erdos287
namespace ResearchBankV9
namespace AsraClearing

/-- **Rational-root clearing.** -/
theorem clearing_iff {q u U : ℕ} (hu : 0 < u) (huU : u ∣ U) (hcop : Nat.Coprime U q)
    (v m n : ℤ) :
    (q : ℤ) ∣ u * m * n - v ↔ (q : ℤ) ∣ (U * m) * n - (U / u : ℕ) * v := by
  obtain ⟨k, rfl⟩ := huU
  have hk : Nat.Coprime k q := Nat.Coprime.coprime_mul_left hcop
  rw [Nat.mul_div_cancel_left k hu]
  have e : ((u * k : ℕ) : ℤ) * m * n - (k : ℤ) * v = (k : ℤ) * (u * m * n - v) := by
    push_cast; ring
  rw [e]
  constructor
  · intro h; exact dvd_mul_of_dvd_right h _
  · intro h
    have hc : IsCoprime (q : ℤ) (k : ℤ) := Nat.isCoprime_iff_coprime.2 hk.symm
    exact hc.dvd_of_dvd_mul_left h

/-- The transformed coefficient `α'(m') = α(m'/U)` if `U ∣ m'`, else `0`. -/
def alphaT (U : ℕ) (α : ℕ → ℝ) (m' : ℕ) : ℝ := if U ∣ m' then α (m' / U) else 0

/-- Support condition: `α'(m') ≠ 0 ⟹ U ∣ m'`. -/
theorem alphaT_support {U : ℕ} {α : ℕ → ℝ} {m' : ℕ} (h : alphaT U α m' ≠ 0) : U ∣ m' := by
  unfold alphaT at h; split_ifs at h with hd; exact hd; exact absurd rfl h

theorem alphaT_mul {U : ℕ} (hU : 0 < U) (α : ℕ → ℝ) (m : ℕ) : alphaT U α (U * m) = α m := by
  simp [alphaT, Nat.mul_div_cancel_left m hU]

/-- **Divisor-bound preservation**: `|α(m)| ≤ τ(m)` for all `m` implies `|α'(m')| ≤ τ(m')`. -/
theorem alphaT_divisor_bound {U : ℕ} (hU : 0 < U) {α : ℕ → ℝ}
    (hα : ∀ m, |α m| ≤ (m.divisors.card : ℝ)) (m' : ℕ) :
    |alphaT U α m'| ≤ (m'.divisors.card : ℝ) := by
  unfold alphaT
  split_ifs with hd
  · obtain ⟨m, rfl⟩ := hd
    rw [Nat.mul_div_cancel_left m hU]
    refine (hα m).trans ?_
    rcases Nat.eq_zero_or_pos m with h0 | hm
    · subst h0; simp
    · exact_mod_cast Finset.card_le_card
        (Nat.divisors_subset_of_dvd (by positivity) (dvd_mul_left m U))
  · simp

/-- **The transformed base progression**: `m n ≡ p₀ (mod B)` iff `(U m) n ≡ U p₀ (mod U B)`. -/
theorem base_progression_iff {U B : ℕ} (hU : 0 < U) (p₀ m n : ℤ) :
    (B : ℤ) ∣ m * n - p₀ ↔ ((U * B : ℕ) : ℤ) ∣ (U * m) * n - U * p₀ := by
  push_cast
  rw [show (U : ℤ) * m * n - U * p₀ = U * (m * n - p₀) by ring]
  exact (Int.mul_dvd_mul_iff_left (by exact_mod_cast hU.ne')).symm

/-- **Firewall: a fixed denominator does not permit deleting the base progression.**  With
`q = 5`, `ρ = 1/2` (`u = U = 2`), base modulus `B = 3`, `p₀ = 1`: the pair `m = 1` (`m' = 2`),
`n = 3` satisfies the cleared root congruence but not the base progression. -/
theorem fixed_denominator_does_not_delete_base :
    ((5 : ℕ) : ℤ) ∣ ((2 : ℕ) * (1 : ℤ)) * 3 - ((2 / 2 : ℕ) : ℤ) * 1 ∧
    ¬ ((3 : ℕ) : ℤ) ∣ (1 : ℤ) * 3 - 1 ∧
    ¬ (((2 * 3 : ℕ)) : ℤ) ∣ ((2 : ℕ) * (1 : ℤ)) * 3 - (2 : ℕ) * 1 := by
  decide

end AsraClearing
end ResearchBankV9
end Erdos287
