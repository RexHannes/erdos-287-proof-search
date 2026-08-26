import Mathlib

/-!
# Gate 1B — the centered divisibility identity

For a positive modulus `m` set

```
rho m N = 1_{m | N} - 1/m   (in ℚ).
```

For **coprime** positive `d, p` we prove exactly

```
rho (d*p) N = rho d N * rho p N + (1/p) * rho d N + (1/d) * rho p N.
```

Coprimality is genuinely needed: `rho_not_multiplicative_of_not_coprime` exhibits
`d = p = 2`, `N = 2` where the identity fails.

This file is pure exact arithmetic.  Gate 1B remains **OPEN**; nothing here is an
analytic estimate.
-/

open scoped BigOperators

namespace TrustedBank
namespace Gate1B

/-- The centered divisibility weight `rho m N = 1_{m ∣ N} - 1/m`, in `ℚ`. -/
def rho (m N : ℕ) : ℚ := (if m ∣ N then (1 : ℚ) else 0) - 1 / m

@[simp] lemma rho_def (m N : ℕ) : rho m N = (if m ∣ N then (1 : ℚ) else 0) - 1 / m := rfl

/-- Mean-zero normalisation check: for `m ≥ 1`, the average of `rho m` over a full
residue period `{0, …, m-1}` vanishes. -/
theorem rho_sum_period {m : ℕ} (hm : 0 < m) :
    ∑ N ∈ Finset.range m, rho m N = 0 := by
  have hset : (Finset.range m).filter (fun N => m ∣ N) = {0} := by
    ext N
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    exact ⟨fun h => Nat.eq_zero_of_dvd_of_lt h.2 h.1, by rintro rfl; exact ⟨hm, dvd_zero m⟩⟩
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have h1 : ∑ N ∈ Finset.range m, (if m ∣ N then (1 : ℚ) else 0) = 1 := by
    rw [← Finset.sum_filter, hset, Finset.sum_singleton]
  have h2 : ∑ _N ∈ Finset.range m, (1 / (m : ℚ)) = 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  simp only [rho_def, Finset.sum_sub_distrib, h1, h2, sub_self]

/-- **Centered product identity.**  For coprime positive `d, p`,
`rho (d p) N = rho d N · rho p N + (1/p)·rho d N + (1/d)·rho p N`. -/
theorem rho_mul_of_coprime {d p : ℕ} (hd : 0 < d) (hp : 0 < p)
    (hcop : Nat.Coprime d p) (N : ℕ) :
    rho (d * p) N = rho d N * rho p N + (1 / p) * rho d N + (1 / d) * rho p N := by
  have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hp' : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hdvd : (d * p ∣ N) ↔ (d ∣ N ∧ p ∣ N) := by
    constructor
    · intro h; exact ⟨dvd_trans (dvd_mul_right d p) h, dvd_trans (dvd_mul_left p d) h⟩
    · rintro ⟨h1, h2⟩; exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h1 h2
  simp only [rho_def, Nat.cast_mul]
  by_cases h1 : d ∣ N <;> by_cases h2 : p ∣ N <;>
    simp [hdvd, h1, h2] <;> field_simp <;> ring

/-- **Coprimality is required.**  With `d = p = 2` and `N = 2` the product identity
fails, so `rho_mul_of_coprime` cannot be stated without the coprimality hypothesis. -/
theorem rho_not_multiplicative_of_not_coprime :
    rho (2 * 2) 2 ≠ rho 2 2 * rho 2 2 + (1 / (2:ℕ) : ℚ) * rho 2 2 + (1 / (2:ℕ) : ℚ) * rho 2 2 := by
  norm_num [rho_def]

/-- Hostile test 1: a coprime pair, `d = 2`, `p = 3`, `N = 6`. -/
theorem rho_test_2_3_6 :
    rho (2 * 3) 6 = rho 2 6 * rho 3 6 + (1 / (3:ℕ) : ℚ) * rho 2 6 + (1 / (2:ℕ) : ℚ) * rho 3 6 := by
  norm_num [rho_def]

/-- Hostile test 2: a coprime pair where neither divides, `d = 2`, `p = 3`, `N = 5`. -/
theorem rho_test_2_3_5 :
    rho (2 * 3) 5 = rho 2 5 * rho 3 5 + (1 / (3:ℕ) : ℚ) * rho 2 5 + (1 / (2:ℕ) : ℚ) * rho 3 5 := by
  norm_num [rho_def]

/-- Hostile test 3: a coprime pair where exactly one divides, `d = 4`, `p = 3`, `N = 8`. -/
theorem rho_test_4_3_8 :
    rho (4 * 3) 8 = rho 4 8 * rho 3 8 + (1 / (3:ℕ) : ℚ) * rho 4 8 + (1 / (4:ℕ) : ℚ) * rho 3 8 := by
  norm_num [rho_def]

/-- Hostile test 4: a second non-coprime failure, `d = 6`, `p = 4`, `N = 12`. -/
theorem rho_fail_6_4_12 :
    rho (6 * 4) 12 ≠ rho 6 12 * rho 4 12 + (1 / (4:ℕ) : ℚ) * rho 6 12
      + (1 / (6:ℕ) : ℚ) * rho 4 12 := by
  norm_num [rho_def]

end Gate1B
end TrustedBank
