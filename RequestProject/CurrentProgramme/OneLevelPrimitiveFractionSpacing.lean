import Mathlib

/-!
# §2 — Primitive-fraction spacing, one level

`CASE-B ONE-LEVEL PRIMITIVE-FRACTION LARGE SIEVE`, Section 2.

Fix `d ≥ 1` and `M ≥ 1`, and consider the frequencies

```
t/(d m) mod 1,   m ∈ [M, 2M),  (m,d) = 1,  (t, dm) = 1.
```

Three exact statements are proved here, with no asymptotic content:

* `primitiveFraction_inj` — with the standard representatives `0 ≤ t < dm` the map
  `(m,t) ↦ t/(dm) mod 1` is injective: equality modulo one forces equality of the denominators
  and of the numerators.  Only `(t, m) = 1` is used (the hypothesis `(t, dm) = 1` is stronger).
* `spacing_lower_bound` — two frequencies that are *not* congruent modulo one are separated by
  at least `1/(d m₁ m₂)`, uniformly in the choice of the integer shift.
* `spacing_uniform` / `primitiveFraction_separation` — with `m₁, m₂ ∈ [M, 2M)` and `G = dM` this
  is at least `d/(4G²)`.

No coprimality with `d` is needed for the metric statements; it is only recorded in the
injectivity statement, where it is genuinely used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace OneLevelSpacing

/-! ## §2.1  Reduced representatives are unique -/

/-- **`DET1-ONELEVEL-PRIMITIVEFRACTION-SPACING45`, injectivity.**  `LEAN_PROVED`.

If `0 ≤ tᵢ < d mᵢ`, `(tᵢ, mᵢ) = 1`, and `t₁/(dm₁) ≡ t₂/(dm₂) (mod 1)`, then `m₁ = m₂` and
`t₁ = t₂`. -/
theorem primitiveFraction_inj {d m1 m2 t1 t2 : ℕ} (hd : 0 < d) (hm1 : 0 < m1) (hm2 : 0 < m2)
    (h1 : Nat.Coprime t1 m1) (h2 : Nat.Coprime t2 m2)
    (hlt1 : t1 < d * m1) (hlt2 : t2 < d * m2) (n : ℤ)
    (heq : (t1 : ℚ) / ((d * m1 : ℕ) : ℚ) - (t2 : ℚ) / ((d * m2 : ℕ) : ℚ) = (n : ℚ)) :
    m1 = m2 ∧ t1 = t2 := by
  have hd1 : (0 : ℚ) < ((d * m1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.mul_pos hd hm1
  have hd2 : (0 : ℚ) < ((d * m2 : ℕ) : ℚ) := by
    exact_mod_cast Nat.mul_pos hd hm2
  -- both fractions lie in `[0,1)`, so the integer shift is zero
  have hx1 : (0 : ℚ) ≤ (t1 : ℚ) / ((d * m1 : ℕ) : ℚ) := by positivity
  have hx2 : (0 : ℚ) ≤ (t2 : ℚ) / ((d * m2 : ℕ) : ℚ) := by positivity
  have hy1 : (t1 : ℚ) / ((d * m1 : ℕ) : ℚ) < 1 := by
    rw [div_lt_one hd1]; exact_mod_cast hlt1
  have hy2 : (t2 : ℚ) / ((d * m2 : ℕ) : ℚ) < 1 := by
    rw [div_lt_one hd2]; exact_mod_cast hlt2
  have hn0 : n = 0 := by
    have hlt : (n : ℚ) < 1 := by rw [← heq]; linarith
    have hgt : (-1 : ℚ) < (n : ℚ) := by rw [← heq]; linarith
    have h1' : n < 1 := by exact_mod_cast hlt
    have h2' : (-1 : ℤ) < n := by exact_mod_cast hgt
    omega
  subst hn0
  -- hence the two rationals are equal; cross-multiply
  have hcross : (t1 : ℚ) * ((d * m2 : ℕ) : ℚ) = (t2 : ℚ) * ((d * m1 : ℕ) : ℚ) := by
    have : (t1 : ℚ) / ((d * m1 : ℕ) : ℚ) = (t2 : ℚ) / ((d * m2 : ℕ) : ℚ) := by
      have := heq; push_cast at this ⊢; linarith
    field_simp at this
    linarith
  have hnat : t1 * m2 = t2 * m1 := by
    have hdq : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
    have : (t1 : ℚ) * (m2 : ℚ) = (t2 : ℚ) * (m1 : ℚ) := by
      push_cast at hcross
      have hne : (d : ℚ) ≠ 0 := ne_of_gt hdq
      field_simp at hcross
      nlinarith [hcross]
    exact_mod_cast this
  -- coprimality upgrades the cross relation to `m₁ = m₂`
  have hdvd1 : m1 ∣ m2 := by
    have : m1 ∣ t1 * m2 := ⟨t2, by rw [hnat]; ring⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm h1) this)
  have hdvd2 : m2 ∣ m1 := by
    have : m2 ∣ t2 * m1 := ⟨t1, by rw [← hnat]; ring⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm h2) this)
  have hm : m1 = m2 := Nat.dvd_antisymm hdvd1 hdvd2
  subst hm
  refine ⟨rfl, ?_⟩
  have := hnat
  exact Nat.eq_of_mul_eq_mul_right hm1 this

/-! ## §2.2  The exact separation -/

/-- **`DET1-ONELEVEL-PRIMITIVEFRACTION-SPACING45`, separation.**  `LEAN_PROVED`.

Two frequencies whose difference is not an integer are `1/(d m₁ m₂)`-separated modulo one:
for every integer shift `n` for which the integral numerator
`t₁m₂ - t₂m₁ - n d m₁ m₂` is nonzero. -/
theorem spacing_lower_bound {d m1 m2 : ℕ} (hd : 0 < d) (hm1 : 0 < m1) (hm2 : 0 < m2)
    (t1 t2 n : ℤ) (hne : t1 * (m2 : ℤ) - t2 * (m1 : ℤ) - n * ((d * m1 * m2 : ℕ) : ℤ) ≠ 0) :
    (1 : ℚ) / ((d * m1 * m2 : ℕ) : ℚ)
      ≤ |(t1 : ℚ) / ((d * m1 : ℕ) : ℚ) - (t2 : ℚ) / ((d * m2 : ℕ) : ℚ) - (n : ℚ)| := by
  have hdq : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have hm1q : (0 : ℚ) < (m1 : ℚ) := by exact_mod_cast hm1
  have hm2q : (0 : ℚ) < (m2 : ℚ) := by exact_mod_cast hm2
  set N : ℤ := t1 * (m2 : ℤ) - t2 * (m1 : ℤ) - n * ((d * m1 * m2 : ℕ) : ℤ) with hN
  have hden : (0 : ℚ) < ((d * m1 * m2 : ℕ) : ℚ) := by push_cast; positivity
  have hrepr : (t1 : ℚ) / ((d * m1 : ℕ) : ℚ) - (t2 : ℚ) / ((d * m2 : ℕ) : ℚ) - (n : ℚ)
      = (N : ℚ) / ((d * m1 * m2 : ℕ) : ℚ) := by
    rw [hN]
    push_cast
    field_simp
  rw [hrepr, abs_div, abs_of_pos hden]
  have h1 : (1 : ℚ) ≤ |(N : ℚ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hne
  gcongr

/-- **`DET1-ONELEVEL-PRIMITIVEFRACTION-SPACING45`, uniform form.**  `LEAN_PROVED`.

For `m₁, m₂ ∈ [M, 2M)` and `G = dM` one has `1/(d m₁ m₂) ≥ d/(4G²)`. -/
theorem spacing_uniform {d M m1 m2 : ℕ} (hd : 0 < d) (hM : 0 < M)
    (h1 : m1 < 2 * M) (h2 : m2 < 2 * M) (hm1 : 0 < m1) (hm2 : 0 < m2) :
    (d : ℚ) / (4 * ((d * M : ℕ) : ℚ) ^ 2) ≤ (1 : ℚ) / ((d * m1 * m2 : ℕ) : ℚ) := by
  have hdq : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have hMq : (0 : ℚ) < (M : ℚ) := by exact_mod_cast hM
  have hm1q : (0 : ℚ) < (m1 : ℚ) := by exact_mod_cast hm1
  have hm2q : (0 : ℚ) < (m2 : ℚ) := by exact_mod_cast hm2
  have h1q : (m1 : ℚ) ≤ 2 * (M : ℚ) := by exact_mod_cast (Nat.le_of_lt h1 : m1 ≤ 2 * M)
  have h2q : (m2 : ℚ) ≤ 2 * (M : ℚ) := by exact_mod_cast (Nat.le_of_lt h2 : m2 ≤ 2 * M)
  have hEq : (d : ℚ) / (4 * ((d * M : ℕ) : ℚ) ^ 2) = 1 / (4 * (d : ℚ) * (M : ℚ) ^ 2) := by
    push_cast
    field_simp
  rw [hEq]
  refine one_div_le_one_div_of_le (by push_cast; positivity) ?_
  push_cast
  nlinarith [mul_le_mul h1q h2q hm2q.le (by positivity : (0:ℚ) ≤ 2 * (M:ℚ)), hdq.le]

/-- **`DET1-ONELEVEL-PRIMITIVEFRACTION-SPACING45`.**  `LEAN_PROVED`.

The banked Section 2 statement: distinct primitive fractions with denominators `d m`,
`m ∈ [M,2M)`, are separated modulo one by at least `d/(4G²)`, `G = dM`. -/
theorem primitiveFraction_separation {d M m1 m2 : ℕ} (hd : 0 < d) (hM : 0 < M)
    (hm1 : 0 < m1) (hm2 : 0 < m2) (h1 : m1 < 2 * M) (h2 : m2 < 2 * M)
    (t1 t2 n : ℤ) (hne : t1 * (m2 : ℤ) - t2 * (m1 : ℤ) - n * ((d * m1 * m2 : ℕ) : ℤ) ≠ 0) :
    (d : ℚ) / (4 * ((d * M : ℕ) : ℚ) ^ 2)
      ≤ |(t1 : ℚ) / ((d * m1 : ℕ) : ℚ) - (t2 : ℚ) / ((d * m2 : ℕ) : ℚ) - (n : ℚ)| :=
  le_trans (spacing_uniform hd hM h1 h2 hm1 hm2)
    (spacing_lower_bound hd hm1 hm2 t1 t2 n hne)

end OneLevelSpacing
end Erdos287
