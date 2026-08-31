import Mathlib

/-!
# §4 — Coefficient energy, one level

`CASE-B ONE-LEVEL PRIMITIVE-FRACTION LARGE SIEVE`, Section 4.

The audited claim is

```
∑_{m ~ G/d} E_{dm}/m²  ≪  d B (1 + B/G) L^{C_E},
```

for a reciprocal energy obeying `E_g ≤ (gB + B²)L^{C_E}`.

`coefficient_energy_bound` proves this in the **exact** form, with implied constant `1`:

```
∑_{M ≤ m < 2M} E_{dm}/m²  ≤  dB(1 + B/G) L^{C_E},   G = dM.
```

The two auxiliary sums used are the trivial ones,
`∑_{M ≤ m < 2M} 1/m ≤ 1` and `∑_{M ≤ m < 2M} 1/m² ≤ 1/M`; both are proved here
(`sum_inv_dyadic_le_one`, `sum_inv_sq_dyadic_le`).  No logarithm enters.

The energy hypothesis `E_g ≤ (gB+B²)L^{C_E}` is *not* proved anywhere in this repository; it
enters every statement of this file as an explicit hypothesis (`hE`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset

namespace Erdos287
namespace OneLevelEnergy

/-! ## §4.1  The two dyadic reciprocal sums -/

/-- `∑_{M ≤ m < 2M} 1/m ≤ 1`.  `LEAN_PROVED`. -/
theorem sum_inv_dyadic_le_one (M : ℕ) (hM : 0 < M) :
    ∑ m ∈ Finset.Ico M (2 * M), (1 : ℝ) / (m : ℝ) ≤ 1 := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hpt : ∀ m ∈ Finset.Ico M (2 * M), (1 : ℝ) / (m : ℝ) ≤ 1 / (M : ℝ) := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1
    exact one_div_le_one_div_of_le hMR this
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [Finset.sum_const, Nat.card_Ico]
  have : ((2 * M - M : ℕ) : ℝ) = (M : ℝ) := by
    have : 2 * M - M = M := by omega
    rw [this]
  rw [nsmul_eq_mul, this]
  rw [mul_one_div, div_self (ne_of_gt hMR)]

/-- `∑_{M ≤ m < 2M} 1/m² ≤ 1/M`.  `LEAN_PROVED`. -/
theorem sum_inv_sq_dyadic_le (M : ℕ) (hM : 0 < M) :
    ∑ m ∈ Finset.Ico M (2 * M), (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 / (M : ℝ) := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hpt : ∀ m ∈ Finset.Ico M (2 * M), (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 / (M : ℝ) ^ 2 := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hmM : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1
    have : (M : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := by nlinarith
    exact one_div_le_one_div_of_le (by positivity) this
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [Finset.sum_const, Nat.card_Ico]
  have hc : ((2 * M - M : ℕ) : ℝ) = (M : ℝ) := by
    have : 2 * M - M = M := by omega
    rw [this]
  rw [nsmul_eq_mul, hc]
  rw [mul_one_div, pow_two, ← div_div, div_self (ne_of_gt hMR)]

/-! ## §4.2  The exact coefficient-energy bound -/

/-- **`DET1-ONELEVEL-COEFFENERGY45`.**  `LEAN_PROVED` (conditional on the source energy bound).

If the reciprocal energy satisfies `0 ≤ E_g ≤ (gB + B²)L` for all `g`, then for `G = dM`

```
∑_{M ≤ m < 2M} E_{dm}/m²  ≤  dB(1 + B/G)·L,
```

with implied constant exactly `1`. -/
theorem coefficient_energy_bound {d M : ℕ} (hd : 0 < d) (hM : 0 < M) (B L : ℝ)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (E : ℕ → ℝ)
    (hE : ∀ g, E g ≤ ((g : ℝ) * B + B ^ 2) * L) :
    ∑ m ∈ Finset.Ico M (2 * M), E (d * m) / (m : ℝ) ^ 2
      ≤ (d : ℝ) * B * (1 + B / ((d * M : ℕ) : ℝ)) * L := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  -- pointwise split
  have hpt : ∀ m ∈ Finset.Ico M (2 * M),
      E (d * m) / (m : ℝ) ^ 2
        ≤ ((d : ℝ) * B * L) * (1 / (m : ℝ)) + (B ^ 2 * L) * (1 / (m : ℝ) ^ 2) := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by
      have : 0 < m := lt_of_lt_of_le hM hm.1
      exact_mod_cast this
    have h1 : E (d * m) ≤ (((d * m : ℕ) : ℝ) * B + B ^ 2) * L := hE (d * m)
    have h2 : E (d * m) / (m : ℝ) ^ 2 ≤ ((((d * m : ℕ) : ℝ)) * B + B ^ 2) * L / (m : ℝ) ^ 2 := by
      gcongr
    refine le_trans h2 (le_of_eq ?_)
    push_cast
    field_simp
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hA : ((d : ℝ) * B * L) * ∑ m ∈ Finset.Ico M (2 * M), (1 : ℝ) / (m : ℝ)
      ≤ ((d : ℝ) * B * L) * 1 :=
    mul_le_mul_of_nonneg_left (sum_inv_dyadic_le_one M hM) (by positivity)
  have hB2 : (B ^ 2 * L) * ∑ m ∈ Finset.Ico M (2 * M), (1 : ℝ) / (m : ℝ) ^ 2
      ≤ (B ^ 2 * L) * (1 / (M : ℝ)) :=
    mul_le_mul_of_nonneg_left (sum_inv_sq_dyadic_le M hM) (by positivity)
  have hgoal : ((d : ℝ) * B * L) * 1 + (B ^ 2 * L) * (1 / (M : ℝ))
      = (d : ℝ) * B * (1 + B / ((d * M : ℕ) : ℝ)) * L := by
    push_cast
    field_simp
  linarith [hA, hB2, hgoal.le, hgoal.ge]

end OneLevelEnergy
end Erdos287
