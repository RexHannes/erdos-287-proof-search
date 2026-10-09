import Mathlib

/-!
# Anchored V3 — column zero patterns and their exact integer weights

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Fix valid preparation data `ω`: a finite set of rows, a positive modulus `m r` per row, and a
baseline partial sum `S₀`.  Put

```
D(ω) = lcm_r (m r),      cof r = D / m r.
```

For a band prime `ℓ` and the set `I ℓ ⊆ rows` of rows carrying an actual terminal site
`m r * ℓ`, the **column zero patterns** are

```
Z ℓ = { E ⊆ I ℓ : ℓ ∣ ∑_{r ∈ E} cof r },
```

with **integer weight** `w ℓ E = (∑_{r ∈ E} cof r) / ℓ`.

The exact reciprocal identity proved here is

```
∑_{r ∈ E} 1 / (m r * ℓ) = w ℓ E / D          (E ∈ Z ℓ).
```

Everything is exact finite arithmetic; no asymptotics occur.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV3

/-- Valid preparation data: finitely many rows with positive moduli and a baseline. -/
structure Prep where
  /-- the finite set of rows -/
  rows : Finset ℕ
  /-- the modulus of each row -/
  m : ℕ → ℕ
  /-- row moduli are positive -/
  hm : ∀ r ∈ rows, 0 < m r
  /-- the baseline partial sum -/
  S₀ : ℚ

namespace Prep

variable (ω : Prep)

/-- The global modulus `D(ω) = lcm_r (m r)`. -/
def D : ℕ := ω.rows.lcm ω.m

/-- The row cofactor `D / m r`. -/
def cof (r : ℕ) : ℕ := ω.D / ω.m r

theorem m_dvd_D {r : ℕ} (hr : r ∈ ω.rows) : ω.m r ∣ ω.D := Finset.dvd_lcm hr

theorem D_pos : 0 < ω.D := by
  rcases Nat.eq_zero_or_pos ω.D with h | h
  · obtain ⟨r, hr, hzero⟩ := Finset.lcm_eq_zero_iff.mp (show ω.rows.lcm ω.m = 0 from h)
    have := ω.hm r hr
    omega
  · exact h

theorem cof_mul {r : ℕ} (hr : r ∈ ω.rows) : ω.cof r * ω.m r = ω.D :=
  Nat.div_mul_cancel (ω.m_dvd_D hr)

end Prep

/-- A column zero pattern for the band prime `ℓ` on the active row set `I`. -/
def IsZeroPattern (ω : Prep) (ℓ : ℕ) (I E : Finset ℕ) : Prop :=
  E ⊆ I ∧ ℓ ∣ ∑ r ∈ E, ω.cof r

/-- The exact integer weight of a column zero pattern. -/
def zpWeight (ω : Prep) (ℓ : ℕ) (E : Finset ℕ) : ℕ := (∑ r ∈ E, ω.cof r) / ℓ

theorem zpWeight_mul {ω : Prep} {ℓ : ℕ} {E : Finset ℕ} (h : ℓ ∣ ∑ r ∈ E, ω.cof r) :
    ℓ * zpWeight ω ℓ E = ∑ r ∈ E, ω.cof r :=
  Nat.mul_div_cancel' h

/-- **The exact reciprocal identity for a column zero pattern.** -/
theorem sum_recip_zeroPattern (ω : Prep) {ℓ : ℕ} (hℓ : 0 < ℓ) {I E : Finset ℕ}
    (hI : I ⊆ ω.rows) (hE : IsZeroPattern ω ℓ I E) :
    ∑ r ∈ E, (1 : ℚ) / ((ω.m r : ℚ) * (ℓ : ℚ)) = (zpWeight ω ℓ E : ℚ) / (ω.D : ℚ) := by
  obtain ⟨hEI, hdvd⟩ := hE
  have hD : (0:ℚ) < (ω.D : ℚ) := by exact_mod_cast ω.D_pos
  have hℓ' : (0:ℚ) < (ℓ : ℚ) := by exact_mod_cast hℓ
  have hterm : ∀ r ∈ E, (1 : ℚ) / ((ω.m r : ℚ) * (ℓ : ℚ))
      = (ω.cof r : ℚ) / ((ω.D : ℚ) * (ℓ : ℚ)) := by
    intro r hr
    have hrow : r ∈ ω.rows := hI (hEI hr)
    have hm : (0:ℚ) < (ω.m r : ℚ) := by exact_mod_cast ω.hm r hrow
    have hcof : (ω.cof r : ℚ) * (ω.m r : ℚ) = (ω.D : ℚ) := by exact_mod_cast ω.cof_mul hrow
    field_simp
    linarith [hcof]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  have hsum : ((∑ r ∈ E, ω.cof r : ℕ) : ℚ) = (ℓ : ℚ) * (zpWeight ω ℓ E : ℚ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) (zpWeight_mul hdvd).symm
  rw [Nat.cast_sum] at hsum
  rw [hsum]
  field_simp

end AnchoredV3
end Erdos287
