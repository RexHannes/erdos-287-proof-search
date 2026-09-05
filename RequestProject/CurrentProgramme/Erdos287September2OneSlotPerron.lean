import Mathlib

/-!
# Erdős #287 — September-2 bank, §4–§5: the one-slot Perron mass and the finite
source-arithmetic ceilings

```
ONE-SLOT PERRON MASS  < 128 log X      : KERNEL-PROVED   (for X ≥ 3)
arsinh(X^400) < log (2 X^400)          : KERNEL-PROVED **FALSE** (recorded, corrected)
N = k·ℓ + r + s ≤ 112                  : KERNEL-PROVED
⌈1/(1-γ)⌉ = 2  for γ = 1/2 − ε         : KERNEL-PROVED
nonempty coordinate subsets ≤ 2^112−1  : KERNEL-PROVED
```

This module is **append-only** and proves *only* elementary real/finite arithmetic.  It does
**not** infer the complete Perron / nuclear ledger, and it claims nothing about Erdős #287.

**§4 — the one-slot Perron kernel.**  With the banked one-slot abscissa and height

```
    c = X^(-200),      T = X^200,      so   T / c = X^400,
```

the one-slot Perron mass is `perronMassOne X = (1/π) · arsinh (X^400)`.

The requested intermediate chain was `arsinh (X^400) < log (2 X^400) < 401 log X`.  Its
*first* step is false — `arsinh t = log (t + √(1+t²)) > log (2t)` for every `t > 0`, because
`√(1+t²) > t`.  This is recorded and kernel-proved as `arsinh_gt_log_two_mul`, and the chain
is repaired through the constant `5/2` in place of `2`:

```
    arsinh t ≤ log (5t/2)          (t ≥ 1, since √(1+t²) ≤ (3/2) t)
    log (5 X^400 / 2) < 401 log X  (X ≥ 3, since log (5/2) < log X)
```

which yields the intended conclusion `perronMassOne X < 128 log X` (using `401 < 128 π`).

**§5 — finite source arithmetic.**  From the banked constants `ε = 5·10⁻²²`, `γ = 1/2 − ε`,
`J₀ = 4`, `ℓ = 12`, `k ≤ 6`, `r, s ≤ 20`, the ceilings `⌈1/(1−γ)⌉ = 2` and `N ≤ 112` are
kernel-proved, together with the (intentionally enormous) count `2^112 − 1` of nonempty
coordinate subsets.  These bounds are **not** an effectivity closure.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace September2OneSlotPerron

/-! ## §4.1  The one-slot abscissa and height -/

/-- The one-slot Perron abscissa `c = X^(-200)`. -/
noncomputable def perronAbscissa (X : ℝ) : ℝ := (X ^ (200 : ℕ))⁻¹

/-- The one-slot Perron height `T = X^200`. -/
noncomputable def perronHeight (X : ℝ) : ℝ := X ^ (200 : ℕ)

/-- **`height_div_abscissa`.**  `KERNEL-PROVED`.  `T / c = X^400`. -/
theorem height_div_abscissa (X : ℝ) :
    perronHeight X / perronAbscissa X = X ^ (400 : ℕ) := by
  unfold perronHeight perronAbscissa
  rw [div_eq_mul_inv, inv_inv, ← pow_add]

/-- The one-slot Perron mass `(1/π) · arsinh (X^400)`. -/
noncomputable def perronMassOne (X : ℝ) : ℝ := (1 / Real.pi) * Real.arsinh (X ^ (400 : ℕ))

/-! ## §4.2  The recorded false step, and its repair -/

/-- **`arsinh_gt_log_two_mul`.**  `KERNEL-PROVED`.  The requested step
`arsinh t < log (2t)` is **false**: the reverse strict inequality holds for every `t > 0`. -/
theorem arsinh_gt_log_two_mul {t : ℝ} (ht : 0 < t) :
    Real.log (2 * t) < Real.arsinh t := by
  have hsq : t < Real.sqrt (1 + t ^ 2) := by
    have h1 : Real.sqrt (t ^ 2) < Real.sqrt (1 + t ^ 2) :=
      Real.sqrt_lt_sqrt (by positivity) (by linarith)
    rwa [Real.sqrt_sq ht.le] at h1
  have hlt : 2 * t < t + Real.sqrt (1 + t ^ 2) := by linarith
  have := Real.log_lt_log (by linarith) hlt
  simpa [Real.arsinh] using this

/-- **`arsinh_le_log_five_halves_mul`.**  `KERNEL-PROVED`.  For `t ≥ 1`,
`arsinh t ≤ log (5t/2)`. -/
theorem arsinh_le_log_five_halves_mul {t : ℝ} (ht : 1 ≤ t) :
    Real.arsinh t ≤ Real.log (5 * t / 2) := by
  have ht0 : (0:ℝ) < t := lt_of_lt_of_le one_pos ht
  have hnn : (0:ℝ) ≤ (3 / 2) * t := by positivity
  have hsq : Real.sqrt (1 + t ^ 2) ≤ (3 / 2) * t := by
    have hle : (1 + t ^ 2 : ℝ) ≤ ((3 / 2) * t) ^ 2 := by nlinarith
    calc Real.sqrt (1 + t ^ 2) ≤ Real.sqrt (((3 / 2) * t) ^ 2) := Real.sqrt_le_sqrt hle
      _ = (3 / 2) * t := Real.sqrt_sq hnn
  have hle : t + Real.sqrt (1 + t ^ 2) ≤ 5 * t / 2 := by linarith
  have := Real.log_le_log (by positivity) hle
  simpa [Real.arsinh] using this

/-- **`log_five_halves_pow_lt`.**  `KERNEL-PROVED`.  For `X ≥ 3`,
`log (5 X^400 / 2) < 401 · log X`. -/
theorem log_five_halves_pow_lt {X : ℝ} (hX : 3 ≤ X) :
    Real.log (5 * X ^ (400 : ℕ) / 2) < 401 * Real.log X := by
  have hX0 : (0:ℝ) < X := by linarith
  have hsplit : Real.log (5 * X ^ (400 : ℕ) / 2)
      = Real.log (5 / 2) + 400 * Real.log X := by
    rw [show (5 * X ^ (400:ℕ) / 2 : ℝ) = (5 / 2) * X ^ (400:ℕ) by ring,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  have hlt : Real.log (5 / 2) < Real.log X := by
    apply Real.log_lt_log (by norm_num)
    linarith
  rw [hsplit]
  linarith

/-- **`perronMassOne_lt`.**  `KERNEL-PROVED`.  For `X ≥ 3` the one-slot Perron mass satisfies
`(1/π) · arsinh (X^400) < 128 · log X`. -/
theorem perronMassOne_lt {X : ℝ} (hX : 3 ≤ X) :
    perronMassOne X < 128 * Real.log X := by
  have hX0 : (0:ℝ) < X := by linarith
  have hpow : (1:ℝ) ≤ X ^ (400 : ℕ) := one_le_pow₀ (by linarith)
  have h1 : Real.arsinh (X ^ (400:ℕ)) ≤ Real.log (5 * X ^ (400:ℕ) / 2) :=
    arsinh_le_log_five_halves_mul hpow
  have h2 : Real.log (5 * X ^ (400:ℕ) / 2) < 401 * Real.log X := log_five_halves_pow_lt hX
  have hlogpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hpi : (401 : ℝ) < 128 * Real.pi := by
    have := Real.pi_gt_d2
    linarith
  have hpipos : (0:ℝ) < Real.pi := Real.pi_pos
  have hkey : Real.arsinh (X ^ (400:ℕ)) < 401 * Real.log X := lt_of_le_of_lt h1 h2
  unfold perronMassOne
  rw [one_div, inv_mul_eq_div, div_lt_iff₀ hpipos]
  calc Real.arsinh (X ^ (400:ℕ)) < 401 * Real.log X := hkey
    _ < (128 * Real.log X) * Real.pi := by nlinarith

/-! ## §5  Finite source-arithmetic ceilings -/

/-- The banked `ε = 5·10⁻²²`. -/
noncomputable def epsN2 : ℝ := 5 / 10 ^ (22 : ℕ)

/-- The banked exponent `γ = 1/2 − ε`. -/
noncomputable def gammaN2 : ℝ := 1 / 2 - epsN2

/-- **`eps_pos_lt_half`.**  `KERNEL-PROVED`. -/
theorem eps_pos_lt_half : 0 < epsN2 ∧ epsN2 < 1 / 2 := by
  unfold epsN2
  constructor <;> norm_num

/-- **`ceil_one_div_one_sub_gamma`.**  `KERNEL-PROVED`.  `⌈1/(1−γ)⌉ = 2`. -/
theorem ceil_one_div_one_sub_gamma : ⌈1 / (1 - gammaN2)⌉ = 2 := by
  obtain ⟨hpos, hlt⟩ := eps_pos_lt_half
  have h1 : 1 - gammaN2 = 1 / 2 + epsN2 := by unfold gammaN2; ring
  have hden : (0:ℝ) < 1 - gammaN2 := by rw [h1]; linarith
  have hupper : 1 / (1 - gammaN2) < 2 := by
    rw [div_lt_iff₀ hden, h1]; linarith
  have hlower : (1:ℝ) < 1 / (1 - gammaN2) := by
    rw [lt_div_iff₀ hden, h1]; linarith
  rw [Int.ceil_eq_iff]
  constructor
  · push_cast; linarith
  · push_cast; linarith

/-- The banked `J₀ = 4`. -/
def J0 : ℕ := 4

/-- The banked block length `ℓ = 12`. -/
def ellN : ℕ := 12

/-- The banked coordinate count `N = k·ℓ + r + s`. -/
def coordCount (k r s : ℕ) : ℕ := k * ellN + r + s

/-- **`coordCount_le_112`.**  `KERNEL-PROVED`.  With `k ≤ 6` and `r, s ≤ 20`,
`N = k·ℓ + r + s ≤ 112`. -/
theorem coordCount_le_112 {k r s : ℕ} (hk : k ≤ 6) (hr : r ≤ 20) (hs : s ≤ 20) :
    coordCount k r s ≤ 112 := by
  unfold coordCount ellN
  omega

/-- **`coordCount_max`.**  `KERNEL-PROVED`.  The bound `112` is attained, hence sharp. -/
theorem coordCount_max : coordCount 6 20 20 = 112 := by
  unfold coordCount ellN
  norm_num

/-- **`nonempty_coordinate_subsets_card`.**  `KERNEL-PROVED`.  On `N ≤ 112` coordinates there
are at most `2^112 − 1` nonempty coordinate subsets. -/
theorem nonempty_coordinate_subsets_card {N : ℕ} (hN : N ≤ 112) :
    ((Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.Nonempty)).card
      ≤ 2 ^ (112 : ℕ) - 1 := by
  have hsub : ((Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.Nonempty)).card
      ≤ Fintype.card (Finset (Fin N)) - 1 := by
    have hmem : (∅ : Finset (Fin N)) ∈ (Finset.univ : Finset (Finset (Fin N))) :=
      Finset.mem_univ _
    have hsubset :
        ((Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.Nonempty))
          ⊆ (Finset.univ : Finset (Finset (Fin N))).erase ∅ := by
      intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      exact Finset.mem_erase.2 ⟨Finset.nonempty_iff_ne_empty.1 hS, Finset.mem_univ _⟩
    calc _ ≤ ((Finset.univ : Finset (Finset (Fin N))).erase ∅).card :=
            Finset.card_le_card hsubset
      _ = Fintype.card (Finset (Fin N)) - 1 := by
            rw [Finset.card_erase_of_mem hmem]; rfl
  have hcard : Fintype.card (Finset (Fin N)) = 2 ^ N := by
    simp [Fintype.card_finset]
  rw [hcard] at hsub
  have hpow : (2:ℕ) ^ N ≤ 2 ^ (112:ℕ) := Nat.pow_le_pow_right (by norm_num) hN
  omega

/-- **`enormous_bounds_are_not_effectivity`.**  `KERNEL-PROVED`.  The finite ceiling `2^112−1`
exceeds the public finite bank ceiling `4·10⁹`, so it is not an effectivity closure. -/
theorem enormous_bounds_are_not_effectivity :
    (4000000000 : ℕ) < 2 ^ (112 : ℕ) - 1 := by
  norm_num

end September2OneSlotPerron
end Erdos287
