import Mathlib
import RequestProject.CurrentProgramme.OneLevelProjectorS1S2
import RequestProject.CurrentProgramme.OneLevelWeightedLargeSieve

/-!
# §§7–10 — Global `Q_H`, the normalised ratio, and the true critical range

`CASE-B ONE-LEVEL PRIMITIVE-FRACTION LARGE SIEVE`, Sections 7–10.

* §7 `global_QH_bound` — combining the fixed-`d` bound of Section 5 with `S1`, `S2` of
  Section 6:

  ```
  |Q_H| ≤ K · ( A·c₁(1 + log⌊X/H⌋) + 8c₁G²/H ),      K = B(1+B/G)L^{C_E}.
  ```

  `global_QH_envelope` is the common-log form `|Q_H| ≪ B(1+B/G)(A + G²/H)L^{C_E+1}`.

* §8 `normalised_ratio_identity` — the exact four-term decomposition of `|Q_H|/(AB²)`, all four
  terms checked independently:

  ```
  L₁/B + L₁/G + L₀G²/(HX) + L₀G/(HA),      X = AB.
  ```

* §9 `logPow_div_rpow_tendsto_zero` — a polynomial lower bound beats every fixed power of the
  logarithm.  This is the *conditional* form of the small-`B` / small-`G` closure; the source
  pins `B ≥ X^{η_B}`, `G > X^{1/2-η₀}` are **not** available in this repository and are not
  asserted anywhere here.

* §10 `branch_G2_over_HX_closes`, `branch_G_over_HA_closes` — each of the two `H`-branches
  closes above the stated threshold, so the unresolved range is
  `H ≤ L^{C_E+K} max(G²/X, G/A)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset ArithmeticFunction Filter Asymptotics

namespace Erdos287
namespace OneLevelGlobal

open Erdos287.SharedGcdGram
open Erdos287.OneLevelProjector

/-! ## §7  The global `Q_H` bound -/

/-- **`DET1-ONELEVEL-PRIMITIVEFRACTION-GLOBAL45`, sharp form.**  `LEAN_PROVED`
(conditional on the fixed-`d` input `hGd` and on the `Ω_H` mass pin `hmass`).

```
|Q_H| ≤ K · ( A c₁ (1 + log⌊X/H⌋) + 8 c₁ G²/H ),
```

where `K = B(1+B/G)L^{C_E}` is the Section 5 constant and `hQ` is the triangle inequality for
the signed projector `∑_d λ_H(d)/d² G_{H,d}`. -/
theorem global_QH_bound {X H : ℕ} (hH : 0 < H) (Om : ℕ → ℝ)
    (hsupp : ∀ e, e < H → Om e = 0) (Gd : ℕ → ℝ) (Q Alen Gfreq K c1 : ℝ)
    (hQ : |Q| ≤ ∑ d ∈ Finset.Icc 1 X, |lambdaH Om d| / (d : ℝ) ^ 2 * Gd d)
    (hGd : ∀ d ∈ Finset.Icc 1 X, Gd d ≤ (Alen * (d : ℝ) + 4 * Gfreq ^ 2) * K)
    (hK : 0 ≤ K) (hAlen : 0 ≤ Alen)
    (hmass : ∑ e ∈ Finset.Icc 1 X, |Om e| / (e : ℝ) ≤ c1) :
    |Q| ≤ K * (Alen * (c1 * (1 + Real.log ((X / H : ℕ) : ℝ))) + 4 * Gfreq ^ 2 * (2 * c1 / H)) := by
  have hS1 := projector_S1_bound Om hH hsupp X c1 hmass
  have hS2 := projector_S2_bound Om hH hsupp X c1 hmass
  have hc1 : (0 : ℝ) ≤ c1 :=
    le_trans (Finset.sum_nonneg (fun e _ => by positivity)) hmass
  -- termwise upper bound
  have hterm : ∀ d ∈ Finset.Icc 1 X,
      |lambdaH Om d| / (d : ℝ) ^ 2 * Gd d
        ≤ K * (Alen * (|lambdaH Om d| / (d : ℝ)) + 4 * Gfreq ^ 2 * (|lambdaH Om d| / (d : ℝ) ^ 2))
      := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd.1
    have hnn : (0 : ℝ) ≤ |lambdaH Om d| / (d : ℝ) ^ 2 := by positivity
    have h1 : |lambdaH Om d| / (d : ℝ) ^ 2 * Gd d
        ≤ |lambdaH Om d| / (d : ℝ) ^ 2 * ((Alen * (d : ℝ) + 4 * Gfreq ^ 2) * K) :=
      mul_le_mul_of_nonneg_left (hGd d (Finset.mem_Icc.mpr hd)) hnn
    refine le_trans h1 (le_of_eq ?_)
    field_simp
  refine le_trans hQ (le_trans (Finset.sum_le_sum hterm) ?_)
  rw [← Finset.mul_sum]
  have hsplit : ∑ d ∈ Finset.Icc 1 X,
      (Alen * (|lambdaH Om d| / (d : ℝ)) + 4 * Gfreq ^ 2 * (|lambdaH Om d| / (d : ℝ) ^ 2))
      = Alen * (∑ d ∈ Finset.Icc 1 X, |lambdaH Om d| / (d : ℝ))
        + 4 * Gfreq ^ 2 * (∑ d ∈ Finset.Icc 1 X, |lambdaH Om d| / (d : ℝ) ^ 2) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hsplit]
  refine mul_le_mul_of_nonneg_left ?_ hK
  have hGfreq : (0 : ℝ) ≤ 4 * Gfreq ^ 2 := by positivity
  exact add_le_add (mul_le_mul_of_nonneg_left hS1 hAlen)
    (mul_le_mul_of_nonneg_left hS2 hGfreq)

/-- **`DET1-ONELEVEL-PRIMITIVEFRACTION-GLOBAL45`, common-log envelope.**  `LEAN_PROVED`.

If the log parameter dominates the local logarithm, `1 + log⌊X/H⌋ ≤ Lg` and `1 ≤ Lg`, the sharp
bound collapses to `|Q_H| ≤ 8c₁·K·(A + G²/H)·Lg`, i.e. one extra power of the logarithm. -/
theorem global_QH_envelope (Alen Gfreq H K c1 Lg logloc : ℝ) (hK : 0 ≤ K) (hAlen : 0 ≤ Alen)
    (hc1 : 0 ≤ c1) (hH : 0 < H) (hLg : 1 ≤ Lg) (hloc : logloc ≤ Lg) :
    K * (Alen * (c1 * logloc) + 4 * Gfreq ^ 2 * (2 * c1 / H))
      ≤ 8 * c1 * K * (Alen + Gfreq ^ 2 / H) * Lg := by
  have h1 : Alen * (c1 * logloc) ≤ Alen * (c1 * Lg) := by
    have : c1 * logloc ≤ c1 * Lg := mul_le_mul_of_nonneg_left hloc hc1
    exact mul_le_mul_of_nonneg_left this hAlen
  have h2 : 4 * Gfreq ^ 2 * (2 * c1 / H) ≤ 8 * c1 * (Gfreq ^ 2 / H) * Lg := by
    have hbase : 4 * Gfreq ^ 2 * (2 * c1 / H) = 8 * c1 * (Gfreq ^ 2 / H) := by
      field_simp
      ring
    rw [hbase]
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hc1)
      (div_nonneg (sq_nonneg Gfreq) hH.le)]
  have h3 : Alen * (c1 * Lg) ≤ 8 * c1 * Alen * Lg := by
    nlinarith [mul_nonneg (mul_nonneg hAlen hc1) (le_trans zero_le_one hLg)]
  have hsum : K * (Alen * (c1 * logloc) + 4 * Gfreq ^ 2 * (2 * c1 / H))
      ≤ K * (8 * c1 * Alen * Lg + 8 * c1 * (Gfreq ^ 2 / H) * Lg) := by
    refine mul_le_mul_of_nonneg_left ?_ hK
    linarith
  refine le_trans hsum (le_of_eq ?_)
  ring

/-! ## §8  The normalised ratio -/

/-- **Normalised ratio, exact four-term form.**  `LEAN_PROVED`.

With `X = AB`,

```
B(1+B/G)(A L₁ + (G²/H)L₀) / (A B²) = L₁/B + L₁/G + L₀G²/(HX) + L₀G/(HA).
```

Each of the four terms is produced by exactly one of the four products, so the four branches
`1/B`, `1/G`, `G²/(HX)`, `G/(HA)` are independent. -/
theorem normalised_ratio_identity (Alen B Gfreq H X L1 L0 : ℝ)
    (hA : Alen ≠ 0) (hB : B ≠ 0) (hG : Gfreq ≠ 0) (hH : H ≠ 0) (hX : X = Alen * B) :
    (B * (1 + B / Gfreq) * (Alen * L1 + Gfreq ^ 2 / H * L0)) / (Alen * B ^ 2)
      = L1 / B + L1 / Gfreq + L0 * Gfreq ^ 2 / (H * X) + L0 * Gfreq / (H * Alen) := by
  subst hX
  field_simp
  ring

/-! ## §9  A polynomial lower bound beats every fixed power of the logarithm -/

/-- **`logPow_div_rpow_tendsto_zero`.**  `LEAN_PROVED`.

For every fixed `K : ℕ` and every fixed `η > 0`, `(log X)^K / X^η → 0`. -/
theorem logPow_div_rpow_tendsto_zero (K : ℕ) {eta : ℝ} (heta : 0 < eta) :
    Tendsto (fun X : ℝ => (Real.log X) ^ K / X ^ eta) atTop (nhds 0) := by
  have h2 := (isLittleO_log_rpow_rpow_atTop (K : ℝ) heta).tendsto_div_nhds_zero
  simpa [Real.rpow_natCast] using h2

/-- **Conditional small-`B` closure.**  `LEAN_PROVED`.

*If* the source supplied a polynomial lower bound `B ≥ X^{η_B}` with fixed `η_B > 0`, then for
every prescribed `ε > 0` and every fixed logarithmic power `K` the ratio `L^K/B` is eventually
`≤ ε`.  The hypothesis is supplied by the caller: this repository contains no proof of any such
lower bound. -/
theorem logPow_div_le_of_polynomial_lower (K : ℕ) {eta eps : ℝ} (heta : 0 < eta)
    (heps : 0 < eps) :
    ∀ᶠ X : ℝ in atTop, ∀ B : ℝ, X ^ eta ≤ B → (Real.log X) ^ K / B ≤ eps := by
  have hlim := logPow_div_rpow_tendsto_zero K heta
  have hev : ∀ᶠ X : ℝ in atTop, (Real.log X) ^ K / X ^ eta < eps := by
    have := hlim.eventually (eventually_lt_nhds heps)
    exact this
  filter_upwards [hev, eventually_gt_atTop (1 : ℝ)] with X hX hX1 B hB
  have hXeta : (0 : ℝ) < X ^ eta := Real.rpow_pos_of_pos (by linarith) eta
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le hXeta hB
  have hlogpos : (0 : ℝ) ≤ (Real.log X) ^ K := by
    have : (0 : ℝ) ≤ Real.log X := Real.log_nonneg (le_of_lt hX1)
    positivity
  calc (Real.log X) ^ K / B ≤ (Real.log X) ^ K / X ^ eta := by
        exact div_le_div_of_nonneg_left hlogpos hXeta hB |>.trans_eq rfl
    _ ≤ eps := le_of_lt hX

/-! ## §10  The true critical range -/

/-- **`G²/(HX)` branch.**  `LEAN_PROVED`.

If `H ≥ (G²/X)·Lg^{C_E+K}` then `Lg^{C_E}G²/(HX) ≤ Lg^{-K}`. -/
theorem branch_G2_over_HX_closes {Gfreq X H Lg : ℝ} (Ce K : ℕ) (hLg : 1 ≤ Lg) (hX : 0 < X)
    (hG : 0 < Gfreq) (hbig : (Gfreq ^ 2 / X) * Lg ^ (Ce + K) ≤ H) :
    Lg ^ Ce * Gfreq ^ 2 / (H * X) ≤ 1 / Lg ^ K := by
  have hLg0 : (0 : ℝ) < Lg := lt_of_lt_of_le zero_lt_one hLg
  have hthr : (0 : ℝ) < (Gfreq ^ 2 / X) * Lg ^ (Ce + K) := by positivity
  have hnum : (0 : ℝ) ≤ Lg ^ Ce * Gfreq ^ 2 := by positivity
  have hstep : Lg ^ Ce * Gfreq ^ 2 / (H * X)
      ≤ Lg ^ Ce * Gfreq ^ 2 / (((Gfreq ^ 2 / X) * Lg ^ (Ce + K)) * X) := by
    apply div_le_div_of_nonneg_left hnum (by positivity)
    exact mul_le_mul_of_nonneg_right hbig hX.le
  refine le_trans hstep (le_of_eq ?_)
  rw [pow_add]
  field_simp

/-- **`G/(HA)` branch.**  `LEAN_PROVED`.

If `H ≥ (G/A)·Lg^{C_E+K}` then `Lg^{C_E}G/(HA) ≤ Lg^{-K}`. -/
theorem branch_G_over_HA_closes {Gfreq Alen H Lg : ℝ} (Ce K : ℕ) (hLg : 1 ≤ Lg)
    (hA : 0 < Alen) (hG : 0 < Gfreq)
    (hbig : (Gfreq / Alen) * Lg ^ (Ce + K) ≤ H) :
    Lg ^ Ce * Gfreq / (H * Alen) ≤ 1 / Lg ^ K := by
  have hLg0 : (0 : ℝ) < Lg := lt_of_lt_of_le zero_lt_one hLg
  have hthr : (0 : ℝ) < (Gfreq / Alen) * Lg ^ (Ce + K) := by positivity
  have hnum : (0 : ℝ) ≤ Lg ^ Ce * Gfreq := by positivity
  have hstep : Lg ^ Ce * Gfreq / (H * Alen)
      ≤ Lg ^ Ce * Gfreq / (((Gfreq / Alen) * Lg ^ (Ce + K)) * Alen) := by
    apply div_le_div_of_nonneg_left hnum (by positivity)
    exact mul_le_mul_of_nonneg_right hbig hA.le
  refine le_trans hstep (le_of_eq ?_)
  rw [pow_add]
  field_simp

/-- **The unresolved union.**  `LEAN_PROVED`.

If `H` exceeds *both* thresholds then both branches are `≤ Lg^{-K}`; equivalently, the
unresolved range is contained in `H ≤ Lg^{C_E+K}·max(G²/X, G/A)`. -/
theorem critical_range_union {Gfreq Alen X H Lg : ℝ} (Ce K : ℕ) (hLg : 1 ≤ Lg) (hX : 0 < X)
    (hA : 0 < Alen) (hG : 0 < Gfreq)
    (hbig : max (Gfreq ^ 2 / X) (Gfreq / Alen) * Lg ^ (Ce + K) < H) :
    Lg ^ Ce * Gfreq ^ 2 / (H * X) ≤ 1 / Lg ^ K ∧
      Lg ^ Ce * Gfreq / (H * Alen) ≤ 1 / Lg ^ K := by
  have hLg0 : (0 : ℝ) < Lg := lt_of_lt_of_le zero_lt_one hLg
  have hpow : (0 : ℝ) < Lg ^ (Ce + K) := by positivity
  constructor
  · refine branch_G2_over_HX_closes Ce K hLg hX hG (le_of_lt (lt_of_le_of_lt ?_ hbig))
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hpow.le
  · refine branch_G_over_HA_closes Ce K hLg hA hG (le_of_lt (lt_of_le_of_lt ?_ hbig))
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hpow.le

end OneLevelGlobal
end Erdos287
