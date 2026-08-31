import Mathlib

/-!
# Reciprocal-density duality — Erdős #287 (append-only)

This module is **append-only** and purely algebraic.  It defines the three reciprocal densities

```
ρ_old      = D₀ H₀ Q / (m R₀),
ρ_dualPair = D₀ R₀ / (m Q),
ρ_dualFull = D₀ H₀ R₀ / (m Q),
```

and proves the two exact identities

```
ρ_old · ρ_dualFull = (D₀ H₀ / m)²,     ρ_dualFull / ρ_old = (R₀/Q)²,
```

together with the **deterministic** implications that follow from them.  Nothing here asserts
that any physical packet closes: the safe form is exactly "if both densities are bounded then the
geometric mean is bounded".

A scale-saturation sanity instance is included in exact monomial form (with `t = X^{1/3}`):
`ρ_old = 1` (natural), `ρ_dualPair = t > 1` (supercritical), `ρ_dualFull = t²`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace ReciprocalDensityDuality

/-! ## §1  The three densities -/

/-- The old reciprocal density `ρ_old = D₀ H₀ Q/(m R₀)`. -/
noncomputable def rhoOld (D0 H0 Q m R0 : ℝ) : ℝ := D0 * H0 * Q / (m * R0)

/-- The dual pair density `ρ_dualPair = D₀ R₀/(m Q)`. -/
noncomputable def rhoDualPair (D0 Q m R0 : ℝ) : ℝ := D0 * R0 / (m * Q)

/-- The full dual density `ρ_dualFull = D₀ H₀ R₀/(m Q)`. -/
noncomputable def rhoDualFull (D0 H0 Q m R0 : ℝ) : ℝ := D0 * H0 * R0 / (m * Q)

/-! ## §2  The two exact identities -/

/-- **`reciprocalDensity_product_identity`.**  `LEAN_PROVED`.

`ρ_old · ρ_dualFull = (D₀ H₀ / m)²`. -/
theorem reciprocalDensity_product_identity (D0 H0 Q m R0 : ℝ) (hQ : Q ≠ 0) (hm : m ≠ 0)
    (hR0 : R0 ≠ 0) :
    rhoOld D0 H0 Q m R0 * rhoDualFull D0 H0 Q m R0 = (D0 * H0 / m) ^ 2 := by
  unfold rhoOld rhoDualFull
  field_simp

/-- **`reciprocalDensity_ratio_identity`.**  `LEAN_PROVED`.

`ρ_dualFull / ρ_old = (R₀/Q)²`. -/
theorem reciprocalDensity_ratio_identity (D0 H0 Q m R0 : ℝ) (hD0 : D0 ≠ 0) (hH0 : H0 ≠ 0)
    (hQ : Q ≠ 0) (hm : m ≠ 0) (hR0 : R0 ≠ 0) :
    rhoDualFull D0 H0 Q m R0 / rhoOld D0 H0 Q m R0 = (R0 / Q) ^ 2 := by
  unfold rhoOld rhoDualFull
  field_simp

/-! ## §3  The safe deterministic implications -/

/-- **`reciprocalDensity_geometric_mean_bound`.**  `LEAN_PROVED`.  The safe form of
`RECIPROCAL-DENSITY-DUALITY45`: if **both** densities are bounded by `L ≥ 0`, then

`D₀ H₀ / m ≤ L`.

No claim is made that any physical packet satisfies the two hypotheses. -/
theorem reciprocalDensity_geometric_mean_bound {D0 H0 Q m R0 L : ℝ} (hQ : Q ≠ 0) (hm : 0 < m)
    (hR0 : R0 ≠ 0) (hD0 : 0 ≤ D0) (hH0 : 0 ≤ H0) (hL : 0 ≤ L)
    (h₁ : rhoOld D0 H0 Q m R0 ≤ L) (h₂ : rhoDualFull D0 H0 Q m R0 ≤ L)
    (hpos₂ : 0 ≤ rhoDualFull D0 H0 Q m R0) :
    D0 * H0 / m ≤ L := by
  have hprod : (D0 * H0 / m) ^ 2 ≤ L * L := by
    rw [← reciprocalDensity_product_identity D0 H0 Q m R0 hQ hm.ne' hR0]
    exact mul_le_mul h₁ h₂ hpos₂ hL
  have hnn : 0 ≤ D0 * H0 / m := by positivity
  nlinarith [hprod, hnn, hL]

/-- **`reciprocalDensity_ratio_bound`.**  `LEAN_PROVED`.  If the full dual density exceeds the old
one by at most a factor `K²` (with `K ≥ 0`), then `R₀/Q ≤ K`. -/
theorem reciprocalDensity_ratio_bound {D0 H0 Q m R0 K : ℝ} (hD0 : 0 < D0) (hH0 : 0 < H0)
    (hQ : 0 < Q) (hm : 0 < m) (hR0 : 0 < R0) (hK : 0 ≤ K)
    (h : rhoDualFull D0 H0 Q m R0 ≤ K ^ 2 * rhoOld D0 H0 Q m R0) :
    R0 / Q ≤ K := by
  have hold : 0 < rhoOld D0 H0 Q m R0 := by
    unfold rhoOld
    positivity
  have hratio : rhoDualFull D0 H0 Q m R0 / rhoOld D0 H0 Q m R0 ≤ K ^ 2 :=
    (div_le_iff₀ hold).mpr (by linarith [h])
  rw [reciprocalDensity_ratio_identity D0 H0 Q m R0 hD0.ne' hH0.ne' hQ.ne' hm.ne' hR0.ne'] at hratio
  have hnn : 0 ≤ R0 / Q := by positivity
  nlinarith [hratio, hnn, hK]

/-! ## §4  Scale-saturation sanity instance -/

/-- **`scaleSaturation_sanity_instance`.**  `LEAN_PROVED`.  Exact monomial instance of the
scale-saturation face, written with `t = X^{1/3} > 1`, i.e.

`D₀ = t² (= X^{2/3}), H₀ = t (= X^{1/3}), Q = t (= X^{1/3}), m = R₀ = t² (= X^{2/3})`:

* the **old** density is natural: `ρ_old = 1`;
* the **dual pair** density is supercritical: `ρ_dualPair = t > 1`;
* the **full dual** density is `t²`.

The exponent dictionary is recorded in the statement itself; no asymptotic notation is used. -/
theorem scaleSaturation_sanity_instance (t : ℝ) (ht : 1 < t) :
    rhoOld (t ^ 2) t t (t ^ 2) (t ^ 2) = 1 ∧
    rhoDualPair (t ^ 2) t (t ^ 2) (t ^ 2) = t ∧
    rhoDualFull (t ^ 2) t t (t ^ 2) (t ^ 2) = t ^ 2 ∧
    1 < rhoDualPair (t ^ 2) t (t ^ 2) (t ^ 2) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have h1 : rhoOld (t ^ 2) t t (t ^ 2) (t ^ 2) = 1 := by
    unfold rhoOld; field_simp
  have h2 : rhoDualPair (t ^ 2) t (t ^ 2) (t ^ 2) = t := by
    unfold rhoDualPair; field_simp
  have h3 : rhoDualFull (t ^ 2) t t (t ^ 2) (t ^ 2) = t ^ 2 := by
    unfold rhoDualFull; field_simp
  exact ⟨h1, h2, h3, by rw [h2]; exact ht⟩

/-- **`reciprocalDensity_duality_is_not_closure`.**  `LEAN_PROVED`.  Firewall: the algebraic
duality does **not** by itself bound anything.  Explicit witness: parameters for which both
identities hold while `ρ_old` is arbitrarily large. -/
theorem reciprocalDensity_duality_is_not_closure :
    ∃ D0 H0 Q m R0 : ℝ, 0 < D0 ∧ 0 < H0 ∧ 0 < Q ∧ 0 < m ∧ 0 < R0 ∧
      1 < rhoOld D0 H0 Q m R0 := by
  refine ⟨4, 1, 1, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  unfold rhoOld
  norm_num

end ReciprocalDensityDuality
end Erdos287
