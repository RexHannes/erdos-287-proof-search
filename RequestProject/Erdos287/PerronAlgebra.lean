import Mathlib
import RequestProject.Erdos287.BsrcWeights

/-!
# Erdős #287 effectivity — Perron variable-change algebra and the strict-equality
correction (§19, §20)

```
PERRON VARIABLE CHANGE  : KERNEL-PROVED (algebra only; no contour theorem is claimed)
STRICT EQUALITY ALGEBRA : KERNEL-PROVED (conditional on strict Perron as a hypothesis)
```

The linear change `u = s + z`, `v = s − z` inverts to `s = (u+v)/2`, `z = (u−v)/2`;
the Jacobian matrix has determinant `−1/2`, i.e. `ds dz = ½ du dv`, and the Perron kernel
compensates exactly: `½ · (1/z) = 1/(u−v)`, while `c^{−s−z} = c^{−u}`.

**No contour-integration theorem is asserted here.**  §20 likewise only records the algebra:
the strict (half-jump) Perron evaluation is an explicit hypothesis, and the physical
`c = 1 / c = 2` outer factor `−4` then produces `2(Δ₁ − Δ₂)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos287
namespace Effectivity

/-! ## §19  The Perron variable change -/

/-- **`perron_change_of_variables`.**  `KERNEL-PROVED`.  `u = s+z`, `v = s−z` inverts to
`s = (u+v)/2`, `z = (u−v)/2`. -/
theorem perron_change_of_variables (s z : ℂ) :
    ((s + z) + (s - z)) / 2 = s ∧ ((s + z) - (s - z)) / 2 = z := by
  constructor <;> ring

/-- The Jacobian matrix of `(s,z) ↦ (u,v) = (s+z, s−z)`. -/
def perronJacobian : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 1, -1]

/-- The Jacobian matrix of the inverse map `(u,v) ↦ (s,z) = ((u+v)/2, (u−v)/2)`. -/
def perronJacobianInv : Matrix (Fin 2) (Fin 2) ℚ := !![1/2, 1/2; 1/2, -1/2]

/-- **`perronJacobian_det`.**  `KERNEL-PROVED`.  `det = −2`. -/
theorem perronJacobian_det : perronJacobian.det = -2 := by
  rw [perronJacobian, Matrix.det_fin_two_of]; ring

/-- **`perronJacobianInv_det`.**  `KERNEL-PROVED`.  `det = −1/2`, so `|det| = 1/2`:
`ds dz = ½ du dv`. -/
theorem perronJacobianInv_det : perronJacobianInv.det = -(1/2) := by
  rw [perronJacobianInv, Matrix.det_fin_two_of]; ring

theorem perronJacobianInv_abs_det : |perronJacobianInv.det| = 1 / 2 := by
  rw [perronJacobianInv_det]; norm_num

/-- **`perron_kernel_compensation`.**  `KERNEL-PROVED`.  With `z = (u−v)/2` and `u ≠ v`,
the Jacobian factor `1/2` and the Perron kernel `1/z` combine to `1/(u−v)`. -/
theorem perron_kernel_compensation {u v : ℂ} (huv : u ≠ v) :
    (1 / 2 : ℂ) * (1 / ((u - v) / 2)) = 1 / (u - v) := by
  have h : u - v ≠ 0 := sub_ne_zero.2 huv
  field_simp

/-- **`perron_exponent_record`.**  `KERNEL-PROVED`.  `c^{−s−z} = c^{−u}` for `u = s + z`. -/
theorem perron_exponent_record (c s z : ℂ) : c ^ (-s - z) = c ^ (-(s + z)) := by
  ring_nf

/-! ## §20  The strict-equality (half-jump) correction -/

/-- `Δ_c(X) = ∑_{2∤d} μ(d)[B(d) − B1]·W(c²d²/X)`. -/
def Delta (B1 : ℚ) (W : ℚ → ℚ) (X : ℚ) (Dset : Finset ℕ) (c : ℚ) : ℚ :=
  ∑ d ∈ Dset with ¬ (2 ∣ d), (moebius d : ℚ) * (B B1 d - B1) * W (c ^ 2 * (d : ℚ) ^ 2 / X)

/-- **`strict_perron_outer_factor`.**  `KERNEL-PROVED` as an implication.  If the strict
(half-jump) Perron evaluation contributes `−½·Δ_c` in each lane — this is the explicit
hypothesis, no Perron theorem is proved here — then the physical `c = 1 / c = 2` outer
factor `−4` gives exactly `2(Δ₁ − Δ₂)`. -/
theorem strict_perron_outer_factor {corr : ℚ → ℚ} {D1 D2 : ℚ}
    (hc1 : corr 1 = -(1 / 2) * D1) (hc2 : corr 2 = -(1 / 2) * D2) :
    (-4 : ℚ) * (corr 1 - corr 2) = 2 * (D1 - D2) := by
  rw [hc1, hc2]; ring

/-- The same statement with the two lanes instantiated at the `Δ_c` of this file. -/
theorem strict_perron_outer_factor_Delta (B1 : ℚ) (W : ℚ → ℚ) (X : ℚ) (Dset : Finset ℕ)
    {corr : ℚ → ℚ}
    (hc1 : corr 1 = -(1 / 2) * Delta B1 W X Dset 1)
    (hc2 : corr 2 = -(1 / 2) * Delta B1 W X Dset 2) :
    (-4 : ℚ) * (corr 1 - corr 2) = 2 * (Delta B1 W X Dset 1 - Delta B1 W X Dset 2) :=
  strict_perron_outer_factor hc1 hc2

end Effectivity
end Erdos287
