import Mathlib
import RequestProject.CurrentProgramme.SharedG0PrimitiveUParam
import RequestProject.CurrentProgramme.LevelPairProductModulus

/-!
# Fixed-`D` frequency rigidity — Erdős #287, ONE-LEVEL MÖBIUS Δ, §4

**Exact integer algebra only.**

With

```
g₁ = g₀r₁,   g₂ = g₀r₂,   n = r₁r₂,   D = t₁r₂ - t₂r₁,
```

the fixed-`D` frequency pair is completely rigid modulo one shared degree of freedom:

* `t1_congr_mod_r1` — `t₁ ≡ D·r₂⁻¹ (mod r₁)`;
* `t2_congr_mod_r2` — `t₂ ≡ -D·r₁⁻¹ (mod r₂)`;
* `fixedD_solution_of_bezout` — for any Bézout pair `x r₂ - y r₁ = 1` and any `u`, the pair
  `t₁ = xD + r₁u`, `t₂ = yD + r₂u` solves `t₁r₂ - t₂r₁ = D`;
* `fixedD_solution_iff` — and conversely, these are *all* the solutions
  (`DET1-FIXEDD-FREQUENCY-RIGIDITY45`, general integer solution);
* `fixedD_u_period_g0` — the residues `t₁ mod g₁`, `t₂ mod g₂` depend only on `u mod g₀`:
  the remaining shared degree of freedom is exactly `u mod g₀`;
* `primitive_split_g0_r`, `primitive_r_side_independent_of_u`,
  `fixedD_primitive_reduces_to_g0_side` — the primitivity restrictions
  `gcd(t₁,g₁) = gcd(t₂,g₂) = 1` split into a `u`-independent `r`-side condition and exactly
  the `g₀`-side conditions used by the research source.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace LevelPairRigidity

/-! ## §4.1  The two congruences -/

/-- **`t₁ ≡ D·r₂⁻¹ (mod r₁)`.**  `LEAN_PROVED`.

Here `w₂` is any inverse of `r₂` modulo `r₁`. -/
theorem t1_congr_mod_r1 {r1 r2 t1 t2 D w2 : ℤ} (hD : t1 * r2 - t2 * r1 = D)
    (hw : r1 ∣ r2 * w2 - 1) : r1 ∣ t1 - D * w2 := by
  obtain ⟨c, hc⟩ := hw
  refine ⟨t1 * (-c) + t2 * w2, ?_⟩
  have : t1 - D * w2 = -(t1 * (r2 * w2 - 1)) + r1 * (t2 * w2) := by
    rw [← hD]; ring
  rw [this, hc]
  ring

/-- **`t₂ ≡ -D·r₁⁻¹ (mod r₂)`.**  `LEAN_PROVED`.

Here `w₁` is any inverse of `r₁` modulo `r₂`. -/
theorem t2_congr_mod_r2 {r1 r2 t1 t2 D w1 : ℤ} (hD : t1 * r2 - t2 * r1 = D)
    (hw : r2 ∣ r1 * w1 - 1) : r2 ∣ t2 - (-D) * w1 := by
  obtain ⟨c, hc⟩ := hw
  refine ⟨t2 * (-c) + t1 * w1, ?_⟩
  have : t2 - (-D) * w1 = -(t2 * (r1 * w1 - 1)) + r2 * (t1 * w1) := by
    rw [← hD]; ring
  rw [this, hc]
  ring

/-! ## §4.2  The general integer solution -/

/-- Every `(x,y)`-shifted pair solves the fixed-`D` equation. -/
theorem fixedD_solution_of_bezout {r1 r2 x y D : ℤ} (hxy : x * r2 - y * r1 = 1) (u : ℤ) :
    (x * D + r1 * u) * r2 - (y * D + r2 * u) * r1 = D := by
  have : (x * D + r1 * u) * r2 - (y * D + r2 * u) * r1 = D * (x * r2 - y * r1) := by ring
  rw [this, hxy, mul_one]

/-- **`DET1-FIXEDD-FREQUENCY-RIGIDITY45`, general integer solution.**  `LEAN_PROVED`.

For coprime `r₁,r₂` with `r₁ ≠ 0` and any Bézout pair `x r₂ - y r₁ = 1`, the solutions of
`t₁r₂ - t₂r₁ = D` are exactly

```
t₁ = xD + r₁u,   t₂ = yD + r₂u,   u ∈ ℤ.
``` -/
theorem fixedD_solution_iff {r1 r2 x y D t1 t2 : ℤ} (hcop : IsCoprime r1 r2) (hr1 : r1 ≠ 0)
    (hxy : x * r2 - y * r1 = 1) :
    t1 * r2 - t2 * r1 = D ↔ ∃ u : ℤ, t1 = x * D + r1 * u ∧ t2 = y * D + r2 * u := by
  have h0 : r2 * (x * D) - r1 * (y * D) = D := by
    have : r2 * (x * D) - r1 * (y * D) = D * (x * r2 - y * r1) := by ring
    rw [this, hxy, mul_one]
  have := Erdos287.SharedG0Param.sharedG0_u_param_iff (r1 := r1) (r2 := r2) (t1 := t1) (t2 := t2)
    (t10 := x * D) (t20 := y * D) (D := D) hcop hr1 h0
  constructor
  · intro h
    exact this.1 (by linarith [h])
  · intro h
    have := this.2 h
    linarith [this]

/-! ## §4.3  The remaining degree of freedom is `u mod g₀` -/

/-- **`DET1-FIXEDD-FREQUENCY-RIGIDITY45`, shared degree of freedom.**  `LEAN_PROVED`.

Shifting `u` by a multiple of `g₀` changes `t₁` by a multiple of `g₁ = g₀r₁` and `t₂` by a
multiple of `g₂ = g₀r₂`.  Hence, once `D` and the Bézout pair are fixed, the frequency pair
`(t₁ mod g₁, t₂ mod g₂)` depends only on `u mod g₀`. -/
theorem fixedD_u_period_g0 {g0 r1 r2 x y D u u' : ℤ} (h : g0 ∣ u - u') :
    (g0 * r1 ∣ (x * D + r1 * u) - (x * D + r1 * u')) ∧
      (g0 * r2 ∣ (y * D + r2 * u) - (y * D + r2 * u')) := by
  obtain ⟨c, hc⟩ := h
  constructor
  · refine ⟨c, ?_⟩
    have : (x * D + r1 * u) - (x * D + r1 * u') = r1 * (u - u') := by ring
    rw [this, hc]; ring
  · refine ⟨c, ?_⟩
    have : (y * D + r2 * u) - (y * D + r2 * u') = r2 * (u - u') := by ring
    rw [this, hc]; ring

/-! ## §4.4  The primitive restrictions are exactly `g₀`-side conditions -/

/-- Primitivity at a level splits into the shared part and the cofactor part. -/
theorem primitive_split_g0_r (t g0 r : ℤ) :
    Int.gcd t (g0 * r) = 1 ↔ Int.gcd t g0 = 1 ∧ Int.gcd t r = 1 := by
  simp [← Int.isCoprime_iff_gcd_eq_one, IsCoprime.mul_right_iff]

/-- The cofactor-side condition does not see `u`. -/
theorem primitive_r_side_independent_of_u (a r u : ℤ) :
    Int.gcd (a + r * u) r = Int.gcd a r := by
  simp [Int.gcd_add_mul_left_left r a u]

/-- **`DET1-FIXEDD-FREQUENCY-RIGIDITY45`, primitive reduction.**  `LEAN_PROVED`.

Along the solution line `t₁ = xD + r₁u`, `t₂ = yD + r₂u`, the two primitivity conditions
decouple into a `u`-independent cofactor condition and exactly the two `g₀`-side conditions

```
gcd(xD + r₁u, g₀) = 1,   gcd(yD + r₂u, g₀) = 1,
```

which by `fixedD_u_period_g0` depend only on `u mod g₀`. -/
theorem fixedD_primitive_reduces_to_g0_side {g0 r1 r2 x y D u : ℤ} :
    (Int.gcd (x * D + r1 * u) (g0 * r1) = 1 ∧ Int.gcd (y * D + r2 * u) (g0 * r2) = 1) ↔
      ((Int.gcd (x * D) r1 = 1 ∧ Int.gcd (y * D) r2 = 1) ∧
        (Int.gcd (x * D + r1 * u) g0 = 1 ∧ Int.gcd (y * D + r2 * u) g0 = 1)) := by
  rw [primitive_split_g0_r, primitive_split_g0_r, primitive_r_side_independent_of_u,
    primitive_r_side_independent_of_u]
  tauto

end LevelPairRigidity
end Erdos287
