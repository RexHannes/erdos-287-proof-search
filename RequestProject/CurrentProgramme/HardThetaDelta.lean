import Mathlib
import RequestProject.CurrentProgramme.SmallROwnerSubtraction

/-!
# CurrentProgramme §10 — the hard-`θ` physical `δ = 1/21` repair

`HARD-THETA-PHYSICAL-DELTA45` — `ALGEBRAIC / CAPACITY PASS`.

Exact rational arithmetic:

```
    1/3 − 2/7 = 1/21,      5/7 − 2/3 = 1/21,      (1/21)/20 = 1/420.
```

The hard short-`t` source uses `T = X^{5/7 − θ}` and `z = T^{1/20}`.  The sieve saves
`1/log z`, *not* definitionally `1/log X`.  On the physical range `1/3 ≤ θ ≤ 2/3` one has
`5/7 − θ ≥ 1/21`, hence

```
    log z ≥ (1/420) log X       and       1/log z ≤ 420 / log X.
```

These two statements are **proved** here for the literal real powers (`Real.rpow`), so the
`O(1/log X)` physical budget is a theorem *given* a `1/log z` saving — no real-power
asymptotic step is faked.

The short-`t` analytic theorem itself remains external and open (see §11).

The historical pair `(2/7, 5/7)` is preserved only as *pointwise / open-interval* capacity
geometry: `no_uniform_delta_on_open_interval` shows there is no uniform positive `δ` there.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace CurrentProgramme

/-! ## §10.1  The exact rational ledger -/

/-- The repaired physical `δ`. -/
def hardDelta : ℚ := 1 / 21

/-- The sieve level exponent `1/20` of the short-`t` source. -/
def hardSieveLevelExponent : ℚ := 1 / 20

/-- The resulting log-scale constant `δ/20 = 1/420`. -/
def hardLogScale : ℚ := hardDelta * hardSieveLevelExponent

theorem hardDelta_lower_endpoint : (1 : ℚ) / 3 - 2 / 7 = hardDelta := by
  unfold hardDelta; norm_num

theorem hardDelta_upper_endpoint : (5 : ℚ) / 7 - 2 / 3 = hardDelta := by
  unfold hardDelta; norm_num

theorem hardLogScale_eq : hardLogScale = 1 / 420 := by
  unfold hardLogScale hardDelta hardSieveLevelExponent; norm_num

theorem hardDelta_pos : 0 < hardDelta := by unfold hardDelta; norm_num

/-- **`hard_physical_range_delta`.**  `LEAN_PROVED` (exact rational arithmetic).

On the physical range `1/3 ≤ θ ≤ 2/3` the short-`t` exponent satisfies `5/7 − θ ≥ 1/21`.
Only the upper endpoint `θ ≤ 2/3` is load-bearing, so that is the stated hypothesis. -/
theorem hard_physical_range_delta {theta : ℚ} (h2 : theta ≤ 2 / 3) :
    hardDelta ≤ 5 / 7 - theta := by
  unfold hardDelta
  linarith

/-! ## §10.2  The real log-scale ledger -/

/-- The short-`t` height `T = X^{5/7 − θ}`. -/
noncomputable def hardT (X theta : ℝ) : ℝ := X ^ (5 / 7 - theta)

/-- The sieve cutoff `z = T^{1/20}`. -/
noncomputable def hardZ (X theta : ℝ) : ℝ := (hardT X theta) ^ ((1 : ℝ) / 20)

/-- **`log_hardZ_eq`.**  `LEAN_PROVED`.

`log z = (1/20)·(5/7 − θ)·log X` for the literal real powers. -/
theorem log_hardZ_eq {X : ℝ} (hX : 0 < X) (theta : ℝ) :
    Real.log (hardZ X theta) = (1 / 20) * ((5 / 7 - theta) * Real.log X) := by
  unfold hardZ hardT
  rw [Real.log_rpow (Real.rpow_pos_of_pos hX _), Real.log_rpow hX]

/-- **`log_hardZ_lower_bound`.**  `LEAN_PROVED`.

For `θ ≤ 2/3` (in particular on the physical range `1/3 ≤ θ ≤ 2/3`) and `X ≥ 3`:
`log z ≥ (1/420) log X`. -/
theorem log_hardZ_lower_bound {X theta : ℝ} (hX : 3 ≤ X) (h2 : theta ≤ 2 / 3) :
    (1 / 420) * Real.log X ≤ Real.log (hardZ X theta) := by
  have hXpos : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  rw [log_hardZ_eq hXpos theta]
  have hcoef : (1 : ℝ) / 21 ≤ 5 / 7 - theta := by linarith
  nlinarith [hlog, hcoef]

/-- **`log_hardZ_pos`.**  `LEAN_PROVED`. -/
theorem log_hardZ_pos {X theta : ℝ} (hX : 3 ≤ X) (h2 : theta ≤ 2 / 3) :
    0 < Real.log (hardZ X theta) := by
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have := log_hardZ_lower_bound hX h2
  nlinarith

/-- **`inv_log_hardZ_bound`.**  `LEAN_PROVED`.

The physical-range budget: `1/log z ≤ 420 / log X`.  This is the exact step at which the
sieve's natural saving `1/log z` becomes an `O(1/log X)` budget, and `δ = 1/21` is what
makes it work.  Only `θ ≤ 2/3` is needed. -/
theorem inv_log_hardZ_bound {X theta : ℝ} (hX : 3 ≤ X) (h2 : theta ≤ 2 / 3) :
    1 / Real.log (hardZ X theta) ≤ 420 / Real.log X := by
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hz : 0 < Real.log (hardZ X theta) := log_hardZ_pos hX h2
  have hle : Real.log X / 420 ≤ Real.log (hardZ X theta) := by
    have := log_hardZ_lower_bound hX h2
    linarith
  have h420 : (0 : ℝ) < Real.log X / 420 := by linarith
  calc 1 / Real.log (hardZ X theta) ≤ 1 / (Real.log X / 420) :=
        one_div_le_one_div_of_le h420 hle
    _ = 420 / Real.log X := by field_simp

/-- **`physical_range_budget_of_sieve_saving`.**  `LEAN_PROVED` (conditional compiler).

If a short-`t` source supplies a saving in the *sieve* variable, `|R| ≤ C / log z`, then for `θ ≤ 2/3` the physical budget `|R| ≤ 420·C / log X` follows. -/
theorem physical_range_budget_of_sieve_saving {X theta C R : ℝ} (hX : 3 ≤ X)
    (h2 : theta ≤ 2 / 3) (hC : 0 ≤ C)
    (hsave : |R| ≤ C / Real.log (hardZ X theta)) :
    |R| ≤ 420 * C / Real.log X := by
  refine le_trans hsave ?_
  have hb := inv_log_hardZ_bound hX h2
  have hz : 0 < Real.log (hardZ X theta) := log_hardZ_pos hX h2
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  calc C / Real.log (hardZ X theta) = C * (1 / Real.log (hardZ X theta)) := by ring
    _ ≤ C * (420 / Real.log X) := by exact mul_le_mul_of_nonneg_left hb hC
    _ = 420 * C / Real.log X := by ring

/-! ## §10.3  The open-interval capacity geometry -/

/-- **`no_uniform_delta_on_open_interval`.**  `LEAN_PROVED`.

The historical pair `(2/7, 5/7)` is only *pointwise* capacity geometry: on the open interval
`θ ∈ (2/7, 5/7)` the quantity `5/7 − θ` is positive but has no uniform positive lower bound,
so no endpoint-uniform statement may be inferred from it. -/
theorem no_uniform_delta_on_open_interval :
    (∀ theta : ℚ, 2 / 7 < theta → theta < 5 / 7 → 0 < 5 / 7 - theta) ∧
      ∀ eps : ℚ, 0 < eps → ∃ theta : ℚ, 2 / 7 < theta ∧ theta < 5 / 7 ∧ 5 / 7 - theta < eps := by
  constructor
  · intro theta _ h2; linarith
  · intro eps heps
    refine ⟨5 / 7 - min eps (1 / 7) / 2, ?_, ?_, ?_⟩
    · have h1 : min eps (1 / 7) ≤ 1 / 7 := min_le_right _ _
      linarith
    · have h2 : 0 < min eps (1 / 7) := lt_min heps (by norm_num)
      linarith
    · have h3 : min eps (1 / 7) ≤ eps := min_le_left _ _
      have h2 : 0 < min eps (1 / 7) := lt_min heps (by norm_num)
      simp only [sub_sub_cancel]
      linarith

/-- **`hardDelta_range_is_not_the_open_interval`.**  `LEAN_PROVED`.

The uniform `δ = 1/21` statement holds on the closed physical range `[1/3, 2/3]`, which is
strictly inside `(2/7, 5/7)`. -/
theorem hardDelta_range_is_not_the_open_interval :
    (2 : ℚ) / 7 < 1 / 3 ∧ (2 : ℚ) / 3 < 5 / 7 ∧
      ∀ theta : ℚ, 1 / 3 ≤ theta → theta ≤ 2 / 3 → hardDelta ≤ 5 / 7 - theta :=
  ⟨by norm_num, by norm_num, fun _ _ h2 => hard_physical_range_delta h2⟩

end CurrentProgramme
end Erdos287
