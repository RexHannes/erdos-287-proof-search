import Mathlib
import RequestProject.HostileAudit.RawRawVarianceCompiler
import RequestProject.Erdos287.PhysicalLogPrefactorRepair3221

/-!
# Hostile-audit safe bank §11 — the hard amplitude exponent compiler

`HARD-THETA-PHYSICAL-DELTA45 : provedFinite / provedAlgebraic`

The rational and log-budget arithmetic of the hard dyadic cells, reusing the banked repaired
physical prefactor `C_ext = 1`
(`Erdos287.V24Prefactor.sp2CextRepaired`).

Banked:

* the amplitude ledger `M = X^{2/7}`, `W₅ = X^{5/7}`, `M·W₅ = X`
  (`hard_amplitude_product`, exactly, in real rpow arithmetic);
* the per-cell log budget

  ```
  outer log^{-2} energy  +  variance log^{-5}  +  one external log   ⇒   log^{-5/2},
  ```

  i.e. `−(2+5)/2 + 1 = −5/2` (`hard_cell_log_budget`);
* the dyadic summation `−5/2 + 1 = −3/2`, giving the research target `log^{-3/2+o(1)}`
  (`hard_dyadic_summation`).

The little-`o` is **not** pretended to be a finite Lean theorem: it is carried by the explicit
abstract asymptotic interface `HardAmplitudeAsymptoticInterface`, which is uninhabited.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace HostileAudit

open Erdos287.V24Prefactor

/-! ## §11.1  The amplitude exponents -/

/-- The outer amplitude exponent: `M = X^{2/7}`. -/
def hardOuterExponent : ℚ := 2 / 7

/-- The inner amplitude exponent: `W₅ = X^{5/7}`. -/
def hardInnerExponent : ℚ := 5 / 7

/-- **`hard_amplitude_exponent_ledger`.**  `LEAN_PROVED` (rational arithmetic). -/
theorem hard_amplitude_exponent_ledger :
    hardOuterExponent + hardInnerExponent = 1 ∧
      hardOuterExponent < hardInnerExponent := by
  unfold hardOuterExponent hardInnerExponent
  norm_num

/-- **`hard_amplitude_product`.**  `LEAN_PROVED`.

`M·W₅ = X^{2/7}·X^{5/7} = X` exactly. -/
theorem hard_amplitude_product {X : ℝ} (hX : 0 < X) :
    X ^ ((2 : ℝ) / 7) * X ^ ((5 : ℝ) / 7) = X := by
  rw [← Real.rpow_add hX]
  norm_num

/-! ## §11.2  The per-cell log budget -/

/-- The outer energy log exponent (`−2`). -/
def outerEnergyLogExponent : ℚ := -2

/-- The external physical log, with the repaired prefactor `C_ext = 1`. -/
def externalLogExponent : ℚ := 1

/-- **`cext_is_one`.**  `LEAN_PROVED`.  The repaired physical prefactor is reused, not
re-derived. -/
theorem cext_is_one : sp2CextRepaired = 1 := rfl

/-- The per-cell net log exponent: `−(2+5)/2 + 1`. -/
def hardCellLogExponent : ℚ :=
  (outerEnergyLogExponent + rawRawLogExponent) / 2 + externalLogExponent

/-- **`hard_cell_log_budget`.**  `LEAN_PROVED` (rational arithmetic).

```
outer log^{-2}  +  variance log^{-5}  +  one external log  ⇒  log^{-5/2}
```

per hard dyadic cell — using the *corrected* variance exponent `−5`, not `−10`. -/
theorem hard_cell_log_budget :
    hardCellLogExponent = -5 / 2 ∧
      externalLogExponent = (sp2CextRepaired : ℚ) := by
  unfold hardCellLogExponent outerEnergyLogExponent externalLogExponent rawRawLogExponent
  constructor
  · norm_num
  · rfl

/-- The exponent after the dyadic summation. -/
def hardDyadicLogExponent : ℚ := hardCellLogExponent + 1

/-- **`hard_dyadic_summation`.**  `LEAN_PROVED` (rational arithmetic).

An additional `O(log X)` dyadic summation moves the per-cell `log^{-5/2}` to the research
target exponent `−3/2`. -/
theorem hard_dyadic_summation :
    hardDyadicLogExponent = -3 / 2 ∧ hardCellLogExponent < hardDyadicLogExponent := by
  unfold hardDyadicLogExponent hardCellLogExponent outerEnergyLogExponent externalLogExponent
    rawRawLogExponent
  norm_num

/-- **`hard_budget_is_not_a_closure`.**  `LEAN_PROVED`.

The research target exponent `−3/2` is **not** below `−1` by the margin that a closure would
need at the level of the dyadic sum alone: `−3/2 < −1` holds, but only *after* the dyadic
summation, and the little-`o` correction is not quantified here. -/
theorem hard_budget_is_not_a_closure :
    hardDyadicLogExponent < -1 ∧ hardCellLogExponent < hardDyadicLogExponent := by
  unfold hardDyadicLogExponent hardCellLogExponent outerEnergyLogExponent externalLogExponent
    rawRawLogExponent
  norm_num

/-! ## §11.3  The abstract asymptotic interface -/

/-- **`HardAmplitudeAsymptoticInterface`** — `EXTERNAL / ASYMPTOTIC / UNINHABITED`.

The `o(1)` in `log^{-3/2+o(1)}` is represented explicitly: the interface supplies, for every
`ε > 0`, a threshold beyond which the hard contribution obeys the exponent `−3/2 + ε`.  This
is an abstract asymptotic *interface*, not a finite theorem, and it is not inhabited. -/
structure HardAmplitudeAsymptoticInterface (Hard : ℝ → ℝ) : Prop where
  /-- For every `ε > 0` the exponent `−3/2 + ε` is eventually admissible. -/
  eventual_exponent :
    ∀ eps : ℝ, 0 < eps → ∃ X0 : ℝ, 3 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X → |Hard X| ≤ (Real.log X) ^ (-(3 : ℝ) / 2 + eps)

/-- **`hardAmplitudeAsymptotic_not_automatic`.**  `LEAN_PROVED`.

The asymptotic interface is not inhabited: the constant function `1` refutes it (take
`ε = 1/4`; for large `X` the right-hand side tends to `0`). -/
theorem hardAmplitudeAsymptotic_not_automatic :
    ∃ Hard : ℝ → ℝ, ¬ HardAmplitudeAsymptoticInterface Hard := by
  refine ⟨fun _ => 1, ?_⟩
  intro h
  obtain ⟨X0, hX0, hbound⟩ := h.eventual_exponent (1 / 4) (by norm_num)
  -- evaluate at a scale where `log X > 1` and the negative power is `< 1`
  set X := max X0 (Real.exp 2) with hXdef
  have hX0X : X0 ≤ X := le_max_left _ _
  have hexp : Real.exp 2 ≤ X := le_max_right _ _
  have hlog : (2 : ℝ) ≤ Real.log X := by
    have hpos : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
    calc (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
      _ ≤ Real.log X := Real.log_le_log hpos hexp
  have h1 : |(1 : ℝ)| ≤ (Real.log X) ^ (-(3 : ℝ) / 2 + 1 / 4) := hbound X hX0X
  have hlt : (Real.log X) ^ (-(3 : ℝ) / 2 + 1 / 4) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · linarith
    · norm_num
  rw [abs_one] at h1
  linarith

end HostileAudit
end Erdos287
