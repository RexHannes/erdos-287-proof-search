import Mathlib
import RequestProject.Erdos287.HighProjectorCutoff3221
import RequestProject.CurrentProgramme.Erdos287FixedBudgetV22Arithmetic

/-!
# Fixed-`D` cutoff repair (`D = log X`, `B0 = 1`)

The banked interface `Erdos287.HighCondCutoff.HighProjectorCutoffCompat3221` is **preserved
unchanged**.  It demands, among other things, *all-`D` cutoff invariance*

```
    ∀ D', unaccounted D' = unaccounted Dana,
```

which is stronger than what the source actually supplies at the single physical cutoff.

This file adds the source-exact **fixed-cutoff** interface at

```
    B0 = 1,     D = log X,
```

which asks only for the vanishing statements *at the physical cutoff itself*.  Adapters are
proved in the direction that is logically valid (`strong ⇒ fixed`); the converse is refuted
(`fixedD_does_not_give_all_D_invariance`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace FixedDCutoff

open Erdos287.V21Cutoff
open Erdos287.V20Compiler

/-! ## §1.  `D = log X` at `B0 = 1` -/

/-- At `B0 = 1` the shared cutoff is literally `log X`. -/
theorem sharedCutoff_one (X : ℝ) : sharedCutoff 1 X = Real.log X := by
  rw [sharedCutoff, highConductorCutoff]
  norm_num

/-! ## §2.  The fixed-cutoff interface -/

/-- **`FixedDCutoffCompat3221`** — the source-exact cutoff interface at `B0 = 1`.

Both sides use the *same* cutoff `D = log X`, and the unaccounted exceptional/principal
piece and the low-conductor residual vanish **at that cutoff**.  No invariance under moving
the cutoff is required. -/
structure FixedDCutoffCompat3221 (X : ℝ) (Dana Dphys : ℝ)
    (unaccounted lowResidual : ℝ → ℝ) : Prop where
  /-- The analytic side uses `D = log X`. -/
  ana_cutoff : Dana = Real.log X
  /-- The physical comparison side uses the same cutoff. -/
  phys_cutoff : Dphys = Real.log X
  /-- The unaccounted piece vanishes **at** the physical cutoff. -/
  unaccounted_vanishes : unaccounted Dana = 0
  /-- The low-conductor reassembly is valid **at** the physical cutoff. -/
  lowCond_reassembly : lowResidual Dana = 0

/-- The two cutoffs of the fixed interface agree. -/
theorem fixedD_cutoffs_match {X Dana Dphys : ℝ} {unaccounted lowResidual : ℝ → ℝ}
    (h : FixedDCutoffCompat3221 X Dana Dphys unaccounted lowResidual) : Dana = Dphys := by
  rw [h.ana_cutoff, h.phys_cutoff]

/-! ## §3.  Adapters -/

/-- **`fixedD_of_strong`.**  `KERNEL-PROVED`.

The banked stronger interface at `B0 = 1` implies the fixed-cutoff interface.  This is the
only adapter direction that is logically valid. -/
theorem fixedD_of_strong {X Dana Dphys : ℝ} {unaccounted lowResidual : ℝ → ℝ}
    (h : HighProjectorCutoffCompat3221 X 1 Dana Dphys unaccounted lowResidual) :
    FixedDCutoffCompat3221 X Dana Dphys unaccounted lowResidual where
  ana_cutoff := by rw [h.ana_cutoff, sharedCutoff_one]
  phys_cutoff := by rw [h.phys_cutoff, sharedCutoff_one]
  unaccounted_vanishes := h.unaccounted_vanishes
  lowCond_reassembly := h.lowCond_reassembly

/-- **`fixedD_does_not_give_all_D_invariance`.**  `KERNEL-PROVED`.

The converse adapter is false: the fixed-cutoff interface can hold while the all-`D`
invariance demanded by the stronger interface fails.  So the repair is a genuine weakening
and the stronger interface is not silently reinstated. -/
theorem fixedD_does_not_give_all_D_invariance :
    ∃ (X Dana Dphys : ℝ) (unaccounted lowResidual : ℝ → ℝ),
      FixedDCutoffCompat3221 X Dana Dphys unaccounted lowResidual ∧
        ¬ (∀ D' : ℝ, unaccounted D' = unaccounted Dana) := by
  classical
  refine ⟨2, Real.log 2, Real.log 2,
    fun D => if D = Real.log 2 then 0 else 1, fun _ => 0,
    ⟨rfl, rfl, by simp, rfl⟩, ?_⟩
  intro hall
  have h := hall (Real.log 2 + 1)
  have hne : Real.log 2 + 1 ≠ Real.log 2 := by intro hcon; linarith
  simp [hne] at h

/-- **`fixedD_not_automatic`.**  `KERNEL-PROVED`.  The fixed interface is still a genuine
source obligation: explicit data refute it. -/
theorem fixedD_not_automatic :
    ∃ (X Dana Dphys : ℝ) (unaccounted lowResidual : ℝ → ℝ),
      ¬ FixedDCutoffCompat3221 X Dana Dphys unaccounted lowResidual := by
  refine ⟨2, Real.log 2, Real.log 2, fun _ => 1, fun _ => 0, ?_⟩
  intro h
  exact one_ne_zero h.unaccounted_vanishes

end FixedDCutoff
end Erdos287
