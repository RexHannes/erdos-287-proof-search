import Mathlib
import RequestProject.CurrentProgramme.ImprimitiveConductorBookkeeping

/-!
# CurrentProgramme §9 — the SmallR owner-subtraction repair

`AFFINE287-SP2-SMALLR-OWNER-SUBTRACTION45` — `LEAN_PROVED ALGEBRAIC / FINITE COMPILER`.

Objects:

```
    S_sr        := the physical SmallR contribution (the literal sector sum),
    M_sr_prin   := the SmallR principal Euler packet (supplied),
    D_sr        := S_sr − M_sr_prin.
```

Banked (algebra, load-bearing):

* `smallR_owner_subtraction` : `S_sr = D_sr + M_sr_prin`, with **no** hypothesis;
* `smallR_defect_bound` : conditionally, `|S_sr| ≤ E₁` and `|M_sr_prin| ≤ E₂` give
  `|D_sr| ≤ E₁ + E₂`;
* the owner convention: the SmallR *principal* part is owned by the Euler principal owner,
  the SmallR *defect* by the direct SmallR owner.

The analytic bounds `E₁`, `E₂` themselves are **not** proved; they enter through the
uninhabited socket `SmallRDefectAnalyticInput`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace CurrentProgramme

/-! ## §9.1  The three objects -/

/-- `S_sr` : the literal physical SmallR contribution at cutoff `u` and modulus `N`. -/
noncomputable def sSmallR (u N : ℕ) (coeff : ℕ × ℕ → ℝ) : ℝ :=
  V24Adapters.sigmaSmallR u N coeff

/-- `D_sr` : the SmallR defect relative to a supplied principal Euler packet `M_sr_prin`. -/
noncomputable def dSmallR (u N : ℕ) (coeff : ℕ × ℕ → ℝ) (mPrin : ℝ) : ℝ :=
  sSmallR u N coeff - mPrin

/-! ## §9.2  The load-bearing algebra -/

/-- **`smallR_owner_subtraction`.**  `LEAN_PROVED`.

`S_sr = D_sr + M_sr_prin`, unconditionally.  This is the reassembly identity on which the
owner convention rests. -/
theorem smallR_owner_subtraction (u N : ℕ) (coeff : ℕ × ℕ → ℝ) (mPrin : ℝ) :
    sSmallR u N coeff = dSmallR u N coeff mPrin + mPrin := by
  unfold dSmallR
  ring

/-- **`smallR_defect_unique`.**  `LEAN_PROVED`.

Given the principal packet, the defect is the *unique* quantity reassembling the physical
SmallR contribution: there is no freedom to spend the same mass twice. -/
theorem smallR_defect_unique (u N : ℕ) (coeff : ℕ × ℕ → ℝ) (mPrin d : ℝ)
    (h : sSmallR u N coeff = d + mPrin) : d = dSmallR u N coeff mPrin := by
  unfold dSmallR
  linarith

/-- **`smallR_defect_bound`.**  `LEAN_PROVED` (conditional on the two supplied estimates).

`|S_sr| ≤ E₁` and `|M_sr_prin| ≤ E₂` imply `|D_sr| ≤ E₁ + E₂`. -/
theorem smallR_defect_bound {u N : ℕ} {coeff : ℕ × ℕ → ℝ} {mPrin e1 e2 : ℝ}
    (h1 : |sSmallR u N coeff| ≤ e1) (h2 : |mPrin| ≤ e2) :
    |dSmallR u N coeff mPrin| ≤ e1 + e2 := by
  unfold dSmallR
  exact le_trans (abs_sub _ _) (add_le_add h1 h2)

/-- **`smallR_reassembly_from_defect`.**  `LEAN_PROVED`.

Conversely, bounds on the defect and the principal packet bound the physical contribution:
the compiler is symmetric, so nothing is lost in the subtraction. -/
theorem smallR_reassembly_from_defect {u N : ℕ} {coeff : ℕ × ℕ → ℝ} {mPrin d1 e2 : ℝ}
    (h1 : |dSmallR u N coeff mPrin| ≤ d1) (h2 : |mPrin| ≤ e2) :
    |sSmallR u N coeff| ≤ d1 + e2 := by
  have h := smallR_owner_subtraction u N coeff mPrin
  rw [h]
  exact le_trans (abs_add_le _ _) (add_le_add h1 h2)

/-! ## §9.3  The analytic socket -/

/-- **`SmallRDefectAnalyticInput`** — `EXTERNAL / ANALYTIC / UNINHABITED`.

The analytic estimates the owner subtraction consumes: a bound `E₁` on the physical SmallR
contribution and a bound `E₂` on the SmallR principal Euler packet, both at scale `X` with a
genuine saving. -/
structure SmallRDefectAnalyticInput
    (u N : ℕ) (coeff : ℕ × ℕ → ℝ) (mPrin e1 e2 X eps : ℝ) : Prop where
  /-- The scale is nontrivial and the declared saving is genuine. -/
  scale : 3 ≤ X ∧ 0 < eps
  /-- The physical SmallR bound. -/
  physical_bound : |sSmallR u N coeff| ≤ e1
  /-- The SmallR principal Euler packet bound. -/
  principal_bound : |mPrin| ≤ e2
  /-- Both bounds are inside the declared budget. -/
  budget : e1 + e2 ≤ eps * X / Real.log X

/-- **`smallR_defect_of_analytic_input`** — `CONDITIONAL`. -/
theorem smallR_defect_of_analytic_input
    {u N : ℕ} {coeff : ℕ × ℕ → ℝ} {mPrin e1 e2 X eps : ℝ}
    (h : SmallRDefectAnalyticInput u N coeff mPrin e1 e2 X eps) :
    |dSmallR u N coeff mPrin| ≤ eps * X / Real.log X :=
  le_trans (smallR_defect_bound h.physical_bound h.principal_bound) h.budget

/-- **`smallRDefectAnalytic_not_automatic`.**  `LEAN_PROVED`.

The analytic socket is a genuine restriction and is not inhabited: the algebraic compiler
above is *not* an analytic bound. -/
theorem smallRDefectAnalytic_not_automatic :
    ∃ (u N : ℕ) (coeff : ℕ × ℕ → ℝ) (mPrin e1 e2 X eps : ℝ),
      ¬ SmallRDefectAnalyticInput u N coeff mPrin e1 e2 X eps := by
  refine ⟨1, 1, fun _ => 0, 1, 0, 0, 3, 1, ?_⟩
  intro h
  have h2 : |(1 : ℝ)| ≤ 0 := h.principal_bound
  rw [abs_one] at h2
  linarith

end CurrentProgramme
end Erdos287
