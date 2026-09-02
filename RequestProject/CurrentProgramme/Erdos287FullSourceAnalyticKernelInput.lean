import Mathlib
import RequestProject.CurrentProgramme.Erdos287K0SP2FourClassPartition

/-!
# The external / paper analytic input of the full source-local analytic kernel

`FULL-SOURCE-LOCAL-ANALYTIC-KERNEL45 : ANALYTIC BANKED (paper / external input)`

This module is **append-only**.

It defines *one* typed structure,
`FullSourceLocalAnalyticKernelInput`, whose fields are exactly the analytic
conclusions that the paper/research run reports and that the downstream finite
compiler consumes:

```
closed-sector Perron-L¹ bound;
full smooth parent bound;
regular parent bound;
low-Q owner estimate;
generated Pascadi triple-cell estimate;
C0 fixed-packet estimate;
transverse fixed-packet estimate;
b-diagonal fixed-packet estimate;
global owner-reassembly identity.
```

All quantitative conclusions are **explicit**: every bound is a literal
inequality against the explicit budget `X / (log X)²` with an explicit numeral
constant.

**Firewall.**  The structure is *not inhabited at the physical values*: no
theorem of this repository produces an inhabitant for the physical owner values
of the K0-SP2 source.  It is neither an `axiom` nor a `sorry`; it is a
hypothesis that every downstream theorem carries explicitly.  §3 records the
counterguards: the structure is a genuine constraint (explicit values refute
it), and it is **not** a consequence of the kernel-proved finite/source
combinatorics — the four-class partition holds for *every* parameter package
while the analytic input still fails.

Nothing here proves, or claims, any analytic estimate, and nothing here bears on
the status of Erdős #287, which remains `open_`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace FullAnalyticKernel

/-! ## §1  The physical owner values and the explicit budget -/

/-- **`OwnerValues`** — the nine real quantities produced by the source compiler:
the eight owner/sector values and the physical full correlation. -/
structure OwnerValues where
  /-- The closed-sector Perron-L¹ value. -/
  closedSectorPerronL1 : ℝ
  /-- The full smooth parent value. -/
  fullSmoothParent : ℝ
  /-- The de-regularised (regular) parent value. -/
  regularParent : ℝ
  /-- The low-`Q` owner value. -/
  lowQOwner : ℝ
  /-- The generated Pascadi triple-cell value. -/
  pascadiTripleCell : ℝ
  /-- The `C0` fixed-packet value. -/
  c0FixedPacket : ℝ
  /-- The transverse fixed-packet value. -/
  transverseFixedPacket : ℝ
  /-- The b-diagonal fixed-packet value. -/
  bDiagonalFixedPacket : ℝ
  /-- The physical full correlation consumed by FCL. -/
  fullCorrelation : ℝ

/-- The explicit analytic budget `X / (log X)²`. -/
noncomputable def budget (X : ℝ) : ℝ := X / (Real.log X) ^ 2

/-- At scales `X ≥ e` the budget is nonnegative. -/
theorem budget_nonneg {X : ℝ} (hX : Real.exp 1 ≤ X) : 0 ≤ budget X := by
  have h1 : (0:ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  exact div_nonneg h1.le (sq_nonneg _)

/-! ## §2  The typed external analytic input -/

/-- **`FullSourceLocalAnalyticKernelInput`** — `EXTERNAL / PAPER-BANKED,
UNINHABITED AT THE PHYSICAL VALUES`.

Exactly the analytic conclusions of the paper/research run, with explicit
numerical constants against the budget `X/(log X)²`, together with the global
owner-reassembly identity.  **No inhabitant for the physical owner values is
constructed anywhere in this repository.** -/
structure FullSourceLocalAnalyticKernelInput (X : ℝ) (v : OwnerValues) : Prop where
  /-- The scale is at least `e`, so `log X ≥ 1`. -/
  scale : Real.exp 1 ≤ X
  /-- Closed-sector Perron-L¹ bound. -/
  closedSectorPerronL1_bound : |v.closedSectorPerronL1| ≤ 3 * budget X
  /-- Full smooth parent bound. -/
  fullSmoothParent_bound : |v.fullSmoothParent| ≤ 4 * budget X
  /-- Regular (de-regularised) parent bound. -/
  regularParent_bound : |v.regularParent| ≤ 4 * budget X
  /-- Low-`Q` owner estimate. -/
  lowQOwner_bound : |v.lowQOwner| ≤ 2 * budget X
  /-- Generated Pascadi triple-cell estimate. -/
  pascadiTripleCell_bound : |v.pascadiTripleCell| ≤ 2 * budget X
  /-- `C0` fixed-packet estimate. -/
  c0FixedPacket_bound : |v.c0FixedPacket| ≤ 3 * budget X
  /-- Transverse fixed-packet estimate. -/
  transverseFixedPacket_bound : |v.transverseFixedPacket| ≤ 3 * budget X
  /-- b-diagonal fixed-packet estimate. -/
  bDiagonalFixedPacket_bound : |v.bDiagonalFixedPacket| ≤ 3 * budget X
  /-- Global owner-reassembly: the physical full correlation is the sum of the five
  owner values and the regular parent. -/
  globalOwnerReassembly :
    v.fullCorrelation =
      v.lowQOwner + v.pascadiTripleCell + v.c0FixedPacket + v.transverseFixedPacket
        + v.bDiagonalFixedPacket + v.regularParent

/-! ## §3  Counterguards -/

/-- The trivial (all-zero) owner values do satisfy the constraints at any scale `X ≥ e`:
the structure is not vacuous.  This is a *statement about the zero data only*; it says
nothing about the physical values. -/
theorem zeroValues_input {X : ℝ} (hX : Real.exp 1 ≤ X) :
    FullSourceLocalAnalyticKernelInput X ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := by
  have hb : 0 ≤ budget X := budget_nonneg hX
  refine ⟨hX, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by norm_num⟩ <;>
    · simp only [abs_zero]
      linarith

/-- **`analyticInput_is_a_genuine_constraint`.**  `KERNEL-PROVED`.

Explicit owner values at an explicit scale refute the analytic input: it is a real
obligation, not a definitional truism. -/
theorem analyticInput_is_a_genuine_constraint :
    ∃ (X : ℝ) (v : OwnerValues), ¬ FullSourceLocalAnalyticKernelInput X v := by
  refine ⟨Real.exp 1, ⟨100, 0, 0, 0, 0, 0, 0, 0, 0⟩, ?_⟩
  intro h
  have hb : budget (Real.exp 1) = Real.exp 1 := by
    simp [budget, Real.log_exp]
  have hlt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have := h.closedSectorPerronL1_bound
  rw [hb] at this
  have h100 : |(100:ℝ)| = 100 := by norm_num
  rw [h100] at this
  nlinarith

/-- **`analyticInput_not_from_source_combinatorics`.**  `KERNEL-PROVED`.

The kernel-proved finite/source combinatorics does **not** deliver the analytic input:
the exact four-class source partition holds for *every* parameter package and every
cutoff, while the analytic input still fails at explicit data. -/
theorem analyticInput_not_from_source_combinatorics
    (P : Erdos287.K0SP2Source.K0SP2Params) (L : ℕ) :
    (P.classRepeatedB7 ∪ P.classLargePP L ∪ P.classDistinctB7 L ∪ P.classRegular L
        = P.sourceSet) ∧
    ∃ (X : ℝ) (v : OwnerValues), ¬ FullSourceLocalAnalyticKernelInput X v :=
  ⟨P.fourClass_union L, analyticInput_is_a_genuine_constraint⟩

/-- **`analyticInput_not_inhabited_here`.**  `KERNEL-PROVED` (bookkeeping).

The repository contains no theorem of the form "for the physical owner values the
analytic input holds"; formally, the only inhabitants exhibited above are the trivial
zero data, and the constraint is refutable, so no blanket inhabitation is available. -/
theorem analyticInput_not_inhabited_here :
    ¬ ∀ (X : ℝ) (v : OwnerValues), FullSourceLocalAnalyticKernelInput X v := by
  intro h
  obtain ⟨X, v, hv⟩ := analyticInput_is_a_genuine_constraint
  exact hv (h X v)

end FullAnalyticKernel
end Erdos287
