import Mathlib
import RequestProject.CurrentProgramme.OwnerMap

/-!
# CurrentProgramme §13 — the post-audit full-`q` compiler

`SP2-BALANCED7-FULL-Q45` — `conditionalCompiler / OPEN`.

`BalancedSevenPostAuditInputs` bundles **every** antecedent explicitly: the literal SP-2
source reassembly, the SmallQ `3+4` large-sieve source input, the SmallR defect analytic
input, the hard physical-range analytic input, the full Euler principal input, the hard
dyadic partition-of-unity input, the unique-owner proof and both signs.  The compiler

```
    BalancedSevenPostAuditInputs → BalancedSevenAsymptoticConclusion
```

is purely logical: the conclusion is obtained from the per-cell savings by the exact
reassembly of §12.  The antecedent bundle is **not** constructed, and no status row is
closed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace CurrentProgramme

open Balanced7Cell Balanced7Owner

/-! ## §13.1  The conclusion -/

/-- The Balanced7 asymptotic conclusion for a physical sum `S`: `S(X) = o(X / log X)`. -/
def BalancedSevenAsymptoticConclusion (S : ℝ → ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → |S X| ≤ eps * X / Real.log X

/-! ## §13.2  The antecedent bundle -/

/-- **`BalancedSevenPostAuditInputs`** — the full antecedent bundle.  `UNINHABITED`.

`S` is the physical two-sign sum, `cellVal` its cell decomposition.  The four `Prop`
parameters are the external children: the literal SP-2 source, the full Euler principal
input, the hard dyadic partition of unity, and the two-sign reassembly. -/
structure BalancedSevenPostAuditInputs
    (S : ℝ → ℝ) (cellVal : Balanced7Cell → ℝ → ℝ)
    (sp2LiteralSource eulerPrincipalInput hardDyadicPartition bothSigns : Prop) : Prop where
  /-- The literal SP-2 physical source is supplied. -/
  sp2_source : sp2LiteralSource
  /-- The full Euler principal input is supplied. -/
  euler_principal : eulerPrincipalInput
  /-- The hard dyadic partition-of-unity input is supplied. -/
  hard_partition : hardDyadicPartition
  /-- Both signs are reassembled. -/
  two_signs : bothSigns
  /-- Exact reassembly of the physical sum from the **owners' accounts** — the unique-owner
  convention of §12, so no cell is spent twice. -/
  owner_reassembly : ∀ X : ℝ, S X = ∑ o : Balanced7Owner, ownerAccount (fun c => cellVal c X) o
  /-- Each cell is supplied by its owner with an `o(X / log X)` saving:
  SmallQ defect by `SmallQ34LS`, SmallR defect by `SmallRDirect`, hard defect by `Hard3221`,
  the three principal cells by `EulerPrincipal`, and the even/nonunit cell is zero-routed. -/
  cell_savings : ∀ c : Balanced7Cell, ∀ eps : ℝ, 0 < eps →
    ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → |cellVal c X| ≤ eps * X / Real.log X

/-! ## §13.3  The compiler -/

/-- **`balancedSeven_postAudit_compiler`.**  `LEAN_PROVED` (purely logical implication).

The full antecedent bundle implies the Balanced7 asymptotic conclusion. -/
theorem balancedSeven_postAudit_compiler
    {S : ℝ → ℝ} {cellVal : Balanced7Cell → ℝ → ℝ}
    {sp2LiteralSource eulerPrincipalInput hardDyadicPartition bothSigns : Prop}
    (h : BalancedSevenPostAuditInputs S cellVal sp2LiteralSource eulerPrincipalInput
      hardDyadicPartition bothSigns) :
    BalancedSevenAsymptoticConclusion S := by
  intro eps heps
  have hseven : (0 : ℝ) < 7 := by norm_num
  choose X0 hX0 using fun c : Balanced7Cell => h.cell_savings c (eps / 7) (by positivity)
  refine ⟨Finset.univ.sup' ⟨smallQPrincipal, Finset.mem_univ _⟩ X0, ?_⟩
  intro X hX
  have hXc : ∀ c : Balanced7Cell, X0 c ≤ X := by
    intro c
    exact le_trans (Finset.le_sup' X0 (Finset.mem_univ c)) hX
  calc |S X| = |∑ c : Balanced7Cell, cellVal c X| := by
        rw [h.owner_reassembly X, no_double_spending]
    _ ≤ ∑ c : Balanced7Cell, |cellVal c X| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c : Balanced7Cell, eps / 7 * X / Real.log X :=
        Finset.sum_le_sum fun c _ => hX0 c X (hXc c)
    _ = eps * X / Real.log X := by
        rw [Finset.sum_const, Finset.card_univ]
        have : (Fintype.card Balanced7Cell : ℝ) = 7 := by
          norm_num [show Fintype.card Balanced7Cell = 7 from by decide +kernel]
        rw [nsmul_eq_mul, this]
        ring

/-- **`postAuditInputs_not_inhabited_here`.**  `LEAN_PROVED`.

The bundle is a genuine restriction: explicit data refute it.  It is not constructed
anywhere in this repository, so no Balanced7 conclusion is banked. -/
theorem postAuditInputs_not_inhabited_here :
    ∃ (S : ℝ → ℝ) (cellVal : Balanced7Cell → ℝ → ℝ)
      (sp2LiteralSource eulerPrincipalInput hardDyadicPartition bothSigns : Prop),
      ¬ BalancedSevenPostAuditInputs S cellVal sp2LiteralSource eulerPrincipalInput
        hardDyadicPartition bothSigns := by
  refine ⟨fun _ => 0, fun _ _ => 0, False, True, True, True, ?_⟩
  intro h
  exact h.sp2_source

/-- **`postAudit_compiler_does_not_prove_balancedSeven`.**  `LEAN_PROVED`.

The compiler is conditional only: its antecedent is not available, so no unconditional
Balanced7 statement follows from this module. -/
theorem postAudit_compiler_does_not_prove_balancedSeven :
    (∃ (S : ℝ → ℝ) (cellVal : Balanced7Cell → ℝ → ℝ)
      (a b c d : Prop), ¬ BalancedSevenPostAuditInputs S cellVal a b c d) ∧
      ∀ (S : ℝ → ℝ) (cellVal : Balanced7Cell → ℝ → ℝ) (a b c d : Prop),
        BalancedSevenPostAuditInputs S cellVal a b c d → BalancedSevenAsymptoticConclusion S :=
  ⟨postAuditInputs_not_inhabited_here, fun _ _ _ _ _ _ h => balancedSeven_postAudit_compiler h⟩

end CurrentProgramme
end Erdos287
