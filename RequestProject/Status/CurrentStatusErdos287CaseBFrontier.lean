import Mathlib
import RequestProject.Status.CurrentStatusErdos287PrimitiveFractionCaseB
import RequestProject.CurrentProgramme.CaseBPrimitiveFractionReproof

/-!
# Append-only status layer — CASE-B reproof bank and the frontier firewall

This module is **append-only**: the CASE-B primitive-fraction ledger
(`CurrentStatusErdos287PrimitiveFractionCaseB`) and everything it imports are re-checked, not
edited.

Two things are certified here.

## §1  The reproof rows

The four additional exact statements of the reproof bank are backed by literal kernel-checked
theorems (`spacingPairForm`, `pipelineQH`, `comparabilityFirewall`, `criticalExponent`), each
recorded below by restating it in full.

## §2  The frontier firewall

The residual of the primitive-fraction audit,

```
287-K0-SP2-DET1-SHAREDGCD-ONELEVEL-PRIMITIVEFRACTION-CRITICAL45,
```

is *not* the frontier of the programme: a chain of strict descendants (squarefree projector
unfold, `k`–`m` fusion, coprime-pair projector, diagonal annihilation, fixed-`Δ` rigidity,
affine phase exposure, affine-defect normal form) leads to the strictly later node

```
287-K0-SP2-DET1-FUSED-SMALL-AFFINEDEFECT-CRITICAL-DELTA-FRIABLE-CROSSRECIP45,
```

which is the current frontier.  The ledger below is a *bookkeeping* object: `stage` linearly
orders the chain, and the theorems record that the primitive-fraction critical node is a strict
ancestor of the frontier, that no node of the chain is marked `closed`, and that Erdős #287
remains `open_`.  Nothing here asserts any mathematical content about the descendant nodes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Filter

namespace Erdos287
namespace CaseBFrontierStatus

open Erdos287.CaseBReproof
open Erdos287.SharedGcdGram

/-! ## §1  The reproof rows are theorems -/

/-- **Row `spacingPairForm`.**  `LEAN_PROVED` (unconditional). -/
theorem spacingPairForm_row_is_a_theorem :
    ∀ {d M m1 m2 t1 t2 : ℕ}, 0 < d → 0 < M → 0 < m1 → 0 < m2 → m1 < 2 * M → m2 < 2 * M →
      Nat.Coprime t1 m1 → Nat.Coprime t2 m2 → t1 < d * m1 → t2 < d * m2 →
      (m1, t1) ≠ (m2, t2) → ∀ n : ℤ,
        (d : ℚ) / (4 * ((d * M : ℕ) : ℚ) ^ 2)
          ≤ |(t1 : ℚ) / ((d * m1 : ℕ) : ℚ) - (t2 : ℚ) / ((d * m2 : ℕ) : ℚ) - (n : ℚ)| :=
  fun hd hM hm1 hm2 h1 h2 hc1 hc2 hlt1 hlt2 hne n =>
    separation_of_distinct_pairs hd hM hm1 hm2 h1 h2 hc1 hc2 hlt1 hlt2 hne n

/-- **Row `comparabilityFirewall`.**  `LEAN_PROVED`:  `AB ≍ X`, not `AB = X`. -/
theorem comparabilityFirewall_row_is_a_theorem :
    ∀ {Alen B Gfreq H X c0 L1 L0 : ℝ}, 0 < Alen → 0 < B → 0 < Gfreq → 0 < H → 0 < X → 0 < c0 →
      0 ≤ L0 → c0 * X ≤ Alen * B →
      (B * (1 + B / Gfreq) * (Alen * L1 + Gfreq ^ 2 / H * L0)) / (Alen * B ^ 2)
        ≤ L1 / B + L1 / Gfreq + L0 * Gfreq ^ 2 / (H * (c0 * X)) + L0 * Gfreq / (H * Alen) :=
  fun hA hB hG hH hX hc0 hL0 hcomp =>
    normalised_ratio_le_of_comparable hA hB hG hH hX hc0 hL0 hcomp

/-- **Row `criticalExponent`.**  `LEAN_PROVED`:  `κ ≤ max(2θ−1, θ−α) + K loglog X / log X`. -/
theorem criticalExponent_row_is_a_theorem :
    ∀ {theta alpha kappa X : ℝ} (K : ℕ), 1 < X →
      X ^ kappa ≤ (Real.log X) ^ K * max (X ^ (2 * theta - 1)) (X ^ (theta - alpha)) →
      kappa ≤ max (2 * theta - 1) (theta - alpha)
        + (K : ℝ) * Real.log (Real.log X) / Real.log X :=
  fun K hX h => kappa_le_of_critical_range K hX h

/-! ## §2  The frontier ledger -/

/-- The strict-descendant chain below the primitive-fraction critical node. -/
inductive FrontierNode
  | primitiveFractionCritical45
  | squarefreeProjectorUnfold
  | kmFusion
  | coprimePairProjector
  | diagonalAnnihilation
  | fixedDeltaRigidity
  | affinePhaseExposure
  | affineDefectNormalForm
  | fusedAffineDefectCritical45
  | erdos287
  deriving DecidableEq, Fintype, Repr

/-- Status labels for the frontier ledger. -/
inductive FrontierLabel
  | closed
  | passedThrough
  | currentFrontier
  | open_
  deriving DecidableEq, Fintype, Repr

open FrontierNode FrontierLabel

/-- Linear position of each node along the reduction chain. -/
def stage : FrontierNode → ℕ
  | primitiveFractionCritical45 => 0
  | squarefreeProjectorUnfold => 1
  | kmFusion => 2
  | coprimePairProjector => 3
  | diagonalAnnihilation => 4
  | fixedDeltaRigidity => 5
  | affinePhaseExposure => 6
  | affineDefectNormalForm => 7
  | fusedAffineDefectCritical45 => 8
  | erdos287 => 9

/-- The frontier ledger.  `passedThrough` means: a strictly later reduction exists, so this node
is no longer the live residual — it does **not** mean the node is closed. -/
def frontierLedger : FrontierNode → FrontierLabel
  | primitiveFractionCritical45 => passedThrough
  | squarefreeProjectorUnfold => passedThrough
  | kmFusion => passedThrough
  | coprimePairProjector => passedThrough
  | diagonalAnnihilation => passedThrough
  | fixedDeltaRigidity => passedThrough
  | affinePhaseExposure => passedThrough
  | affineDefectNormalForm => passedThrough
  | fusedAffineDefectCritical45 => currentFrontier
  | erdos287 => open_

/-- **No node of the chain is closed.**  `LEAN_PROVED`. -/
theorem frontier_no_closed_rows : ∀ n : FrontierNode, frontierLedger n ≠ closed := by
  decide +kernel

/-- **The frontier is unique.**  `LEAN_PROVED`. -/
theorem frontier_unique :
    ∀ n : FrontierNode, frontierLedger n = currentFrontier ↔ n = fusedAffineDefectCritical45 := by
  decide +kernel

/-- **The primitive-fraction critical node is a strict ancestor of the frontier.**
`LEAN_PROVED`. -/
theorem primitiveFractionCritical_strictly_before_frontier :
    stage primitiveFractionCritical45 < stage fusedAffineDefectCritical45 := by
  decide +kernel

/-- **The primitive-fraction critical node is not the frontier.**  `LEAN_PROVED`. -/
theorem primitiveFractionCritical_not_frontier :
    frontierLedger primitiveFractionCritical45 ≠ currentFrontier := by
  decide +kernel

/-- **Every intermediate reduction is strictly between the two critical nodes.**
`LEAN_PROVED`. -/
theorem chain_is_strictly_increasing :
    ∀ m n : FrontierNode, frontierLedger m = passedThrough →
      frontierLedger n = currentFrontier → stage m < stage n := by
  decide +kernel

/-- **Erdős #287 is still open in this ledger.**  `LEAN_PROVED`. -/
theorem frontier_erdos287_open : frontierLedger erdos287 = open_ := by decide +kernel

/-- **The earlier CASE-B ledger is preserved verbatim.**  `LEAN_PROVED`.  The primitive-fraction
audit still reports `hCriticalOpen` at its residual and `open_` at Erdős #287; this delta only
adds the information that a strictly later child exists. -/
theorem caseB_ledger_preserved :
    Erdos287.PrimitiveFractionCaseBStatus.ledger
        Erdos287.PrimitiveFractionCaseBStatus.Node.primitiveFractionCritical45
      = Erdos287.PrimitiveFractionCaseBStatus.Label.hCriticalOpen ∧
    Erdos287.PrimitiveFractionCaseBStatus.ledger
        Erdos287.PrimitiveFractionCaseBStatus.Node.erdos287
      = Erdos287.PrimitiveFractionCaseBStatus.Label.open_ := by
  decide +kernel

end CaseBFrontierStatus
end Erdos287
