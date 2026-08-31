import Mathlib
import RequestProject.CurrentProgramme.PostAuditFullQCompiler

/-!
# Append-only status module — Erdős #287 Balanced7 post-audit repair

This module is **append-only**: `CurrentStatus`-style historical ledgers (V20, V21, V22,
SP-2, V23, V24) are untouched, and no historical status row is deleted or rewritten.  The
historical research claim `BALANCED7 : CLOSED` remains visible in the historical reports; it
is **not controlling**, and this ledger records `BALANCED7 : open_`.

Rows recorded here, and the proofs that back them, all live in
`RequestProject/CurrentProgramme/`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace Balanced7RepairStatus

open Erdos287.CurrentProgramme

/-! ## §1  The ledger -/

/-- The status nodes of the Balanced7 repair pass. -/
inductive Node
  | balancedSevenEulerUniformity45
  | cExtLogRRepair45
  | qPacketStructuralPartition45
  | smallQTypeIAdapter45
  | smallQ34LSNormalization45
  | smallROwnerSubtraction45
  | hardThetaPhysicalDelta45
  | balancedSevenShortTSieve45
  | balancedSevenShiu45
  | imprimitiveConductorBookkeeping45
  | threePlusFourFiniteAlgebra45
  | allQNoDoubleSpending45
  | sp2BalancedSevenFullQ45
  | balancedSeven
  | effectivePolylogModulusReplacement45
  | k0UniformFragmentationReassembly45
  | fcl
  | erdos287
  deriving DecidableEq, Fintype, Repr

/-- The status labels.  The constructor `closed` exists so that "no closed rows" is a
statement about this ledger; it is never used. -/
inductive Label
  | closed
  | externallyAudited
  | provedAlgebraic
  | provedFinite
  | supersededAsControllingFrontier
  | sourceOpen
  | analyticOpen
  | conditionalCompiler
  | notActivated
  | open_
  deriving DecidableEq, Fintype, Repr

open Node Label

/-- The Balanced7 repair ledger. -/
def ledger : Node → Label
  | balancedSevenEulerUniformity45 => externallyAudited
  | cExtLogRRepair45 => provedAlgebraic
  | qPacketStructuralPartition45 => provedFinite
  | smallQTypeIAdapter45 => supersededAsControllingFrontier
  | smallQ34LSNormalization45 => sourceOpen
  | smallROwnerSubtraction45 => provedAlgebraic
  | hardThetaPhysicalDelta45 => provedAlgebraic
  | balancedSevenShortTSieve45 => analyticOpen
  | balancedSevenShiu45 => analyticOpen
  | imprimitiveConductorBookkeeping45 => sourceOpen
  | threePlusFourFiniteAlgebra45 => provedFinite
  | allQNoDoubleSpending45 => conditionalCompiler
  | sp2BalancedSevenFullQ45 => conditionalCompiler
  | balancedSeven => open_
  | effectivePolylogModulusReplacement45 => analyticOpen
  | k0UniformFragmentationReassembly45 => notActivated
  | fcl => open_
  | erdos287 => open_

/-- The exact residual order; `0` means "not on the residual list". -/
def residualRank : Node → ℕ
  | smallQ34LSNormalization45 => 1
  | imprimitiveConductorBookkeeping45 => 2
  | balancedSevenShortTSieve45 => 3
  | balancedSevenShiu45 => 4
  | sp2BalancedSevenFullQ45 => 5
  | _ => 0

/-! ## §2  Ledger integrity -/

/-- **`no_closed_rows`.**  `LEAN_PROVED`.  No row of this ledger is `closed`. -/
theorem no_closed_rows : ∀ n : Node, ledger n ≠ closed := by decide +kernel

/-- **`erdos287_open`.**  `LEAN_PROVED`. -/
theorem erdos287_open : ledger erdos287 = open_ ∧ open_ ≠ closed := by decide +kernel

/-- **`balanced7_open`.**  `LEAN_PROVED`.

Balanced7 is open; the historical research claim of closure is not controlling. -/
theorem balanced7_open :
    ledger balancedSeven = open_ ∧ ledger fcl = open_ ∧
      open_ ≠ closed ∧ open_ ≠ provedAlgebraic ∧ open_ ≠ conditionalCompiler := by
  decide +kernel

/-- **`first_residual_is_smallq_34LS_normalisation`.**  `LEAN_PROVED`. -/
theorem first_residual_is_smallq_34LS_normalisation :
    residualRank smallQ34LSNormalization45 = 1 ∧
      (∀ n : Node, residualRank n = 1 → n = smallQ34LSNormalization45) ∧
      ledger smallQ34LSNormalization45 = sourceOpen := by
  decide +kernel

/-- **`ledger_is_honest`.**  `LEAN_PROVED`.

Each label is backed by what the repository actually contains:

* the rows labelled `provedAlgebraic` / `provedFinite` are backed by kernel-checked theorems
  (the `C_ext` margin, the SmallR owner subtraction, the `δ = 1/21` ledger, the exact `q/r`
  partition and the finite `3+4` collision bound);
* the rows labelled `sourceOpen` / `analyticOpen` / `externallyAudited` are backed by
  interfaces that are *not* inhabited;
* `conditionalCompiler` rows are implications only. -/
theorem ledger_is_honest :
    -- proved rows really are theorems
    (cVarCurrent - 2 * cExtCurrent = 3) ∧
      (∀ (u N : ℕ) (coeff : ℕ × ℕ → ℝ) (mPrin : ℝ),
        sSmallR u N coeff = dSmallR u N coeff mPrin + mPrin) ∧
      hardLogScale = 1 / 420 ∧
      (∀ (contrib : Balanced7Cell → ℝ),
        ∑ o : Balanced7Owner, ownerAccount contrib o = ∑ c : Balanced7Cell, contrib c) ∧
      -- open rows really are uninhabited interfaces
      (∃ (S N qRange : Finset ℕ) (w3 : Fin 3 → ℕ → ℝ) (w4 : Fin 4 → ℕ → ℝ)
        (A3 B4 : ℕ → ℝ) (P s mult3 mult4 : ℕ) (E3 E4 Cqphi Clog X eps : ℝ)
        (cb ms swc lsc : Prop),
        ¬ BalancedSevenSmallQ34LSInput S N qRange w3 w4 A3 B4 P s mult3 mult4 E3 E4 Cqphi
          Clog X eps cb ms swc lsc) ∧
      (∃ X theta C R : ℝ, ¬ BalancedSevenShortTSieveInput X theta C R) ∧
      (∃ (Wprime s : ℕ) (Mbox : Finset ℕ) (Mlen : ℕ) (Cshiu : ℝ),
        ¬ BalancedSevenShiuInput Wprime s Mbox Mlen Cshiu) ∧
      (∃ (family : Finset ℕ) (J HP : ℕ → ℝ → ℝ) (S2 Hbound A : ℝ),
        ¬ BalancedSevenFullQEulerIdentityInput family J HP S2 Hbound A) ∧
      -- and the full-`q` compiler antecedent is not available
      (∃ (S : ℝ → ℝ) (cellVal : Balanced7Cell → ℝ → ℝ) (a b c d : Prop),
        ¬ BalancedSevenPostAuditInputs S cellVal a b c d) :=
  ⟨logR_signed_margin.1, smallR_owner_subtraction, hardLogScale_eq, no_double_spending,
   smallQ34LS_not_automatic, shortTSieve_not_automatic, shiu_not_automatic,
   fullQEulerIdentity_not_automatic, postAuditInputs_not_inhabited_here⟩

/-! ## §3  The effectivity firewall -/

/-- An *effective* Balanced7 statement: an explicit threshold `M0` beyond which the physical
sum obeys the `eps`-budget. -/
def EffectiveBalancedSeven (S : ℝ → ℝ) (M0 eps : ℝ) : Prop :=
  ∀ X : ℝ, M0 ≤ X → |S X| ≤ eps * X / Real.log X

/-- **`effectivity_firewall`.**  `LEAN_PROVED`.

There is no implication `asymptotic Balanced7 → computable M0`: for every claimed threshold
`M0` and budget `eps > 0` there is a function satisfying the asymptotic conclusion and
violating the effective statement at that threshold. -/
theorem effectivity_firewall (M0 eps : ℝ) (heps : 0 < eps) :
    ∃ S : ℝ → ℝ, BalancedSevenAsymptoticConclusion S ∧ ¬ EffectiveBalancedSeven S M0 eps := by
  set xs : ℝ := max M0 3 with hxs
  have hxs3 : (3 : ℝ) ≤ xs := le_max_right _ _
  have hxsM : M0 ≤ xs := le_max_left _ _
  have hlogxs : 0 < Real.log xs := Real.log_pos (by linarith)
  set C : ℝ := eps * xs / Real.log xs + 1 with hC
  refine ⟨fun X => if X ≤ xs then C else 0, ?_, ?_⟩
  · intro eps' heps'
    refine ⟨xs + 1, ?_⟩
    intro X hX
    have hnot : ¬ X ≤ xs := by linarith
    have hXpos : 0 < Real.log X := Real.log_pos (by linarith)
    simp only [hnot, if_false, abs_zero]
    exact div_nonneg (mul_nonneg heps'.le (by linarith)) hXpos.le
  · intro h
    have hle : |(if xs ≤ xs then C else 0)| ≤ eps * xs / Real.log xs := h xs hxsM
    have hCpos : 0 < C := by
      have : 0 ≤ eps * xs / Real.log xs :=
        div_nonneg (mul_nonneg heps.le (by linarith)) hlogxs.le
      linarith
    rw [if_pos le_rfl, abs_of_pos hCpos] at hle
    linarith

/-! ## §4  The downstream firewall -/

/-- **`downstream_not_activated`.**  `LEAN_PROVED`.

`287-K0-SP2-UNIFORM-FRAGMENTATION-REASSEMBLY45` is not activated and is not on the residual
list: the Balanced7 repair must survive a fresh hostile audit first. -/
theorem downstream_not_activated :
    ledger k0UniformFragmentationReassembly45 = notActivated ∧
      residualRank k0UniformFragmentationReassembly45 = 0 ∧
      notActivated ≠ closed ∧ notActivated ≠ provedAlgebraic := by
  decide +kernel

/-- **`euler_uniformity_is_externally_audited_only`.**  `LEAN_PROVED`. -/
theorem euler_uniformity_is_externally_audited_only :
    ledger balancedSevenEulerUniformity45 = externallyAudited ∧
      externallyAudited ≠ provedAlgebraic ∧ externallyAudited ≠ closed := by
  decide +kernel

end Balanced7RepairStatus
end Erdos287
