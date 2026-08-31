import Mathlib
import RequestProject.CurrentProgramme.UniformFragmentationCompiler

/-!
# Append-only status module — Erdős #287, post-Balanced7 "Pro" pass

This module is **append-only**.  No historical ledger is modified: the V15–V24 / SP-2 banks
and the pass-1 module `CurrentStatusErdos287Balanced7Repair` are untouched, and no historical
row is deleted or rewritten.

The latest research/paper closure candidate for `BALANCED7` is recorded here **only** as
metadata: it has not been independently re-audited and it is **not** Lean-proved.  This
ledger therefore keeps `BALANCED7 : open_`.

The downstream row `287-K0-SP2-UNIFORM-FRAGMENTATION-REASSEMBLY45` is `reduced`
(conditional compiler present, antecedent unavailable), and the first exact downstream
residual is `287-K0-SP2-THREE-SMALLPRIME-PREFIX-TYPEII45`, `analyticOpen`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace PostBalanced7ProStatus

open Erdos287.PostBalanced7Pro
open Erdos287.CurrentProgramme

/-! ## §1  The ledger -/

/-- The status nodes of the post-Balanced7 pass. -/
inductive Node
  | sevenBoxPrimeWeights45
  | primeTupleMultiplicity45
  | conductorSplitLargeSieve45
  | lowConductorSiegelWalfisz45
  | smallQ34LSNormalization45
  | smallQ34LSConditionalCompiler45
  | smallPrimePrefixDecomposition45
  | truncatedMoebiusObstruction45
  | threeSmallPrimePrefixTypeII45
  | postRepairOwnerNoDoubleSpending45
  | sp2BalancedSevenPostRepairFullQ45
  | k0UniformFragmentationReassembly45
  | balancedSeven
  | effectivePolylogModulusReplacement45
  | fcl
  | erdos287
  deriving DecidableEq, Fintype, Repr

/-- The status labels.  `closed` exists only so that "no closed rows" is a statement about
this ledger; it is never used. -/
inductive Label
  | closed
  | provedFinite
  | provedAlgebraic
  | conditionalCompiler
  | reduced
  | sourceOpen
  | analyticOpen
  | open_
  deriving DecidableEq, Fintype, Repr

open Node Label

/-- The post-Balanced7 ledger. -/
def ledger : Node → Label
  | sevenBoxPrimeWeights45 => provedFinite
  | primeTupleMultiplicity45 => provedFinite
  | conductorSplitLargeSieve45 => provedFinite
  | lowConductorSiegelWalfisz45 => analyticOpen
  | smallQ34LSNormalization45 => sourceOpen
  | smallQ34LSConditionalCompiler45 => conditionalCompiler
  | smallPrimePrefixDecomposition45 => provedFinite
  | truncatedMoebiusObstruction45 => provedFinite
  | threeSmallPrimePrefixTypeII45 => analyticOpen
  | postRepairOwnerNoDoubleSpending45 => provedFinite
  | sp2BalancedSevenPostRepairFullQ45 => conditionalCompiler
  | k0UniformFragmentationReassembly45 => reduced
  | balancedSeven => open_
  | effectivePolylogModulusReplacement45 => analyticOpen
  | fcl => open_
  | erdos287 => open_

/-- The exact residual order of this pass; `0` means "not on the residual list". -/
def residualRank : Node → ℕ
  | smallQ34LSNormalization45 => 1
  | lowConductorSiegelWalfisz45 => 2
  | threeSmallPrimePrefixTypeII45 => 3
  | sp2BalancedSevenPostRepairFullQ45 => 4
  | _ => 0

/-! ## §2  Ledger integrity -/

/-- **`no_closed_rows`.**  `LEAN_PROVED`.  No row of this ledger is `closed`. -/
theorem no_closed_rows : ∀ n : Node, ledger n ≠ closed := by decide +kernel

/-- **`erdos287_open`.**  `LEAN_PROVED`. -/
theorem erdos287_open : ledger erdos287 = open_ ∧ open_ ≠ closed := by decide +kernel

/-- **`balanced7_open`.**  `LEAN_PROVED`.

Balanced7 stays open: the latest research/paper closure candidate is metadata only, has not
been independently re-audited, and is not Lean-proved. -/
theorem balanced7_open :
    ledger balancedSeven = open_ ∧ ledger fcl = open_ ∧
      open_ ≠ closed ∧ open_ ≠ provedFinite ∧ open_ ≠ conditionalCompiler ∧
      open_ ≠ reduced := by
  decide +kernel

/-- **`k0_is_reduced_not_closed`.**  `LEAN_PROVED`. -/
theorem k0_is_reduced_not_closed :
    ledger k0UniformFragmentationReassembly45 = reduced ∧ reduced ≠ closed := by
  decide +kernel

/-- **`first_downstream_residual_is_three_smallprime_prefix`.**  `LEAN_PROVED`.

Among the strictly downstream rows (the K0 fragmentation package), the first exact residual
is the `Ω(d) ≥ 3` small-prime-prefix Type-II input. -/
theorem first_downstream_residual_is_three_smallprime_prefix :
    ledger threeSmallPrimePrefixTypeII45 = analyticOpen ∧
      residualRank threeSmallPrimePrefixTypeII45 = 3 ∧
      (∀ n : Node, residualRank n = 3 → n = threeSmallPrimePrefixTypeII45) := by
  decide +kernel

/-- **`first_residual_is_smallq_34LS_normalisation`.**  `LEAN_PROVED`.

The controlling frontier is unchanged from pass 1: the first exact residual overall is still
the SmallQ `3+4` coefficient/source normalisation. -/
theorem first_residual_is_smallq_34LS_normalisation :
    residualRank smallQ34LSNormalization45 = 1 ∧
      (∀ n : Node, residualRank n = 1 → n = smallQ34LSNormalization45) ∧
      ledger smallQ34LSNormalization45 = sourceOpen := by
  decide +kernel

/-- **`effectivity_firewall`.**  `LEAN_PROVED`.

Nothing in this pass makes Balanced7 effective: the polylog modulus replacement stays
`analyticOpen`, and the tiny-modulus provider is explicitly ineffective. -/
theorem effectivity_firewall :
    ledger effectivePolylogModulusReplacement45 = analyticOpen ∧
      analyticOpen ≠ closed ∧
      (∀ (X : ℝ) (A sMax : ℕ) (psi : ℕ → ℕ → ℕ → ℝ) (thr : Option ℕ),
        BalancedSevenLowConductorSiegelWalfiszInput X A sMax psi thr →
          ∀ M : ℕ, thr ≠ some M) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro X A sMax psi thr h M
  exact lowConductor_effectivity_firewall h M

/-- **`ledger_is_honest`.**  `LEAN_PROVED`.

Each label of this pass is backed by what the repository actually contains:

* the `provedFinite` rows are backed by kernel-checked finite/arithmetic theorems (the
  conductor split, the smooth/rough uniqueness, the truncated-Möbius obstruction and the
  post-repair no-double-spending identity);
* the `sourceOpen` / `analyticOpen` rows are backed by interfaces that are *not* inhabited;
* the `conditionalCompiler` and `reduced` rows are implications only. -/
theorem ledger_is_honest :
    -- proved rows really are theorems
    (∀ (F : CharacterFamily) (D N : ℕ) (c : ℕ → ℂ),
        condSum F D N c + highCondSum F D N c = fullCondSum F N c) ∧
      (∀ (contrib : PostRepairCell → ℝ),
        ∑ o : PostRepairOwner, postRepairAccount contrib o = ∑ c : PostRepairCell, contrib c) ∧
      (¬ ∃ F : ℕ → ℤ, ∀ d m : ℕ, truncMoebius 2 (d * m) = F d) ∧
      -- open rows really are uninhabited interfaces
      (∃ (z X : ℕ) (w : ℕ → ℝ) (Xr eps : ℝ),
        ¬ ThreeSmallPrimePrefixTypeIIInput z X w Xr eps) ∧
      (∃ (X : ℝ) (A sMax : ℕ) (psi : ℕ → ℕ → ℕ → ℝ) (thr : Option ℕ),
        ¬ BalancedSevenLowConductorSiegelWalfiszInput X A sMax psi thr) ∧
      -- conditional rows really are only implications
      (∃ (R : ℝ → ℝ) (frag : ℕ → ℝ → ℝ) (K : ℕ) (a b : Prop),
        ¬ K0UniformFragmentationInputs R frag K a b) ∧
      (∃ (S : ℝ → ℝ) (cellVal : PostRepairCell → ℝ → ℝ) (a b c d : Prop),
        ¬ BalancedSevenPostRepairInputs S cellVal a b c d) :=
  ⟨fun F D N c => condSum_add_highCondSum F D N c,
    postRepair_no_double_spending,
    truncMoebius_not_prefix_factorisable,
    threeSmallPrimePrefix_not_automatic,
    lowConductorSiegelWalfisz_not_automatic,
    k0FragmentationInputs_not_inhabited_here,
    postRepairInputs_not_inhabited_here⟩

/-- **`downstream_not_activated`.**  `LEAN_PROVED`.

The K0 fragmentation reassembly is not activated: its bundle is refuted by explicit data,
and it can never be formed while the `Ω(d) ≥ 3` Type-II source is unavailable. -/
theorem downstream_not_activated :
    ledger k0UniformFragmentationReassembly45 = reduced ∧
      (∀ (R : ℝ → ℝ) (frag : ℕ → ℝ → ℝ) (K : ℕ) (a : Prop),
        ¬ K0UniformFragmentationInputs R frag K a False) :=
  ⟨by decide +kernel, k0_residual_is_three_prefix⟩

end PostBalanced7ProStatus
end Erdos287
