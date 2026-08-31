import Mathlib
import RequestProject.HostileAudit.BalancedSevenHostileAuditCompiler
import RequestProject.HostileAudit.RawRawVarianceCompiler

/-!
# Append-only status module — Erdős #287, Balanced7 hostile-audit safe bank

This module is **append-only**: the V15–V24 / SP-2 / post-Balanced7 "Pro" ledgers are not
modified, and no historical row is deleted or rewritten.

It records the state after the independent hostile audit of the Balanced7 analysis.  The
audit is *external mathematics*: it is metadata here, never a Lean theorem.  Accordingly the
label `externallyAudited` is introduced and is provably distinct from every "proved" label.

It also records, as metadata, the two **retracted death certificates** of §6:

* `SMALLQ-LS-DEATH-CERTIFICATE : RETRACTED` — it dropped `f·k ∼ Q`, hence dropped `k ≪ Q/D`;
* `SMALLR-GENERAL-MODULUS-DEATH-CERTIFICATE : RETRACTED` — the induced-character identity
  with `j = r/f` is valid for arbitrary `r`, and the `D`-saving comes from `j ≪ R/D`
  (both facts are now Lean theorems: `induced_character_pointwise`,
  `complementary_factor_bound`).

`BALANCED7`, `FCL` and `ERDOS287` remain **open**; there is no `closed` row.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace Balanced7HostileAuditStatus

open Erdos287.HostileAudit
open Erdos287.CurrentProgramme
open Erdos287.PostBalanced7Pro

/-! ## §1  The ledger -/

/-- The nodes of the hostile-audit pass. -/
inductive Node
  | balancedSevenSP2SourceAdapter45
  | generalModulusInducedCharacter45
  | totientComplementaryFactor45
  | smallQ34LS45
  | smallRGeneralModulusLS45
  | smallROwnerSubtraction45
  | hardDelta45
  | shortT45
  | shiu45
  | rawRaw45
  | allQNoDoubleSpending45
  | smallQLSDeathCertificate
  | smallRGeneralModulusDeathCertificate
  | effectiveLowCondExceptionalPNT45
  | balancedSeven
  | balancedSevenEffective
  | k0UniformFragmentationReassembly45
  | threeSmallPrimePrefixTypeII45
  | n2
  | gate2
  | windowPairSupply
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
  | externallyAudited
  | retracted
  | reduced
  | notActivated
  | sourceOpen
  | analyticOpen
  | open_
  deriving DecidableEq, Fintype, Repr

open Node Label

/-- The hostile-audit ledger. -/
def ledger : Node → Label
  | balancedSevenSP2SourceAdapter45 => sourceOpen
  | generalModulusInducedCharacter45 => provedAlgebraic
  | totientComplementaryFactor45 => provedAlgebraic
  | smallQ34LS45 => externallyAudited
  | smallRGeneralModulusLS45 => externallyAudited
  | smallROwnerSubtraction45 => provedAlgebraic
  | hardDelta45 => provedAlgebraic
  | shortT45 => externallyAudited
  | shiu45 => externallyAudited
  | rawRaw45 => externallyAudited
  | allQNoDoubleSpending45 => provedAlgebraic
  | smallQLSDeathCertificate => retracted
  | smallRGeneralModulusDeathCertificate => retracted
  | effectiveLowCondExceptionalPNT45 => sourceOpen
  | balancedSeven => externallyAudited
  | balancedSevenEffective => open_
  | k0UniformFragmentationReassembly45 => reduced
  | threeSmallPrimePrefixTypeII45 => analyticOpen
  | n2 => notActivated
  | gate2 => conditionalCompiler
  | windowPairSupply => open_
  | fcl => open_
  | erdos287 => open_

/-- Which rows additionally carry a *proved* conditional compiler in Lean. -/
def hasConditionalCompiler : Node → Bool
  | smallQ34LS45 => true
  | smallRGeneralModulusLS45 => true
  | shortT45 => true
  | shiu45 => true
  | rawRaw45 => true
  | balancedSeven => true
  | effectiveLowCondExceptionalPNT45 => true
  | gate2 => true
  | _ => false

/-- The exact residual order of the main line; `0` means "not on the residual list". -/
def residualRank : Node → ℕ
  | threeSmallPrimePrefixTypeII45 => 1
  | balancedSevenSP2SourceAdapter45 => 2
  | effectiveLowCondExceptionalPNT45 => 3
  | k0UniformFragmentationReassembly45 => 4
  | _ => 0

/-! ## §2  Ledger integrity -/

/-- **`no_closed_rows`.**  `LEAN_PROVED`.  No row of this ledger is `closed`. -/
theorem no_closed_rows : ∀ n : Node, ledger n ≠ closed := by decide +kernel

/-- **`erdos287_open`.**  `LEAN_PROVED`. -/
theorem erdos287_open : ledger erdos287 = open_ ∧ ledger fcl = open_ := by decide +kernel

/-- **`externallyAudited_is_not_proved`.**  `LEAN_PROVED`.

The central honesty statement of this pass: an external hostile audit is a *different* label
from every Lean-proved label, and from `closed`. -/
theorem externallyAudited_is_not_proved :
    externallyAudited ≠ closed ∧ externallyAudited ≠ provedFinite ∧
      externallyAudited ≠ provedAlgebraic ∧ externallyAudited ≠ conditionalCompiler := by
  decide +kernel

/-- **`balanced7_is_audited_not_proved`.**  `LEAN_PROVED`.

`BALANCED7` is recorded as a hostile-audited research/paper pass, **not** as a Lean analytic
theorem, and its effective version stays open. -/
theorem balanced7_is_audited_not_proved :
    ledger balancedSeven = externallyAudited ∧
      ledger balancedSevenEffective = open_ ∧
      externallyAudited ≠ closed := by
  decide +kernel

/-- **`death_certificates_retracted`.**  `LEAN_PROVED` (metadata + the two theorems that
force the retraction).

* the SmallQ LS death certificate dropped `f·k ∼ Q`, hence `k ≪ Q/D`;
* the SmallR general-modulus death certificate assumed the induced-character identity needs
  `r` squarefree or `gcd(f,j) = 1`, which is false — and the `D`-saving really does come from
  `j < 2R/D`. -/
theorem death_certificates_retracted :
    ledger smallQLSDeathCertificate = retracted ∧
      ledger smallRGeneralModulusDeathCertificate = retracted ∧
      -- the induced-character identity holds with a non-squarefree modulus, `gcd(f,j) ≠ 1`
      (∀ n : ℕ, (if Nat.Coprime n 4 then (1 : ℂ) else 0)
        = (if Nat.Coprime n 2 then (1 : ℂ) else 0) * coprimeIndicator n 2) ∧
      -- and the `D`-saving is the complementary-factor bound
      (∀ D f j R : ℝ, 0 < D → D < f → 0 ≤ j → f * j < 2 * R → j < 2 * R / D) :=
  ⟨by decide +kernel, by decide +kernel, induced_character_nonSquarefree_instance,
    fun _ _ _ _ hD hDf hj hw => complementary_factor_bound hD hDf hj hw⟩

/-- **`first_mainline_residual_is_three_smallprime_prefix`.**  `LEAN_PROVED`. -/
theorem first_mainline_residual_is_three_smallprime_prefix :
    ledger threeSmallPrimePrefixTypeII45 = analyticOpen ∧
      residualRank threeSmallPrimePrefixTypeII45 = 1 ∧
      (∀ n : Node, residualRank n = 1 → n = threeSmallPrimePrefixTypeII45) := by
  decide +kernel

/-- **`source_seal_is_open`.**  `LEAN_PROVED`.

Section 2 did **not** succeed in sealing the source: the adapter is `sourceOpen`, and it is
refuted by explicit data.  Balanced7 is therefore *not* recorded as source-sealed. -/
theorem source_seal_is_open :
    ledger balancedSevenSP2SourceAdapter45 = sourceOpen ∧
      (∃ (C : Erdos287.SP2Source.SP2FixedCertificateData) (sector : Finset ℕ) (Hs : ℕ → ℤ)
        (cut : ℕ → ℕ) (V : Fin 7 → ℝ → ℝ) (phase : Fin 7 → ℕ → ℂ) (Y : ℝ)
        (omegaSrc : Fin 7 → ℕ → ℂ),
        ¬ BalancedSevenSP2SourceSeal C sector Hs cut V phase Y omegaSrc) :=
  ⟨by decide +kernel, sp2SourceSeal_not_automatic⟩

/-- **`effectivity_socket_is_open`.**  `LEAN_PROVED`.

`287-EFFECTIVE-LOWCOND-EXCEPTIONAL-PNT45` is a source/theorem dictionary node: the socket is
present, has a conditional consumer, and is not inhabited. -/
theorem effectivity_socket_is_open :
    ledger effectiveLowCondExceptionalPNT45 = sourceOpen ∧
      hasConditionalCompiler effectiveLowCondExceptionalPNT45 = true ∧
      (∃ (X C1 C2 X0 : ℝ) (A f q : ℕ) (V : ℝ → ℝ) (Tmell psi mainTerm secondaryTerm : ℝ)
        (exceptional : Option (ℕ × ℝ)),
        ¬ EffectiveLowConductorExceptionalPNTInput X C1 C2 X0 A f q V Tmell psi mainTerm
          secondaryTerm exceptional) :=
  ⟨by decide +kernel, by decide +kernel, effectiveLowConductor_not_automatic⟩

/-- **`downstream_frontier_preserved`.**  `LEAN_PROVED`.

The downstream frontier of §16 is unchanged: K0 fragmentation `reduced`, the `Ω(d) ≥ 3`
Type-II prefix `analyticOpen`, `N2` not activated, `Gate2` conditional, the window-pair supply
open, `FCL` open, `ERDOS287` open. -/
theorem downstream_frontier_preserved :
    ledger k0UniformFragmentationReassembly45 = reduced ∧
      ledger threeSmallPrimePrefixTypeII45 = analyticOpen ∧
      ledger n2 = notActivated ∧
      ledger gate2 = conditionalCompiler ∧
      ledger windowPairSupply = open_ ∧
      ledger fcl = open_ ∧
      ledger erdos287 = open_ := by
  decide +kernel

/-- **`ledger_is_honest`.**  `LEAN_PROVED`.

Each label of this pass is backed by what the repository actually contains:

* the `provedAlgebraic` rows are backed by kernel-checked theorems (the induced-character
  identity, the complementary-factor bound, the SmallR owner subtraction, the hard-`δ`
  rational ledger, the full-`q` no-double-spending identity);
* the `externallyAudited` and `sourceOpen` rows are backed by interfaces that are **not**
  inhabited;
* the `conditionalCompiler` content is implications only. -/
theorem ledger_is_honest :
    -- proved rows really are theorems
    (∀ (chiStar chiR : ℕ → ℂ) (f j : ℕ), InducedCharacterSpec chiStar chiR f j →
        ∀ n : ℕ, chiR n = chiStar n * coprimeIndicator n j) ∧
      (∀ (u N : ℕ) (coeff : ℕ × ℕ → ℝ) (mPrin : ℝ),
        sSmallR u N coeff = mPrin + dSmallR u N coeff mPrin) ∧
      (∀ val : FullQCell → ℝ,
        ∑ o : PostRepairOwner, fullQAccount val o = ∑ c : FullQCell, val c) ∧
      (hardCellLogExponent = -5 / 2) ∧
      -- open rows really are uninhabited interfaces
      (∃ (N : ℕ) (Rr : ℝ) (cells : Finset (ℕ × ℕ)) (Lval : ℕ × ℕ → ℝ) (E : ℕ → ℝ),
        ¬ PrimitiveWeightedLargeSieveInput N Rr cells Lval E) ∧
      (∃ X theta C R : ℝ, ¬ BalancedSevenShortTSieveInput X theta C R) ∧
      (∃ (Wprime s : ℕ) (Mbox : Finset ℕ) (Mlen : ℕ) (Cshiu : ℝ),
        ¬ BalancedSevenShiuInput Wprime s Mbox Mlen Cshiu) ∧
      -- the Balanced7 bundle is only an implication
      (∃ (S : ℝ → ℝ) (cellVal : FullQCell → ℝ → ℝ) (a b c d e f g i : Prop),
        ¬ BalancedSevenHostileAuditInputs S cellVal a b c d e f g i) :=
  ⟨fun _ _ _ _ h n => induced_character_pointwise h n,
    smallR_source_eq_principal_add_defect,
    fullQ_no_double_spending,
    (hard_cell_log_budget).1,
    primitiveLargeSieve_not_automatic,
    shortTSieve_still_uninhabited,
    shiu_input_still_uninhabited,
    hostileAuditInputs_not_inhabited_here⟩

/-- **`rawRaw_row_uses_the_corrected_exponent`.**  `LEAN_PROVED`.

The `rawRaw45` row records the corrected `log^{-5}` saving: the `log^{-10}` version is
refuted by explicit admissible data. -/
theorem rawRaw_row_uses_the_corrected_exponent :
    ledger rawRaw45 = externallyAudited ∧
      ∃ (M W5 Q L alpha2 c1 c2 VRR : ℝ),
        RawRawVarianceInputs M W5 Q L alpha2 c1 c2 VRR True True ∧
          VRR ≤ M * W5 ^ 2 / Q / L ^ 5 ∧ ¬ (VRR ≤ M * W5 ^ 2 / Q / L ^ 10) :=
  ⟨by decide +kernel, rawRaw_saving_is_five_not_ten⟩

end Balanced7HostileAuditStatus
end Erdos287
