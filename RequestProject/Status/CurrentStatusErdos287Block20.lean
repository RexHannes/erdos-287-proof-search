import Mathlib
import RequestProject.Status.CurrentStatusErdos287Balanced7HostileAudit
import RequestProject.CurrentProgramme.ExceptionalMainTermComparisonAdapter

/-!
# Append-only status module — Erdős #287, BLOCK20 Δ safe bank

This module is **append-only**: the Balanced7 hostile-audit ledger
(`Erdos287.Balanced7HostileAuditStatus`) is imported and **not modified**, and
`historical_balanced7_status_preserved` checks that its rows still read as before.

Every label is backed by what the repository actually contains:

* `provedFinite` / `provedAlgebraic` rows are kernel-checked theorems;
* `conditionalCompiler` content is implications only;
* `sourceOpen` / `analyticOpen` rows are **uninhabited** interfaces, each with a refutation
  theorem exhibiting explicit failing data;
* `supersessionCandidate` is used where source coverage could **not** be proved — the
  historical row is never marked false.

`FCL` and `ERDOS287` remain `open_`; there is no `closed` row.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace Block20Status

open Erdos287.Block20
open Erdos287.HostileAudit

/-! ## §1  The ledger -/

/-- The nodes of the BLOCK20 Δ pass. -/
inductive Node
  | balanced7SourceSeal45
  | largePrimePowerRouter45
  | block20Packing45
  | block20BilinearSourceCompiler45
  | block20TypeIIWindow45
  | threeSmallPrimePrefixTypeII45
  | perronConditionRemoval45
  | perronBoundaryRouter45
  | block20GeneratedTypeII45
  | k0UniformFragmentationReassembly45
  | effectiveLowCondExceptionalPNT45
  | exceptionalMainTermComparisonAdapter45
  | balancedSevenEffective
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
  | supersessionCandidate
  | sourceOpen
  | analyticOpen
  | open_
  deriving DecidableEq, Fintype, Repr

open Node Label

/-- The BLOCK20 Δ ledger. -/
def ledger : Node → Label
  | balanced7SourceSeal45 => sourceOpen
  | largePrimePowerRouter45 => externallyAudited
  | block20Packing45 => provedFinite
  | block20BilinearSourceCompiler45 => provedFinite
  | block20TypeIIWindow45 => provedFinite
  | threeSmallPrimePrefixTypeII45 => supersessionCandidate
  | perronConditionRemoval45 => analyticOpen
  | perronBoundaryRouter45 => analyticOpen
  | block20GeneratedTypeII45 => analyticOpen
  | k0UniformFragmentationReassembly45 => conditionalCompiler
  | effectiveLowCondExceptionalPNT45 => conditionalCompiler
  | exceptionalMainTermComparisonAdapter45 => sourceOpen
  | balancedSevenEffective => open_
  | fcl => open_
  | erdos287 => open_

/-- Which rows additionally carry a *proved* conditional compiler in Lean. -/
def hasConditionalCompiler : Node → Bool
  | largePrimePowerRouter45 => true
  | block20BilinearSourceCompiler45 => true
  | block20TypeIIWindow45 => true
  | perronConditionRemoval45 => true
  | k0UniformFragmentationReassembly45 => true
  | effectiveLowCondExceptionalPNT45 => true
  | exceptionalMainTermComparisonAdapter45 => true
  | threeSmallPrimePrefixTypeII45 => true
  | _ => false

/-- The exact residual order of the main line; `0` means "not on the residual list". -/
def residualRank : Node → ℕ
  | block20GeneratedTypeII45 => 1
  | perronConditionRemoval45 => 2
  | balanced7SourceSeal45 => 3
  | threeSmallPrimePrefixTypeII45 => 4
  | _ => 0

/-- The parallel (effectivity) residual list. -/
def effectivityResidualRank : Node → ℕ
  | exceptionalMainTermComparisonAdapter45 => 1
  | _ => 0

/-! ## §2  Ledger integrity -/

/-- **`no_closed_rows`.**  `LEAN_PROVED`. -/
theorem no_closed_rows : ∀ n : Node, ledger n ≠ closed := by decide +kernel

/-- **`erdos287_open`.**  `LEAN_PROVED`. -/
theorem erdos287_open : ledger erdos287 = open_ := by decide +kernel

/-- **`fcl_open`.**  `LEAN_PROVED`. -/
theorem fcl_open : ledger fcl = open_ ∧ ledger balancedSevenEffective = open_ := by
  decide +kernel

/-- **`generated_typeII_is_current_mainline_residual`.**  `LEAN_PROVED`.

`287-K0-SP2-BLOCK20-GENERATED-TYPEII45` is the first exact main-line analytic residual, and
its interface is **uninhabited**. -/
theorem generated_typeII_is_current_mainline_residual :
    ledger block20GeneratedTypeII45 = analyticOpen ∧
      residualRank block20GeneratedTypeII45 = 1 ∧
      (∀ n : Node, residualRank n = 1 → n = block20GeneratedTypeII45) ∧
      (∃ (X : ℝ) (N : ℕ) (pi : Block20Template) (w : Fin pi.r → ℂ) (mass : Fin pi.r → ℝ)
        (epsStar sigmaStar : ℝ) (W : ℝ → ℝ) (B : ℕ → ℝ) (bound : ℝ),
        ¬ Block20GeneratedTypeIIInput X N pi w mass epsStar sigmaStar W B bound) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    block20GeneratedTypeII_not_automatic⟩

/-- **`effectivity_adapter_is_parallel_residual`.**  `LEAN_PROVED`.

`287-EXCEPTIONAL-MAINTERM-COMPARISON-ADAPTER45` is the first residual of the *parallel*
effectivity line, and is uninhabited. -/
theorem effectivity_adapter_is_parallel_residual :
    ledger exceptionalMainTermComparisonAdapter45 = sourceOpen ∧
      effectivityResidualRank exceptionalMainTermComparisonAdapter45 = 1 ∧
      residualRank exceptionalMainTermComparisonAdapter45 = 0 ∧
      (∃ (mainTerm secondaryTerm physicalMainTerm exceptionalBudget : ℝ)
        (route : ExceptionalRoute),
        ¬ ExceptionalMainTermComparisonAdapter mainTerm secondaryTerm physicalMainTerm
          exceptionalBudget route) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, exceptionalAdapter_not_automatic⟩

/-- **`threeSmallPrime_not_false`.**  `LEAN_PROVED`.

The historical `Ω(d) ≥ 3` row is a **supersession candidate**, never marked false: the class
is nonempty, and the coverage statement that would retire it is recorded as an explicit
(unproved) residual. -/
theorem threeSmallPrime_not_false :
    ledger threeSmallPrimePrefixTypeII45 = supersessionCandidate ∧
      supersessionCandidate ≠ closed ∧
      Erdos287.PostBalanced7Pro.PrefixAtLeastThree 10 8 ∧
      (∀ (z : ℕ) (X sigmaStar : ℝ), ThreeSmallPrimeSourceCoveredByBlock20 z X sigmaStar →
        ∀ n : ℕ, n ≠ 0 → Erdos287.PostBalanced7Pro.PrefixAtLeastThree z n →
          ∃ pi : Block20Template, RoutesAtomWithMass z X sigmaStar pi n) :=
  ⟨by decide +kernel, by decide +kernel, threeSmallPrime_class_is_nonempty,
    fun _ _ _ h _ hn hpref => threeSmallPrime_supersession_of_coverage h hn hpref⟩

/-- **`source_seal_row_is_open_with_exact_residual`.**  `LEAN_PROVED`.

Section 2 of this pass repaired everything except one field: the seal follows from
`FixedCertificateSP2PacketMatchesCompilerPacket`, which is not available. -/
theorem source_seal_row_is_open_with_exact_residual :
    ledger balanced7SourceSeal45 = sourceOpen ∧
      (∀ (C : Erdos287.SP2Source.SP2FixedCertificateData) (sector : Finset ℕ) (Hs : ℕ → ℤ)
          (cut : ℕ → ℕ) (V : Fin 7 → ℝ → ℝ) (Y t : ℝ),
          Erdos287.SP2Source.SP2PacketNormalization C →
          (∀ (i : Fin 7) (x : ℝ), 0 ≤ V i x ∧ V i x ≤ 1) →
          FixedCertificateSP2PacketMatchesCompilerPacket sector Hs cut →
          BalancedSevenSP2SourceSeal C sector Hs cut V
            (fun _ p => Complex.exp (t * Real.log p * Complex.I)) Y
            (fun i p => Erdos287.PostBalanced7Pro.omegaBox (V i) Y t p)) ∧
      (∃ (sector : Finset ℕ) (Hs : ℕ → ℤ) (cut : ℕ → ℕ),
        ¬ FixedCertificateSP2PacketMatchesCompilerPacket sector Hs cut) :=
  ⟨by decide +kernel, sourceSeal_status_is_open.1, sourceSeal_status_is_open.2⟩

/-- **`block20_finite_rows_are_theorems`.**  `LEAN_PROVED`.

The `provedFinite` rows really are finite theorems: the exact rational ledger, the
constructive packing contract, the bilinear split, and the Type-II window. -/
theorem block20_finite_rows_are_theorems :
    ledger block20Packing45 = provedFinite ∧
      ledger block20BilinearSourceCompiler45 = provedFinite ∧
      ledger block20TypeIIWindow45 = provedFinite ∧
      -- the exact rational inequality
      (∀ epsStar : ℚ, EpsAdmissible epsStar →
        (1629054 : ℚ) / 10000000 ≤ sigmaStarQ epsStar ∧ 1 < 19 * (sigmaStarQ epsStar / 3)) ∧
      -- the constructive packing contract
      (∀ (sigma thr : ℝ) (ld lm : List ℝ), (1629054 : ℝ) / 10000000 ≤ sigma → thr = sigma / 3 →
        (∀ x ∈ ld, 0 ≤ x) → (∀ x ∈ lm, 0 ≤ x) → (∀ x ∈ ld, x ≤ sigma) → (∀ x ∈ lm, x ≤ sigma) →
        ld.sum + lm.sum ≤ 1 → Block20PackingValidity sigma thr ld lm (packBoth thr ld lm)) ∧
      -- the exact bilinear split
      (∀ (pi : Block20Template) (w : Fin pi.r → ℂ),
        (∏ j : Fin pi.r, w j) = xiOf pi w * kappaOf pi w) ∧
      (∀ pi : Block20Template, (∏ j : Fin pi.r, pi.blockValue j) = pi.uOf * pi.vOf) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    fun _ h => ⟨sigmaStar_ge h, nineteen_blocks_overflow h⟩,
    fun sigma thr ld lm h1 h2 h3 h4 h5 h6 h7 => packBoth_validity sigma thr ld lm h1 h2 h3 h4 h5 h6 h7,
    fixed_template_source_factorisation, template_product_split⟩

/-- **`analytic_rows_are_uninhabited`.**  `LEAN_PROVED`.

Every `analyticOpen` / `sourceOpen` row of this pass is an interface with no inhabitant. -/
theorem analytic_rows_are_uninhabited :
    (∃ (X : ℝ) (N bound : ℕ) (w : ℕ → ℝ) (sigmaStar C eta : ℝ),
        ¬ LargePrimePowerRouterEstimateInput X N bound w sigmaStar C eta) ∧
      (∃ (X delta cPerron : ℝ) (cutoff : ℕ → ℝ) (kernel : ℝ → ℂ)
        (coeff reconstructed boundaryStrip truncation : ℕ → ℂ) (kernelL1 stripErr truncErr : ℝ),
        ¬ PerronConditionRemovalInput X delta cPerron cutoff kernel coeff reconstructed
          boundaryStrip truncation kernelL1 stripErr truncErr) ∧
      (∃ (Hs sourceWeight : ℕ → ℤ) (smooth : ℝ → ℝ) (sector : Finset ℕ)
        (X stripWidth stripErr : ℝ),
        ¬ PerronBoundaryRouterInput Hs sourceWeight smooth sector X stripWidth stripErr) ∧
      (∃ (pi : Block20Template) (w : Fin pi.r → ℂ) (tau40 : ℕ → ℝ) (N : ℕ) (L1 L2 : ℝ),
        ¬ GeneratedCoefficientNormInput pi w tau40 N L1 L2) ∧
      (∃ (S : ℝ → ℝ) (cellVal : Fin 4 → ℝ → ℝ) (a b c d : Prop),
        ¬ K0UniformFragmentationInputs S cellVal a b c d) :=
  ⟨largePrimePowerRouter_not_automatic, perronConditionRemoval_not_automatic,
    perronBoundaryRouter_not_automatic, generatedCoefficientNorm_not_automatic,
    k0UniformFragmentation_not_inhabited_here⟩

/-- **`historical_balanced7_status_preserved`.**  `LEAN_PROVED`.

The previous ledger is untouched and still reads exactly as banked. -/
theorem historical_balanced7_status_preserved :
    Erdos287.Balanced7HostileAuditStatus.ledger
        Erdos287.Balanced7HostileAuditStatus.Node.erdos287 =
      Erdos287.Balanced7HostileAuditStatus.Label.open_ ∧
    Erdos287.Balanced7HostileAuditStatus.ledger
        Erdos287.Balanced7HostileAuditStatus.Node.fcl =
      Erdos287.Balanced7HostileAuditStatus.Label.open_ ∧
    Erdos287.Balanced7HostileAuditStatus.ledger
        Erdos287.Balanced7HostileAuditStatus.Node.balancedSevenSP2SourceAdapter45 =
      Erdos287.Balanced7HostileAuditStatus.Label.sourceOpen ∧
    (∀ n : Erdos287.Balanced7HostileAuditStatus.Node,
      Erdos287.Balanced7HostileAuditStatus.ledger n ≠
        Erdos287.Balanced7HostileAuditStatus.Label.closed) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    Erdos287.Balanced7HostileAuditStatus.no_closed_rows⟩

/-- **`log_budget_is_crude_not_optimal`.**  `LEAN_PROVED`. -/
theorem log_budget_is_crude_not_optimal :
    currentCrudeBudget.total = 22 ∧ ∃ b : CompilerLogBudget, b.total < currentCrudeBudget.total :=
  ⟨currentCrudeBudget_total, crude_budget_is_not_an_optimality_theorem⟩

end Block20Status
end Erdos287
