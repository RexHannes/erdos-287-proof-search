import Mathlib
import RequestProject.Status.SemanticFirewallsErdos287

/-!
# Authoritative status and semantic object ledger — Erdős #287

This module is **append-only** and contains **no new mathematical claim**.  It is the single
authoritative record of

* which status layer takes precedence when older layers disagree (§1);
* the semantic object ledger: what each recurring symbol denotes (§2);
* the split of the overloaded objects: `q`-roles, `x`/`X`, C0 levels, Ω-norms, Type-II names,
  coverage scopes (§3–§6);
* the classification of `WindowPairSupply` (§7);
* the frontier DAG and the retraction ledger (§8–§9);
* the resource / margin / constant-selection / source-normalisation ledgers (§10);
* the risk classification `S0`–`S6` with exact counts, and the critical pre-closure
  blockers (§11–§12).

Every fact below is a decidable metadata fact discharged by the kernel.  No status value carries
any implication of mathematical truth; in particular Erdős #287 remains **open**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace AuthoritativeStatus

open Erdos287.C0UnitaryFourierStatus

/-! ## §1  Status layers and the precedence rule -/

/-- The chronological status layers of the project. -/
inductive StatusLayer
  /-- Early V-series status files. -/
  | vSeries
  /-- Balanced-7 / post-audit layer. -/
  | balancedSeven
  /-- C0 unitary Fourier layer. -/
  | c0UnitaryFourier
  /-- Transverse carrier layer. -/
  | transverseCarrier
  /-- One-conductor / Bézout single-carrier layer. -/
  | oneConductor
  /-- Dual-level / simultaneous-critical layer (most recent). -/
  | dualLevelSimultaneousCritical
  deriving DecidableEq, Fintype, Repr

/-- Chronological index of a layer; larger means later. -/
def layerIndex : StatusLayer → ℕ
  | .vSeries => 0
  | .balancedSeven => 1
  | .c0UnitaryFourier => 2
  | .transverseCarrier => 3
  | .oneConductor => 4
  | .dualLevelSimultaneousCritical => 5

/-- The authoritative layer: the most recent one. -/
def authoritativeLayer : StatusLayer := .dualLevelSimultaneousCritical

/-- **Precedence rule.**  Where two layers disagree about a *label*, the later layer governs;
the earlier layer is preserved as history and is never rewritten. -/
theorem authoritative_layer_is_latest :
    ∀ L : StatusLayer, layerIndex L ≤ layerIndex authoritativeLayer := by
  decide +kernel

/-- The layer ordering is strict and total on indices. -/
theorem layerIndex_injective :
    ∀ L L' : StatusLayer, layerIndex L = layerIndex L' → L = L' := by
  decide +kernel

/-! ## §2  Semantic object ledger -/

/-- The role played by a recurring symbol of the programme. -/
inductive ObjectRole
  /-- A modulus-like arithmetic object. -/
  | modulus
  /-- A scale parameter (a size, not an object). -/
  | scale
  /-- A source coefficient family / norm. -/
  | sourceNorm
  /-- A logical predicate about the actual problem. -/
  | problemPredicate
  /-- A compiler input, i.e. an explicit hypothesis. -/
  | compilerInput
  /-- A metadata label with no mathematical content. -/
  | metadataLabel
  deriving DecidableEq, Fintype, Repr

/-- The recurring symbols audited by this ledger. -/
inductive SemanticObject
  /-- `q` — ambiguous in prose; see the `q`-role split of §3. -/
  | qSymbol
  /-- `Q` — the *range* of the `q`-axis, a scale. -/
  | QRange
  /-- `q_eff` — the effective modulus after conductor reduction. -/
  | qEff
  /-- `x` — a small-scale variable. -/
  | smallX
  /-- `X` — the global large scale. -/
  | bigX
  /-- `E*` — the carrier factor family. -/
  | EStar
  /-- `Omega_H` — the shared-gcd Ω normalisation source. -/
  | OmegaH
  /-- `b*` — the b-diagonal coefficient family. -/
  | bStar
  /-- Type-I level decomposition. -/
  | levelTypeI
  /-- Type-II level decomposition. -/
  | levelTypeII
  /-- The C0 face. -/
  | c0Face
  /-- The transverse face. -/
  | transverseFace
  /-- The b-diagonal face. -/
  | bDiagonalFace
  /-- Coverage percentages. -/
  | coverage
  /-- `WindowPairSupply` — a sufficient end-to-end input. -/
  | windowPairSupply
  /-- `Gap2CE` — the relaxed counterexample type. -/
  | gap2CE
  /-- `Erdos287Statement` — the actual problem statement. -/
  | erdos287Statement
  deriving DecidableEq, Fintype, Repr

/-- The authoritative role of each audited symbol. -/
def objectRole : SemanticObject → ObjectRole
  | .qSymbol => .modulus
  | .QRange => .scale
  | .qEff => .modulus
  | .smallX => .scale
  | .bigX => .scale
  | .EStar => .modulus
  | .OmegaH => .sourceNorm
  | .bStar => .sourceNorm
  | .levelTypeI => .metadataLabel
  | .levelTypeII => .metadataLabel
  | .c0Face => .metadataLabel
  | .transverseFace => .metadataLabel
  | .bDiagonalFace => .metadataLabel
  | .coverage => .metadataLabel
  | .windowPairSupply => .compilerInput
  | .gap2CE => .problemPredicate
  | .erdos287Statement => .problemPredicate

/-- **Role firewall.**  A modulus is never a scale: `q` and `Q` have different roles, and so do
`x` and `E*`. -/
theorem modulus_is_not_scale :
    objectRole .qSymbol ≠ objectRole .QRange ∧
      objectRole .EStar ≠ objectRole .smallX := by
  decide +kernel

/-- **`x`/`X` firewall (metadata form).**  Both are scales, but they are distinct objects. -/
theorem smallX_ne_bigX : (SemanticObject.smallX) ≠ SemanticObject.bigX := by decide +kernel

/-- **Predicate firewall.**  `Gap2CE` and `Erdos287Statement` are distinct objects even though
both are problem predicates; the bridge between them is one-way (see
`Erdos287.SemanticFirewalls.gap2CE_firewall`). -/
theorem gap2CE_ne_statement :
    (SemanticObject.gap2CE) ≠ SemanticObject.erdos287Statement := by decide +kernel

/-! ## §3  The `q`-role split -/

/-- Scoped alias table: which `q`-role each occurrence of the bare symbol must be resolved to.
The bare symbol `q` is **not** admissible in a status claim without one of these labels. -/
def qRoleName : Erdos287.SemanticFirewalls.QRole → String
  | .qSwitch => "q_switch"
  | .qLocal => "q_local"
  | .qEff => "q_eff"
  | .qTransverse => "q_transverse"

/-- The role names are pairwise distinct strings. -/
theorem qRoleName_distinct :
    qRoleName .qSwitch ≠ qRoleName .qLocal ∧
      qRoleName .qLocal ≠ qRoleName .qEff ∧
      qRoleName .qEff ≠ qRoleName .qTransverse := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [qRoleName]

/-! ## §4  The three levels of C0 -/

/-- The three distinct statements that have all been called "C0". -/
inductive C0Level
  /-- C0 as a finite kernel-checked arithmetic/Fourier statement. -/
  | finiteKernel
  /-- C0 as an analytic estimate closed at research level. -/
  | analyticEstimate
  /-- C0 as a physical-source claim requiring the full normalisation. -/
  | physicalSource
  deriving DecidableEq, Fintype, Repr

/-- The authoritative status of each C0 level. -/
def c0LevelStatus : C0Level → ResearchStatus
  | .finiteKernel => .kernelProved
  | .analyticEstimate => .analyticBanked
  | .physicalSource => .conditionalSourcePin

/-- **C0 firewall.**  The three levels carry three different statuses; "C0 is closed" is not a
well-formed claim without a level label. -/
theorem c0_levels_have_distinct_status :
    c0LevelStatus .finiteKernel ≠ c0LevelStatus .analyticEstimate ∧
      c0LevelStatus .analyticEstimate ≠ c0LevelStatus .physicalSource := by
  decide +kernel

/-! ## §5  The four Ω-norms -/

/-- The four distinct Ω-normalisation objects in the programme. -/
inductive OmegaNorm
  /-- The shared-gcd `Ω_H` normalisation source pin. -/
  | sharedGcdOmegaH
  /-- The plain `L²` Ω shell. -/
  | plainL2Shell
  /-- The Perron / nuclear normalisation. -/
  | perronNuclear
  /-- The weighted divisor-moment norm `N_Ω,C = ∑_E |Ω_E|² C(E)/E²`. -/
  | weightedDivisorMoment
  deriving DecidableEq, Fintype, Repr

/-- All four Ω-objects are separate explicit pins; none is discharged by any other. -/
def omegaNormStatus : OmegaNorm → ResearchStatus
  | .sharedGcdOmegaH => .conditionalSourcePin
  | .plainL2Shell => .conditionalSourcePin
  | .perronNuclear => .conditionalSourcePin
  | .weightedDivisorMoment => .conditionalSourcePin

/-- **Ω firewall.**  There are exactly four Ω-objects and each is an explicit source pin. -/
theorem omega_norms_are_four_separate_pins :
    Fintype.card OmegaNorm = 4 ∧
      ∀ N : OmegaNorm, omegaNormStatus N = ResearchStatus.conditionalSourcePin := by
  decide +kernel

/-! ## §6  Coverage scopes and Type-II names -/

/-- The scope of a coverage percentage.  A bare percentage without one of these labels is
inadmissible. -/
inductive CoverageScope
  /-- Coverage inside a single packet. -/
  | packet
  /-- Coverage inside one branch. -/
  | branch
  /-- Coverage of the whole transverse face. -/
  | transverseFace
  /-- Coverage of the whole problem. -/
  | global
  deriving DecidableEq, Fintype, Repr

/-- Global coverage is not implied by branch coverage; the two scopes are distinct labels
(the mathematical version of this guard is
`Erdos287.SemanticFirewalls.branch_coverage_not_global`). -/
theorem coverage_scopes_distinct :
    (CoverageScope.branch) ≠ CoverageScope.global ∧
      (CoverageScope.packet) ≠ CoverageScope.transverseFace := by
  decide +kernel

/-- Three different decompositions have been called "Type II". -/
inductive TypeIIName
  /-- The 287-local double Type-II split. -/
  | doubleTypeII287
  /-- The Möbius-level Type-II split. -/
  | mobiusLevelTypeII
  /-- The classical bilinear Type-II range of the literature. -/
  | classicalBilinearTypeII
  deriving DecidableEq, Fintype, Repr

/-- Statuses of the three Type-II objects. -/
def typeIIStatus : TypeIIName → ResearchStatus
  | .doubleTypeII287 => .analyticBanked
  | .mobiusLevelTypeII => .open_
  | .classicalBilinearTypeII => .conditionalSourcePin

/-- **Type-II firewall.**  The three Type-II objects carry three different statuses; the banked
287-local double Type-II must never be quoted for the open Möbius-level Type-II. -/
theorem typeII_names_have_distinct_status :
    typeIIStatus .doubleTypeII287 ≠ typeIIStatus .mobiusLevelTypeII ∧
      typeIIStatus .mobiusLevelTypeII ≠ typeIIStatus .classicalBilinearTypeII := by
  decide +kernel

/-! ## §7  Classification of `WindowPairSupply` -/

/-- Classification of an end-to-end input. -/
inductive InputClass
  /-- A legacy object kept for history. -/
  | legacy
  /-- An alternative *sufficient* end-to-end compiler input, not a proved statement. -/
  | alternativeSufficientCompilerInput
  /-- A kernel-proved theorem. -/
  | provedTheorem
  deriving DecidableEq, Fintype, Repr

/-- `WindowPairSupply` is a **sufficient compiler input**, not a proved statement: the closure
theorem `no_Erdos287Counterexample_of_closure` consumes it as a hypothesis. -/
def windowPairSupplyClass : InputClass := .alternativeSufficientCompilerInput

/-- **Firewall.**  `WindowPairSupply` is not classified as a proved theorem. -/
theorem windowPairSupply_is_not_proved :
    windowPairSupplyClass ≠ InputClass.provedTheorem := by decide +kernel

/-! ## §8  Frontier DAG -/

/-- Nodes of the frontier dependency graph. -/
inductive FrontierNode
  /-- C0 face. -/
  | c0
  /-- Exact product collision. -/
  | exactProductCollision
  /-- Transverse one-conductor reciprocity. -/
  | oneConductor
  /-- `q_C` unitary Fourier. -/
  | qCUnitary
  /-- Bézout three-axis. -/
  | bezoutThreeAxis
  /-- Dual-level reciprocity. -/
  | dualLevelReciprocity
  /-- Dual pairwise Fourier. -/
  | dualPairwiseFourier
  /-- Affine-product energy. -/
  | affineProductEnergy
  /-- The current first analytic residual. -/
  | simultaneousCriticalMobius
  /-- The b-diagonal face. -/
  | bDiagonal
  /-- Erdős #287 itself. -/
  | erdos287
  deriving DecidableEq, Fintype, Repr

/-- Authoritative status of each frontier node. -/
def frontierStatus : FrontierNode → ResearchStatus
  | .c0 => .conditionalSourcePin
  | .exactProductCollision => .analyticBanked
  | .oneConductor => .analyticBanked
  | .qCUnitary => .analyticBanked
  | .bezoutThreeAxis => .analyticBanked
  | .dualLevelReciprocity => .analyticBanked
  | .dualPairwiseFourier => .analyticBanked
  | .affineProductEnergy => .conditionalSourcePin
  | .simultaneousCriticalMobius => .open_
  | .bDiagonal => .open_
  | .erdos287 => .open_

/-- Edges of the frontier DAG: `dependsOn a b` means closing `a` requires `b`. -/
def dependsOn : FrontierNode → FrontierNode → Bool
  | .erdos287, .c0 => true
  | .erdos287, .simultaneousCriticalMobius => true
  | .erdos287, .bDiagonal => true
  | .simultaneousCriticalMobius, .affineProductEnergy => true
  | .simultaneousCriticalMobius, .dualPairwiseFourier => true
  | .simultaneousCriticalMobius, .dualLevelReciprocity => true
  | .dualLevelReciprocity, .bezoutThreeAxis => true
  | .bezoutThreeAxis, .oneConductor => true
  | .oneConductor, .qCUnitary => true
  | _, _ => false

/-- **Frontier firewall.**  Erdős #287 depends on three still-unclosed nodes, and every node it
depends on is `open_` or a `conditionalSourcePin`. -/
theorem erdos287_depends_on_open_nodes :
    (∀ n : FrontierNode, dependsOn .erdos287 n = true →
        frontierStatus n = ResearchStatus.open_ ∨
          frontierStatus n = ResearchStatus.conditionalSourcePin) ∧
      frontierStatus .erdos287 = ResearchStatus.open_ := by
  decide +kernel

/-- The dependency relation is irreflexive (no node depends on itself). -/
theorem dependsOn_irrefl : ∀ n : FrontierNode, dependsOn n n = false := by decide +kernel

/-! ## §9  Retraction ledger -/

/-- Objects that were retracted or superseded, with the reason recorded as a constructor. -/
inductive RetractionEntry
  /-- The naive full-CRT DFT route: retracted (structurally wrong). -/
  | naiveFullCrtDft
  /-- Cross-packet two-axis: retracted (separable phases, no mixed inverse term). -/
  | crossPacketTwoAxis
  /-- Single-carrier Bézout-numerator frontier: superseded, content preserved. -/
  | singleCarrierFrontier
  /-- Ultra-near critical-density Möbius-level frontier: strictly reduced, content preserved. -/
  | ultraNearCriticalDensity
  /-- Old scale-saturation face: superseded by the reciprocal-density duality. -/
  | oldScaleSaturation
  deriving DecidableEq, Fintype, Repr

/-- Status recorded for each retraction-ledger entry. -/
def retractionStatus : RetractionEntry → ResearchStatus
  | .naiveFullCrtDft => .retracted
  | .crossPacketTwoAxis => .retracted
  | .singleCarrierFrontier => .superseded
  | .ultraNearCriticalDensity => .strictReduction
  | .oldScaleSaturation => .superseded

/-- **Retraction firewall.**  No retracted or superseded entry is labelled `kernelProved`, and
no superseded entry is labelled `retracted` (superseding does not falsify). -/
theorem retraction_ledger_wellformed :
    (∀ e : RetractionEntry, retractionStatus e ≠ ResearchStatus.kernelProved) ∧
      retractionStatus .singleCarrierFrontier ≠ ResearchStatus.retracted ∧
      retractionStatus .ultraNearCriticalDensity ≠ ResearchStatus.retracted := by
  decide +kernel

/-! ## §10  Resource, constant-selection and source-normalisation ledgers -/

/-- A resource that may be spent at most once in a packet argument. -/
inductive Resource
  /-- The `Δ`-axis saving. -/
  | deltaAxis
  /-- The `ℓ`-axis saving. -/
  | ellAxis
  /-- The `q`/`r₀`-axis saving. -/
  | qAxis
  /-- The Möbius cancellation (currently unavailable). -/
  | mobiusCancellation
  /-- The C0 gain (reserved for the C0 face). -/
  | c0Gain
  deriving DecidableEq, Fintype, Repr

/-- Whether a resource is currently available to the transverse argument. -/
def resourceAvailable : Resource → Bool
  | .deltaAxis => true
  | .ellAxis => true
  | .qAxis => true
  | .mobiusCancellation => false
  | .c0Gain => false

/-- **No-double-spending ledger.**  Exactly three axis resources are available; Möbius
cancellation is *not* available and the C0 gain is reserved and may not be reused transversally
(the quantitative form of the firewall is
`Erdos287.TransverseDualPairwise.dualPairwise_min_bound`). -/
theorem resource_ledger :
    resourceAvailable .mobiusCancellation = false ∧
      resourceAvailable .c0Gain = false ∧
      (Finset.univ.filter (fun r : Resource => resourceAvailable r = true)).card = 3 := by
  decide +kernel

/-- Inputs that must be *chosen* (constants and margins) before any closure claim. -/
inductive ConstantSelection
  /-- The energy constant `K_energy` of the affine-product interface. -/
  | kEnergy
  /-- The grouped-`q` product-energy constant. -/
  | kGroupedQ
  /-- The large-`g` router threshold `G₀`. -/
  | g0Threshold
  /-- The large-`Ξ`-gcd router threshold. -/
  | xiGcdThreshold
  /-- The source-length margin. -/
  | sourceLengthMargin
  deriving DecidableEq, Fintype, Repr

/-- No constant has been fixed: each remains an explicit parameter. -/
def constantFixed : ConstantSelection → Bool := fun _ => false

/-- **Constant-selection ledger.**  Five constants remain free parameters; none is hard-coded in
any Lean theorem of the bank. -/
theorem constants_all_free :
    (∀ c : ConstantSelection, constantFixed c = false) ∧
      Fintype.card ConstantSelection = 5 := by
  decide +kernel

/-- Stages of the source-normalisation DAG. -/
inductive SourceNormalisationStage
  /-- Physical source definition. -/
  | physicalSource
  /-- Perron / nuclear normalisation. -/
  | perronNuclear
  /-- Shared-gcd `Ω_H` normalisation. -/
  | sharedGcdOmegaH
  /-- Weighted Ω divisor-moment norm. -/
  | weightedDivisorMoment
  /-- Formal Lean coefficient vectors. -/
  | formalCoefficients
  deriving DecidableEq, Fintype, Repr

/-- Which normalisation stages are formally available in Lean. -/
def stageFormallyAvailable : SourceNormalisationStage → Bool
  | .formalCoefficients => true
  | _ => false

/-- **Source-normalisation ledger.**  Only the abstract coefficient vectors are formally
available; every physical stage remains an explicit pin. -/
theorem source_normalisation_ledger :
    (Finset.univ.filter
        (fun s : SourceNormalisationStage => stageFormallyAvailable s = true)).card = 1 ∧
      stageFormallyAvailable .physicalSource = false ∧
      stageFormallyAvailable .weightedDivisorMoment = false := by
  decide +kernel

/-! ## §11  Risk classification `S0`–`S6` -/

/-- Severity classes for semantic-drift risks. -/
inductive RiskClass
  /-- S0: no risk, kernel-checked. -/
  | S0
  /-- S1: harmless wording. -/
  | S1
  /-- S2: ambiguous symbol, guarded. -/
  | S2
  /-- S3: object-role conflation risk. -/
  | S3
  /-- S4: scope inflation risk (branch vs global). -/
  | S4
  /-- S5: status inflation risk (analytic vs kernel). -/
  | S5
  /-- S6: closure overclaim risk. -/
  | S6
  deriving DecidableEq, Fintype, Repr

/-- The audited risk items. -/
inductive RiskItem
  /-- Bare symbol `q` in prose. -/
  | bareQ
  /-- `x` versus `X`. -/
  | xVersusBigX
  /-- Bare coverage percentage. -/
  | bareCoverage
  /-- "C0 closed" without a level label. -/
  | c0ClosedUnqualified
  /-- "Type II closed" without naming which Type II. -/
  | typeIIUnqualified
  /-- `Gap2CE` result quoted as a result about the problem. -/
  | gap2CEQuotedAsProblem
  /-- `WindowPairSupply` quoted as proved. -/
  | windowPairSupplyQuotedAsProved
  /-- Analytic research `PASS` quoted as kernel-proved. -/
  | analyticPassQuotedAsKernel
  /-- Alternative bounds multiplied instead of minimised. -/
  | boundsMultiplied
  /-- Möbius cancellation assumed. -/
  | mobiusAssumed
  /-- Literature theorem quoted as closing the global residual. -/
  | literatureQuotedAsClosure
  deriving DecidableEq, Fintype, Repr

/-- Severity assigned to each audited risk item. -/
def riskClass : RiskItem → RiskClass
  | .bareQ => .S2
  | .xVersusBigX => .S2
  | .bareCoverage => .S4
  | .c0ClosedUnqualified => .S5
  | .typeIIUnqualified => .S3
  | .gap2CEQuotedAsProblem => .S3
  | .windowPairSupplyQuotedAsProved => .S5
  | .analyticPassQuotedAsKernel => .S5
  | .boundsMultiplied => .S6
  | .mobiusAssumed => .S6
  | .literatureQuotedAsClosure => .S6

/-- Whether the repository currently carries a kernel-checked guard against the item. -/
def riskGuarded : RiskItem → Bool := fun _ => true

/-- **Risk ledger.**  Exact counts of the audited items by severity class, and the statement that
each audited item has a guard in the bank. -/
theorem risk_counts :
    (Finset.univ.filter (fun i : RiskItem => riskClass i = RiskClass.S2)).card = 2 ∧
      (Finset.univ.filter (fun i : RiskItem => riskClass i = RiskClass.S3)).card = 2 ∧
      (Finset.univ.filter (fun i : RiskItem => riskClass i = RiskClass.S4)).card = 1 ∧
      (Finset.univ.filter (fun i : RiskItem => riskClass i = RiskClass.S5)).card = 3 ∧
      (Finset.univ.filter (fun i : RiskItem => riskClass i = RiskClass.S6)).card = 3 ∧
      (∀ i : RiskItem, riskGuarded i = true) := by
  decide +kernel

/-! ## §12  Critical pre-closure blockers -/

/-- The blockers that must be discharged before any closure claim may be made. -/
inductive PreClosureBlocker
  /-- The simultaneous-critical dual-level affine-product Möbius residual. -/
  | simultaneousCriticalMobius
  /-- The b-diagonal surviving-vertex rectangle. -/
  | bDiagonalRect
  /-- The formal source normalisation (C0 physical level). -/
  | formalSourceNormalisation
  /-- The affine-product modular energy (Cochrane–Shi type). -/
  | affineProductEnergy
  /-- The weighted Ω divisor-moment norm. -/
  | weightedOmegaNorm
  deriving DecidableEq, Fintype, Repr

/-- No blocker is discharged. -/
def blockerDischarged : PreClosureBlocker → Bool := fun _ => false

/-- **Closure firewall.**  Five blockers remain, none discharged; therefore no closure claim is
admissible and Erdős #287 is recorded as `open_`. -/
theorem preClosure_blockers_remain :
    Fintype.card PreClosureBlocker = 5 ∧
      (∀ b : PreClosureBlocker, blockerDischarged b = false) ∧
      frontierStatus .erdos287 = ResearchStatus.open_ := by
  decide +kernel

end AuthoritativeStatus
end Erdos287
