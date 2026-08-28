import Mathlib
import RequestProject.Erdos287.PrePoissonDensity3221
import RequestProject.Erdos287.HighConductorVariance3221
import RequestProject.Erdos287.CharacterGram3221
import RequestProject.Erdos287.BalancedSevenV19Compiler
import RequestProject.Status.Erdos287V18Status

/-!
# Erdős #287 — V19 status: pre-Poisson divisor density / high-conductor variance

**ERDŐS #287 REMAINS OPEN.**  Nothing in V19 proves it, nor Balanced7, nor the factorial
signed endpoint, nor the comparison match, nor the inverse-sampled high-conductor
logarithmic variance bound.  No `axiom` was added and no analytic or source interface is
inhabited anywhere.

## 0. Regression guard

Baseline build located and reused, unchanged, before any edit:
`FactorialEulerPolarization.lean`, `FactorialEulerLocal.lean`,
`FactorialPolarizationLinearity.lean`, `PascadiParameterLedger.lean`,
`NormalForm3221.lean`, `MovingPhaseProvider3221.lean`,
`FactorialEndpoint3221Adapter.lean`, `Erdos287V18Status.lean`, and the whole V17 3221
finite/exponent bank (`Exponent3221Ledger`, `BalancedSeven3221Grouping`,
`SourceAssistedDiagonal3221`, `OffDiagonal3221`, `EHNoWrap3221`,
`DIKuznetsov3221Interface`, `BalancedSeven3221Compiler`).  No existing theorem was
restated under a new name, weakened, renamed or deleted; V19 is append-only apart from five
import lines in `RequestProject/Main.lean`.

## 1. Frontier repair (Phase A)

The V18 record

```
LITERAL 3221 NORMAL FORM : SOURCE_BLOCKED
SMALL-Z RANGE ADAPTER    : CONDITIONAL
LEVELWISE LARGE-RANGE    : OPEN_ANALYTIC
```

is **not deleted and not declared false**.  It is marked *superseded as the controlling
frontier*, because the physical source has since been reconstructed before
Poisson/completion.  Concretely:

* `V18_NORMALFORM_SMALLZ` — `HISTORICAL / SUPERSEDED AS CONTROLLING FRONTIER`;
* `3221-DI-NORMALFORM45` — `SOURCE_MISMATCH` for the reconstructed physical route;
* `PASCADI101-LEVELWISE-PHASE-SMALLZ45` — `CONDITIONAL PROVIDER METADATA, NOT CURRENTLY
  REQUIRED`;
* `3221-SPARSE-RECIPROCAL-KF-DICTIONARY45` — `RETIRED AS CURRENT ROUTE`.

**These are metadata labels only.**  No analytic falsity is derived from them anywhere: the
ledger below is a function on a finite index type, and no theorem in this repository
converts a ledger value into a mathematical claim.  The V18 declarations remain in the
build, sorry-free and unchanged.

The current controlling node is `3221-INVERSE-SAMPLED-HIGHCOND-LOGVAR45`.

## 2. What V19 adds (all sorry-free, kernel-checked)

* **Pre-Poisson affine divisor identity** (`PrePoissonDensity3221.lean`):
  `affineResidue_iff_dvd_two_mul_add`, `balancedSeven_affine_divisor_condition`,
  `exists_affineResidue`.
* **Pre-Poisson divisor density**: `sampled_q_card_le_divisorCount`,
  `sampled_q_card_le_divisorCount_affine`; the asymptotic divisor bound is *not* proved and
  is isolated as the uninhabited `DivisorGrowthInput`.
* **Second-copy density**: `secondCopy_shell_iff`, `congruence_interval_card_le`,
  `congruence_interval_card_le_one_add_quotient`,
  `secondCopy_card_le_one_add_quotient` — exact `ℤ` interval arithmetic, no real intervals.
* **Finite density compiler**: `sampledQuadBox_card_le`, with no `X`-exponent inside.
* **Exponent ledger** (reusing `Erdos287.Ledger3221` unchanged):
  `prePoisson_density_exponent = 39/35`, `cauchy_prefactor_exponent = 31/35`,
  `highCond_naturalScale_exponent = 39/35`, `naturalScale_matches_density`, plus the two
  retired-lane rational audits `BC3221_capacity_deficit_arithmetic`,
  `DRZ3221_capacity_deficit_arithmetic` (metadata only — **no external theorem is
  formalised, assumed or axiomatised**).
* **First Cauchy / `μ`-sign consumption** (`HighConductorVariance3221.lean`):
  `firstCauchy_sign_consumption`, `postCauchy_weight_sign_invariant`,
  `moebius_sq_of_squarefree`, and the firewall `firstCauchy_loses_sign_information`.
* **RR/RK/KK reassembly**: `normSq_sub_reassembly`,
  `highConductorEnergy_reassembles_crossTerms` — `PROVED_ALGEBRAIC` only; the physical
  comparison term is **not** thereby matched.
* **High-conductor residue object and socket**: `residueSum`,
  `residueSum_sum_over_classes`, the pure-data `InverseSampledHighCond3221Data` (no free
  `Prop` field), its energy `Vhi`, and the load-bearing identification
  `samplePoint_iff_affineSampled` between the inverse sampling point `−s(2m)⁻¹` and the
  Phase-B divisibility `q ∣ 2mw + s`.
* **The open analytic input**: `InverseSampledHighCondLogVar3221Input`, uninhabited, with
  an explicit positive saving parameter `Lsave`, plus `highCondLogVar_not_automatic`.
* **Character expansion** (`CharacterGram3221.lean`): Dirichlet-character infrastructure
  *is* available, so the low/high conductor projection is defined literally and
  `residueSum_eq_cLow_add_cHigh` is **proved**, together with the orthogonality expansion
  `totient_mul_residueSum_eq_sum_char`, the exact Gram identities `gram_expansion`,
  `highResidue_energy_gram`, `inverseSampled_highResidue_gram`, and the five-box/two-box
  factorisations `cHat_fiveBox_factorisation`, `cHat_twoBox_factorisation`.  **No
  character-sum bound is proved or assumed.**
* **The conditional compiler** (`BalancedSevenV19Compiler.lean`):
  `cauchyPrefactor_of_firstCauchy` (the certificate is genuinely produced by Cauchy, not
  postulated), `highCond_source_bound_of_logVar`, `highCond_source_abs_bound`,
  `factorialEndpoint_of_highCondLogVar`, `balancedSeven_of_highCondLogVar`, with the
  logarithmic budget explicit and the comparison channel independent
  (`comparison_stays_independent`), plus `balancedSeven_not_automatic` and
  `cauchyPrefactor_not_automatic`.

## 3. Final V19 ledger

```
FACTORIAL EULER                    : PROVED_ALGEBRAIC / LEAN_PROVED   (V16, unchanged)
EXPECTED-TERM LINEARITY            : PROVED_ALGEBRAIC / LEAN_PROVED   (V16, unchanged)
3221 GROUPING                      : PROVED_FINITE                    (V17, unchanged)
PRE-POISSON AFFINE DIVISOR IDENTITY: LEAN_PROVED
FIRST CAUCHY SIGN CONSUMPTION      : LEAN_PROVED / PROVED_ALGEBRAIC
RR/RK/KK REASSEMBLY                : LEAN_PROVED / PROVED_ALGEBRAIC
PRE-POISSON DIVISOR DENSITY        : LEAN_PROVED FINITE (+ separate divisor-growth input)
NATURAL-SCALE 39/35 LEDGER         : PROVED_ALGEBRAIC / CAPACITY_ONLY
V18 DI/SMALL-Z ROUTE               : SUPERSEDED AS CONTROLLING FRONTIER
KLOOSTERMAN-FRACTION BLACKBOX      : RETIRED / EXTERNAL CAPACITY AUDITED
INVERSE-SAMPLED HIGHCOND LOGVAR    : OPEN_ANALYTIC
CHARACTER GRAM EXPANSION           : PROVED_FINITE
COMPARISON                         : SOURCE_OPEN
BALANCED7                          : OPEN
FCL                                : OPEN
WINDOWPAIRSUPPLY                   : OPEN
ERDOS287                           : OPEN
```
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace V19Status

/-! ## The machine-readable V19 ledger

This is **metadata**: a function on a finite index type.  No theorem in this repository
converts a ledger value into a mathematical claim, and in particular no analytic falsity is
derived from any label below. -/

/-- The V19 status nodes. -/
inductive Node
  | v18NormalFormSmallZ
  | diNormalForm3221
  | pascadiLevelwisePhaseSmallZ
  | sparseReciprocalKFDictionary
  | factorialEuler
  | expectedTermLinearity
  | grouping3221
  | prePoissonAffineDivisor
  | firstCauchySignConsumption
  | rrrkkkReassembly
  | prePoissonDivisorDensity
  | naturalScaleLedger
  | inverseSampledHighCondLogVar
  | characterGramExpansion
  | comparison
  | balancedSeven
  | fcl
  | windowPairSupply
  | erdos287
  deriving DecidableEq, Fintype, Repr

/-- The V19 status labels. -/
inductive Label
  | historicalSuperseded
  | sourceMismatch
  | conditionalProviderMetadata
  | retiredExternalCapacityAudited
  | leanProved
  | provedFinite
  | provedAlgebraicCapacityOnly
  | openAnalytic
  | sourceOpen
  | openNode
  deriving DecidableEq, Fintype, Repr

open Node Label

/-- The V19 ledger. -/
def ledger : Node → Label
  | v18NormalFormSmallZ => historicalSuperseded
  | diNormalForm3221 => sourceMismatch
  | pascadiLevelwisePhaseSmallZ => conditionalProviderMetadata
  | sparseReciprocalKFDictionary => retiredExternalCapacityAudited
  | factorialEuler => leanProved
  | expectedTermLinearity => leanProved
  | grouping3221 => provedFinite
  | prePoissonAffineDivisor => leanProved
  | firstCauchySignConsumption => leanProved
  | rrrkkkReassembly => leanProved
  | prePoissonDivisorDensity => provedFinite
  | naturalScaleLedger => provedAlgebraicCapacityOnly
  | inverseSampledHighCondLogVar => openAnalytic
  | characterGramExpansion => provedFinite
  | comparison => sourceOpen
  | balancedSeven => openNode
  | fcl => openNode
  | windowPairSupply => openNode
  | erdos287 => openNode

/-- **The controlling analytic frontier is unique.**  `3221-INVERSE-SAMPLED-HIGHCOND-LOGVAR45`
is the *only* node carrying `OPEN_ANALYTIC`. -/
theorem controlling_analytic_node_unique (n : Node) :
    ledger n = openAnalytic ↔ n = inverseSampledHighCondLogVar := by
  revert n
  decide +kernel

/-- The V18 DI/small-`Z` route is recorded as *superseded as controlling frontier*, which is
distinct from every "proved" and from every "open" label: no falsity is asserted. -/
theorem v18_route_superseded_not_refuted :
    ledger v18NormalFormSmallZ = historicalSuperseded ∧
      historicalSuperseded ≠ openNode ∧ historicalSuperseded ≠ leanProved ∧
      historicalSuperseded ≠ openAnalytic := by
  decide +kernel

/-- The retired Kloosterman-fraction dictionary carries the `RETIRED / EXTERNAL CAPACITY
AUDITED` label, again distinct from any claim of falsity. -/
theorem kloostermanFraction_retired :
    ledger sparseReciprocalKFDictionary = retiredExternalCapacityAudited := by
  decide +kernel

/-- The four terminal nodes stay open. -/
theorem terminal_nodes_open :
    ledger balancedSeven = openNode ∧ ledger fcl = openNode ∧
      ledger windowPairSupply = openNode ∧ ledger erdos287 = openNode := by
  decide +kernel

/-- The comparison node is `SOURCE_OPEN` and is *not* proved. -/
theorem comparison_source_open :
    ledger comparison = sourceOpen ∧ sourceOpen ≠ leanProved := by
  decide +kernel

/-! ## Axiom audit for the principal new theorems -/

section AxiomAudit

-- Phase B/E/F: pre-Poisson affine divisor identity and density
#print axioms Erdos287.PrePoisson3221.isCoprime_two_of_odd
#print axioms Erdos287.PrePoisson3221.affineResidue_iff_dvd_two_mul_add
#print axioms Erdos287.PrePoisson3221.balancedSeven_affine_divisor_condition
#print axioms Erdos287.PrePoisson3221.exists_affineResidue
#print axioms Erdos287.PrePoisson3221.sampled_q_card_le_divisorCount
#print axioms Erdos287.PrePoisson3221.sampled_q_card_le_divisorCount_affine
#print axioms Erdos287.PrePoisson3221.secondCopy_shell_iff
#print axioms Erdos287.PrePoisson3221.congruence_interval_card_le
#print axioms Erdos287.PrePoisson3221.congruence_interval_card_le_one_add_quotient
#print axioms Erdos287.PrePoisson3221.secondCopy_card_le_one_add_quotient
#print axioms Erdos287.PrePoisson3221.sampledQuadBox_card_le
#print axioms Erdos287.PrePoisson3221.prePoisson_density_exponent
#print axioms Erdos287.PrePoisson3221.cauchy_prefactor_exponent
#print axioms Erdos287.PrePoisson3221.highCond_naturalScale_exponent
#print axioms Erdos287.PrePoisson3221.naturalScale_matches_density
#print axioms Erdos287.PrePoisson3221.BC3221_capacity_deficit_arithmetic
#print axioms Erdos287.PrePoisson3221.DRZ3221_capacity_deficit_arithmetic
#print axioms Erdos287.PrePoisson3221.prePoisson_grouping_product

-- Phase C/D/G: first Cauchy, residue object, reassembly, socket
#print axioms Erdos287.HighCond3221.firstCauchy_sign_consumption
#print axioms Erdos287.HighCond3221.postCauchy_weight_sign_invariant
#print axioms Erdos287.HighCond3221.firstCauchy_loses_sign_information
#print axioms Erdos287.HighCond3221.residueSum_sum_over_classes
#print axioms Erdos287.HighCond3221.normSq_sub_reassembly
#print axioms Erdos287.HighCond3221.highConductorEnergy_reassembles_crossTerms
#print axioms Erdos287.HighCond3221.InverseSampledHighCond3221Data.samplePoint_iff_affineSampled
#print axioms Erdos287.HighCond3221.InverseSampledHighCond3221Data.Vhi_nonneg
#print axioms Erdos287.HighCond3221.probeData_Vhi
#print axioms Erdos287.HighCond3221.highCondLogVar_not_automatic

-- Phase H: character orthogonality, projection, Gram, five-box
#print axioms Erdos287.CharGram3221.totient_mul_residueSum_eq_sum_char
#print axioms Erdos287.CharGram3221.residueSum_eq_cLow_add_cHigh
#print axioms Erdos287.CharGram3221.gram_expansion
#print axioms Erdos287.CharGram3221.highResidue_energy_gram
#print axioms Erdos287.CharGram3221.inverseSampled_highResidue_gram
#print axioms Erdos287.CharGram3221.sum_mul_sum4
#print axioms Erdos287.CharGram3221.cHat_twoBox_factorisation
#print axioms Erdos287.CharGram3221.cHat_fiveBox_factorisation

-- Phase I: the conditional compiler and its firewalls
#print axioms Erdos287.V19Compiler.cauchyPrefactor_of_firstCauchy
#print axioms Erdos287.V19Compiler.highCond_source_bound_of_logVar
#print axioms Erdos287.V19Compiler.highCond_source_abs_bound
#print axioms Erdos287.V19Compiler.factorialEndpoint_of_highCondLogVar
#print axioms Erdos287.V19Compiler.balancedSeven_of_highCondLogVar
#print axioms Erdos287.V19Compiler.balancedSeven_not_automatic
#print axioms Erdos287.V19Compiler.cauchyPrefactor_not_automatic
#print axioms Erdos287.V19Compiler.comparison_stays_independent

-- The ledger itself
#print axioms Erdos287.V19Status.controlling_analytic_node_unique
#print axioms Erdos287.V19Status.v18_route_superseded_not_refuted
#print axioms Erdos287.V19Status.terminal_nodes_open

end AxiomAudit

end V19Status
end Erdos287
