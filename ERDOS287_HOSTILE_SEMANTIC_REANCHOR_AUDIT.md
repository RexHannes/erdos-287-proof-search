# ERDŐS #287 — HOSTILE SEMANTIC RE-ANCHORING AUDIT

Append-only hygiene layer. **No new analytic claim** is made anywhere in this layer; every
declaration it adds is either a kernel-checked countermodel/guard or a decidable metadata fact.

---

## FILES ADDED

```
RequestProject/Status/SemanticFirewallsErdos287.lean
RequestProject/Status/CurrentAuthoritativeStatusErdos287.lean
RequestProject/Status/AxiomAuditErdos287SemanticReanchor.lean
ERDOS287_HOSTILE_SEMANTIC_REANCHOR_AUDIT.md   (this file)
```

## FILES MODIFIED

```
RequestProject/Main.lean   — three appended `import` lines only.
```

## FILES DELETED

```
none
```

No previous declaration was deleted, renamed, weakened, relocated or restated.

---

## 1. AUTHORITATIVE STATUS AND PRECEDENCE

`Erdos287.AuthoritativeStatus` records the six chronological status layers
(`vSeries`, `balancedSeven`, `c0UnitaryFourier`, `transverseCarrier`, `oneConductor`,
`dualLevelSimultaneousCritical`) with a numerical index, and fixes the precedence rule:

* `authoritativeLayer = dualLevelSimultaneousCritical`;
* `authoritative_layer_is_latest` — no layer is later;
* `layerIndex_injective` — the layers are distinct.

Where two layers disagree about a **label**, the later layer governs; the earlier layer is
preserved as history and is never rewritten.

## 2. SEMANTIC OBJECT LEDGER

`SemanticObject` (17 audited symbols) with `objectRole : SemanticObject → ObjectRole` assigns each
recurring symbol exactly one role among `modulus`, `scale`, `sourceNorm`, `problemPredicate`,
`compilerInput`, `metadataLabel`:

| symbol | role |
|---|---|
| `q` (bare) | modulus — inadmissible without a `q`-role label (§3) |
| `Q` | scale (range of the `q`-axis) |
| `q_eff` | modulus (after conductor reduction) |
| `x` | scale (small) |
| `X` | scale (global) |
| `E*` | modulus |
| `Omega_H` | source norm |
| `b*` | source norm |
| Type I / Type II | metadata labels |
| C0 / transverse / b-diagonal faces | metadata labels |
| coverage | metadata label |
| `WindowPairSupply` | compiler input |
| `Gap2CE` | problem predicate (relaxed) |
| `Erdos287Statement` | problem predicate (exact) |

Guards: `modulus_is_not_scale`, `smallX_ne_bigX`, `gap2CE_ne_statement`.

## 3. `q`-ROLE SPLIT

`Erdos287.SemanticFirewalls.QRole` has exactly four constructors
(`qSwitch`, `qLocal`, `qEff`, `qTransverse`), proved pairwise distinct
(`qRoles_pairwise_distinct`, `qRole_card = 4`), with the scoped alias table `qRoleName` and
`qRoleName_distinct`. The bare symbol `q` is inadmissible in a status claim.

## 4. POINTWISE vs AGGREGATE FIREWALL

`pointwise_not_aggregate` and `aggregate_not_pointwise` are explicit two-point countermodels:
neither form of bound implies the other with the same constant.

## 5. x / X FIREWALL

`smallX_bound_does_not_transfer` : a bound valid at a small scale need not hold at a large scale
(explicit witness). Together with `smallX_ne_bigX` this bans identification of the two symbols.

## 6. COVERAGE SCOPE LABELS

`CoverageScope` = `packet | branch | transverseFace | global`, with `coverage_scopes_distinct`,
and the mathematical guard `branch_coverage_not_global` (full coverage of one branch is not full
coverage of the union). **A bare "100 %" is banned**: every coverage figure must carry a scope
label.

## 7. THREE-LEVEL C0 SPLIT

`C0Level` = `finiteKernel | analyticEstimate | physicalSource`, with
`c0LevelStatus = kernelProved | analyticBanked | conditionalSourcePin` and
`c0_levels_have_distinct_status`. "C0 is closed" is not well-formed without a level label; the
physical level remains a source pin.

## 8. FOUR-WAY Ω-NORM SPLIT

`OmegaNorm` = `sharedGcdOmegaH | plainL2Shell | perronNuclear | weightedDivisorMoment`;
`omega_norms_are_four_separate_pins` records four distinct objects, each a
`conditionalSourcePin`. The mathematical separation of the weighted divisor-moment norm from the
plain `L²` shell is `Erdos287.TransverseAffineProduct.omegaWeighted_not_implied_by_l2`.

## 9. TYPE-II NAMING SPLIT

`TypeIIName` = `doubleTypeII287 | mobiusLevelTypeII | classicalBilinearTypeII` with statuses
`analyticBanked | open_ | conditionalSourcePin` and `typeII_names_have_distinct_status`.
The banked 287-local double Type-II may never be quoted for the open Möbius-level Type-II.

## 10. `WindowPairSupply` CLASSIFICATION

`windowPairSupplyClass = alternativeSufficientCompilerInput`, with
`windowPairSupply_is_not_proved`. It is a **sufficient input consumed as a hypothesis** by the
closure theorem, not a proved statement.

## 11. `Gap2CE` ONE-WAY FIREWALL WITH COUNTERMODEL

* `singletonGap2CE` : the set `A = {1}` is a valid `Gap2CE` (reciprocals sum to 1; the gap
  condition is vacuous).
* `singleton_not_counterexample` : it is **not** an `Erdos287Counterexample`.
* `gap2CE_firewall` : the bridge runs one way only.

Consequence: results proved *about* `Gap2CE` objects concern a strictly larger class, and a
`Gap2CE` statement is never by itself a statement about Erdős #287.

## 12. FRONTIER DAG

`FrontierNode` (11 nodes) with `frontierStatus` and the dependency relation `dependsOn`.
`erdos287_depends_on_open_nodes` : every node #287 depends on is `open_` or a
`conditionalSourcePin`, and #287 itself is `open_`. `dependsOn_irrefl` : no self-dependency.

## 13. RETRACTION LEDGER

`RetractionEntry` with `retractionStatus`:

```
naiveFullCrtDft          retracted
crossPacketTwoAxis       retracted
singleCarrierFrontier    superseded      (content preserved, NOT false)
ultraNearCriticalDensity strictReduction (content preserved, NOT false)
oldScaleSaturation       superseded
```

`retraction_ledger_wellformed` : no retracted/superseded entry is `kernelProved`, and superseding
is not retraction.

## 14. RESOURCE / MARGIN LEDGER

`Resource` = `deltaAxis | ellAxis | qAxis | mobiusCancellation | c0Gain`.
`resource_ledger` : exactly **three** axis resources are available; Möbius cancellation is
**unavailable** and the C0 gain is reserved (not reusable transversally). The quantitative
no-double-spending statement is `Erdos287.TransverseDualPairwise.dualPairwise_min_bound`
(alternatives are minimised, never multiplied), with the countermodel
`dualPairwise_min_is_not_product`.

## 15. CONSTANT-SELECTION DAG

`ConstantSelection` = `kEnergy | kGroupedQ | g0Threshold | xiGcdThreshold | sourceLengthMargin`;
`constants_all_free` : all five remain free parameters, none hard-coded in any theorem.

## 16. SOURCE-NORMALISATION DAG

`SourceNormalisationStage` = `physicalSource | perronNuclear | sharedGcdOmegaH |
weightedDivisorMoment | formalCoefficients`; `source_normalisation_ledger` : exactly **one**
stage (the abstract coefficient vectors) is formally available in Lean; every physical stage
remains an explicit pin.

## 17. RISK CLASSIFICATION S0–S6

`RiskItem` (11 audited items) with `riskClass` and exact counts (`risk_counts`):

```
S0  0     (no unguarded item is risk-free by default)
S1  0
S2  2     bare `q`;  `x` versus `X`
S3  2     unqualified Type II;  Gap2CE quoted as the problem
S4  1     bare coverage percentage
S5  3     "C0 closed" unqualified;  WindowPairSupply quoted as proved;
          analytic PASS quoted as kernel-proved
S6  3     bounds multiplied;  Möbius cancellation assumed;
          literature quoted as closing the global residual
```

`riskGuarded` : every audited item now has a kernel-checked guard in the bank
(`risk_counts` includes `∀ i, riskGuarded i = true`).

## 18. CRITICAL PRE-CLOSURE BLOCKERS

`PreClosureBlocker` = simultaneous-critical Möbius residual, b-diagonal surviving-vertex
rectangle, formal source normalisation, affine-product modular energy, weighted Ω norm.
`preClosure_blockers_remain` : five blockers, **none discharged**, and #287 is `open_`.

## 19. README / PUBLICATION WORDING — PATCH PLAN (NOT APPLIED)

The following wording patterns are risk-carrying. The plan below *qualifies* claims; it never
weakens a proved statement, and no README text was rewritten by this layer.

| pattern | risk | suggested replacement |
|---|---|---|
| "C0 is closed" | S5 | "C0 is analytically closed **conditional on the formal source normalisation**" |
| "100 % coverage" | S4 | "100 % of *packet class X* (scope label)" |
| "Type II closed" | S3 | name which Type II (`287-local double Type II`) |
| "counterexample ruled out" from a `Gap2CE` lemma | S3 | say "ruled out for the relaxed `Gap2CE` class" |
| "`WindowPairSupply` gives the theorem" | S5 | "…**assuming** `WindowPairSupply`" |
| research "PASS" | S5 | "analytically banked (research level), not kernel-proved" |
| citing fixed-modulus literature as closing the residual | S6 | record as literature candidate only |

## 20. BUILD AND AXIOM AUDIT

```
Per-module builds:
    RequestProject.Status.SemanticFirewallsErdos287            PASS
    RequestProject.Status.CurrentAuthoritativeStatusErdos287   PASS
    RequestProject.Status.AxiomAuditErdos287SemanticReanchor   PASS

Default `lake build`:  Build completed successfully (8317 jobs), 0 errors.

Axiom audit (AxiomAuditErdos287SemanticReanchor):
    65 declarations audited
    41 depend on NO axioms
    remainder depend only on subsets of {propext, Classical.choice, Quot.sound}
    0 sorryAx, 0 custom axioms, 0 native_decide, 0 unsafe / opaque / implemented_by
```

## STRICT OUTPUT

```
SEMANTIC OBJECT LEDGER:        PRESENT
q-ROLE SPLIT:                  PRESENT (4 roles, pairwise distinct)
x / X FIREWALL:                PRESENT (countermodel)
POINTWISE vs AGGREGATE:        PRESENT (both directions countermodelled)
FINITE-THEOREM vs COMPILER:    PRESENT (status-label distinctness + conditional-hypothesis shells)
THREE-LEVEL C0 SPLIT:          PRESENT
FOUR-WAY Ω SPLIT:              PRESENT
COVERAGE SCOPE LABELS:         PRESENT (bare "100 %" banned)
TYPE-II NAMING SPLIT:          PRESENT
WindowPairSupply CLASS:        ALTERNATIVE SUFFICIENT COMPILER INPUT
Gap2CE FIREWALL:               PRESENT WITH COUNTERMODEL ({1})
FRONTIER DAG:                  PRESENT
RETRACTION LEDGER:             PRESENT (superseded ≠ false)
RESOURCE / MARGIN LEDGER:      PRESENT (3 axes available; Möbius and C0 unavailable)
CONSTANT-SELECTION DAG:        PRESENT (5 constants, all free)
SOURCE-NORMALISATION DAG:      PRESENT (1 of 5 stages formal)
SEMANTIC UNIT TESTS:           PRESENT (all kernel-checked)
RISK CLASSIFICATION:           S2:2  S3:2  S4:1  S5:3  S6:3   (all guarded)
PRE-CLOSURE BLOCKERS:          5, none discharged
NEW ANALYTIC CLAIMS:           NONE
EXISTING BANK:                 UNALTERED
BUILD:                         PASS — 8317 jobs, 0 errors
ERDOS287:                      OPEN
```

STOP.
