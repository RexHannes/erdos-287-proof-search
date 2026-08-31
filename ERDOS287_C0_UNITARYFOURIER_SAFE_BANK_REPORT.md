# ERDŐS #287 — C0 UNITARY-FOURIER SAFE BANK REPORT

> **Public synchronization note — 31 August 2026.** This is the supplied formal-bank report for the completed 8298-job Aristotle run. Its final “next exact transverse target” records the research state at the time of that formal run and is now **historical/superseded as the controlling research frontier** by `THREEFACTOR-TRANSVERSE-CRITICAL-BEZOUTNUMERATOR-SINGLECARRIER45`. No newer one-conductor Lean bank is inferred from the later research-only result. The named modules in this report depend on a larger formal dependency graph than is currently dependency-complete under public `RequestProject/Main.lean`; therefore the 8298-job result is reported as a supplied verified bank, not as a build already reproduced from current public main.

Append-only delta. No existing file was deleted, relocated, renamed, weakened or reinterpreted in the supplied Aristotle bank; its `RequestProject/Main.lean` received appended `import` lines only.

---

## FILES ADDED IN THE SUPPLIED FORMAL BANK

- `RequestProject/CurrentProgramme/Erdos287ReciprocalUnitaryFourier.lean`
- `RequestProject/CurrentProgramme/Erdos287BalancedBUnitaryFourierCompiler.lean`
- `RequestProject/CurrentProgramme/Erdos287AffineBilinearReciprocalNumerator.lean`
- `RequestProject/CurrentProgramme/Erdos287C0PhysicalNormalisationInterface.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseCarrierInterface.lean`
- `RequestProject/Status/CurrentStatusErdos287C0UnitaryFourier.lean`
- `RequestProject/Status/CurrentStatusErdos287TransverseCarrier.lean`
- `RequestProject/Status/AxiomAuditErdos287C0UnitaryFourier.lean`
- `ERDOS287_C0_UNITARYFOURIER_SAFE_BANK_REPORT.md`

Paths follow the formal project's conventions (`CurrentProgramme/` for mathematics, `Status/` for ledgers and axiom audits).

## FILES MODIFIED IN THE SUPPLIED FORMAL BANK

- `RequestProject/Main.lean` — eight appended `import` lines, nothing reordered or removed.

---

## NEW KERNEL THEOREMS — unconditional and `sorry`-free in the supplied bank

### `Erdos287.ReciprocalUnitaryFourier`

| name | statement |
|---|---|
| `norm_sum_mul_sq_le` | finite Cauchy–Schwarz over `ℂ` |
| `unitaryFourierKernel` | `F_C(y,z) = e_x(C y z)` (definition) |
| `unitaryFourierKernel_symm`, `unitaryFourierKernel_norm` | symmetry; `‖F_C(y,z)‖ = 1` |
| `unitaryFourier_mulConj_sum` | full Gram: `∑_z F_C(y,z) conj F_C(y',z) = x·[y=y']`, i.e. `F_C F_C^* = x I` |
| `unitaryFourier_column_energy` | `∑_y ‖∑_z B z F_C(y,z)‖² = x ∑_z ‖B z‖²` (exact) |
| `unitaryFourier_bilinear_bound` | `‖∑_{y,z} A y B z F_C(y,z)‖² ≤ x ‖A‖₂² ‖B‖₂²` |
| `unitaryFourier_finset_bilinear_bound` | same for arbitrary finite supports (zero extension) |
| `isUnit_zmod_inv`, `zmod_inv_inv_of_isUnit`, `zmod_inv_bijOn_units` | inversion permutation of the units |
| `reciprocalUnitaryFourier_bilinear_bound` | principal new theorem: `‖∑_{r,s unit} A r B s e_x(C r⁻¹ s⁻¹)‖² ≤ x ‖A‖₂² ‖B‖₂²` |
| `transverseTwoCarrierUnitaryFourier` | naming alias of the previous line for modulus `m`, unit `Gamma` |
| `unitaryFourier_mulConj_sum_composite` | explicit instance at composite modulus `x = 12`, `C = 5` |

### `Erdos287.BalancedBUnitaryFourier`

| name | statement |
|---|---|
| `norm_sum_sq_le_card` | `‖∑_{i∈s} f i‖² ≤ #s ∑_{i∈s} ‖f i‖²` |
| `residueAggregate` | aggregation of a coefficient sequence over one residue class |
| `residueAggregate_l2_le_maxFiber` | `∑_r ‖agg r‖² ≤ M ∑_n ‖A n‖²` for a uniform fibre bound `M` |
| `interval_residue_fibre_card_le` | interval of length `N` meets a class mod `x` in `≤ N/x + 1` points |
| `intervalResidueAggregate_l2_bound` | interval corollary of the aggregation inequality |
| `reciprocalPhase_fiberwise` | exact regrouping of a reciprocal-phase double sum by residues |
| `balancedReciprocalFourier_compiler` | `‖∑_{n,e} A n β e e_x(C n⁻¹ e⁻¹)‖² ≤ x M_N M_E E_A E_B` on unit support |
| `balancedFourier_contraction_identity` | `x(1+N/x)(1+E/x)/B = x/B + 1/E + 1/N + 1/x` when `B = N E` |
| `coprime_product_left / _middle / _right / _all` | nonunit firewall: each factor of `b = ℓ d e` coprime to `x` |
| `productConvolutionEnergy_not_automatic` | convolution-energy interface can fail |

### `Erdos287.AffineBilinearReciprocalNumerator`

`zmod_inv_mul_of_isUnit`, `affineNumerator_reciprocal_decomposition`, `affineBilinearNumerator_reciprocal_decomposition`, `affineNumerator_character_factorisation`, `affineBilinearNumerator_character_factorisation`, and `affineBilinear_rankOne_reduction`.

The key reciprocal decomposition is

```text
(B0+B1*S1+B2*S2+B3*S1*S2)(S1*S2)^(-1)
 = B0*S1^(-1)*S2^(-1) + B1*S2^(-1) + B2*S1^(-1) + B3.
```

### Interfaces with non-automaticity witnesses

`perronNuclearNormalisation_not_automatic`, `omegaHL2Normalisation_not_automatic`, `c0PhysicalNormalisation_not_automatic`, `c0PhysicalNormalisation_satisfiable`, `usableTwoCarrierPair_not_automatic`, `usableTwoCarrierPair_satisfiable`, `transverseCarrierCase_no_exhaustiveness_claimed`, status-ledger theorems, `inv_sqrt_comparison_not_automatic`, and `constant_order_acyclic`.

### Conditional compilers — explicit hypotheses only

- `Erdos287.BalancedBUnitaryFourier.threeCarrierReciprocalFourier_of_productEnergy` — hypothesis `ProductConvolutionEnergyHypothesis`.
- `Erdos287.C0PhysicalNormalisation.c0_balanced_branch_bound_of` — hypotheses include unit conditioned coefficient, unit carrier support, residue-fibre bounds, `ProductConvolutionEnergyHypothesis`, and `OmegaHL2NormalisationHypothesis`. Its conclusion is an explicit finite inequality, not a proposition named “C0 closed”.
- `Erdos287.C0PhysicalNormalisation.perronNuclear_total_of_normalisation` and `omegaHL2_of_pointwise_normalisation`.
- `Erdos287.TransverseCarrier.transverseTwoCarrier_bound_of_unitSupport` and `transverseTwoCarrier_bound_with_fibre_weights`.

## REUSED BANK

- `Erdos287.ConditionedInverseConv.OmegaHNormalizationHypothesis` and `omegaH_energy_of_normalization` are reused, not duplicated: the new `ℓ²` shell is derived from the existing pointwise shell by `omegaHL2_of_pointwise_normalisation`.
- The transverse two-carrier mechanism reuses `reciprocalUnitaryFourier_bilinear_bound` through an alias; there is no second proof.
- Earlier C0 source-lift and COMMON-x ledgers are re-checked and proved preserved (`sourceLift_ledger_still_preserved`, `c0_ledger_still_preserved`).

## RETRACTED ARCHITECTURE — not re-encoded in the supplied bank

- old post-conditioning index `n = j (u')⁻¹ mod x` — retracted;
- old wrap `1 + U U' / B` — retracted;
- the common raw factor `b u'` is cancelled before projective conditioning and is not reintroduced.

The conditioned Kloosterman kernel of the research source is `S(-a_ρ b_ρ⁻¹, j; x)`; the finite theorems of this delta are stated for the abstract reciprocal kernel `e_x(C r⁻¹ s⁻¹)` and are independent of that identification.

## C0 ANALYTIC STATUS RECORDED BY THE FORMAL BANK

```text
C0 ANALYTIC CORE:
    CLOSED.

C0 PHYSICAL/FORMAL NORMALISATION:
    OPEN SOURCE PIN.

Therefore:
    C0 ANALYTICALLY CLOSED
    CONDITIONAL ON FORMAL NORMALISATION.
```

The bare phrase “C0 CLOSED” is not a Lean theorem. No Lean theorem asserts analytic C0 closure.

## FORMAL SOURCE PINS

- `SHAREDGCD-OMEGAH-NORMALISATION-SOURCEPIN45` — represented by `OmegaHNormalizationHypothesis` (pointwise, pre-existing) and `OmegaHL2NormalisationHypothesis` (`ℓ²`, new). Never assumed automatically.
- complete Perron / nuclear normalisation — `PerronNuclearNormalisationHypothesis`. Never assumed and no constant is guessed.
- bundle: `C0PhysicalNormalisationData` / `C0PhysicalNormalisationHypothesis`, proved neither automatic nor contradictory.

## TRANSVERSE CONDITIONAL MECHANISM IN THIS FORMAL SNAPSHOT

For modulus `m` and unit `Gamma`, with unit-supported carriers and arbitrary `ℓ²` coefficients,

```text
| ∑_{S1,S2} α(S1) β(S2) e_m(Gamma S1⁻¹ S2⁻¹) |²
    ≤ m M1 M2 ‖α‖₂² ‖β‖₂².
```

This is the same finite theorem as the C0 reciprocal bound. Its analytic validity does not require the pointwise definition of `Ω_H`: the statement quantifies over arbitrary coefficient vectors and only their `ℓ²` masses appear.

## TRANSVERSE ITEMS NOT PROVED BY THIS FORMAL SNAPSHOT

The 8298-job formal bank did not prove or encode:

- exact atomic carrier factorisation of `Q_*^red`;
- exact dependence of `B_*^red` on each carrier;
- existence of two simultaneously long usable signless carriers;
- completeness of a single-carrier residual classification;
- the later research-level one-conductor reciprocity theorem;
- the current `CRITICAL-BEZOUTNUMERATOR-SINGLECARRIER45` residual as a Lean theorem.

Only the source interface `TransverseCarrierPacket`, predicate `UsableTwoCarrierPair`, and bare trichotomy datatype `TransverseCarrierCase` exist in this formal snapshot. No exhaustiveness theorem is stated.

## PARALLEL b-DIAGONAL

`BDIAGONAL-AFFINEA-SURVIVING-VERTEX-RECT45`: **OPEN / PARALLEL / UNTOUCHED** in the formal snapshot. `no_double_spending` records that C0, transverse, and b-diagonal rows are distinct ledger entries.

## AXIOM AUDIT

`#print axioms` is run for every declaration of this delta in `RequestProject/Status/AxiomAuditErdos287C0UnitaryFourier.lean`. The supplied result reports that every declaration depends on a subset of `propext`, `Classical.choice`, `Quot.sound`; several depend on no axioms at all.

- no `sorryAx`;
- no custom `axiom`;
- no `unsafe`, `opaque`, `implemented_by`, or `native_decide`;
- decidable ledger facts use kernel checking.

## BUILD STATUS

```text
NEW MODULE BUILD:    PASS  (each of the eight new modules built individually)
DEFAULT lake build:  PASS  (8298 jobs, 0 errors)
```

This is the last actually supplied completed build for this C0/unitary-Fourier formal snapshot. A newer one-conductor formal build is not invented.

## SAFE FORMAL VERDICT

```text
RECIPROCAL UNITARY FOURIER:       PASS
COMPOSITE MODULUS:                PASS
UNIT-RESTRICTED VERSION:          PASS
INVERSION PERMUTATION:            PASS
RESIDUE AGGREGATION:              PASS
PRODUCT ENERGY:                   EXPLICIT HYPOTHESIS
FOUR-TERM CONTRACTION IDENTITY:   PASS
AFFINE/BILINEAR NUMERATOR:        PASS
OMEGA_H-BLIND FINITE THEOREM:     PASS
C0 PHYSICAL NORMALISATION:        EXPLICIT INTERFACE / SOURCE PIN
PERRON NORMALISATION:             SOURCE PIN
OMEGA_H NORMALISATION:            SOURCE PIN

C0 STATUS:
    ANALYTICALLY CLOSED
    CONDITIONAL ON FORMAL NORMALISATION

TRANSVERSE TWO-CARRIER FINITE THEOREM: FORMALLY AVAILABLE
LATER ONE-CONDUCTOR RESEARCH BANK:     NOT CLAIMED FORMAL HERE
PARALLEL b-DIAGONAL:                   OPEN
AXIOM AUDIT:                           PASS AS REPORTED
DEFAULT lake build:                    PASS — 8298 jobs / 0 errors
ERDOS287:                              OPEN
```

The current research frontier is maintained separately in `CURRENT_STATUS.md` and `RESEARCH_FRONTIERS/CURRENT_FRONTIERS.md`.