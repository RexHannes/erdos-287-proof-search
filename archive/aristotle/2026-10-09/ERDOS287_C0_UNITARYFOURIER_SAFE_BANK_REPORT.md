# ERDŐS #287 — C0 UNITARY-FOURIER SAFE BANK REPORT

Append-only delta.  No existing file was deleted, relocated, renamed, weakened or reinterpreted;
`RequestProject/Main.lean` received appended `import` lines only.

---

## FILES ADDED

- `RequestProject/CurrentProgramme/Erdos287ReciprocalUnitaryFourier.lean`
- `RequestProject/CurrentProgramme/Erdos287BalancedBUnitaryFourierCompiler.lean`
- `RequestProject/CurrentProgramme/Erdos287AffineBilinearReciprocalNumerator.lean`
- `RequestProject/CurrentProgramme/Erdos287C0PhysicalNormalisationInterface.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseCarrierInterface.lean`
- `RequestProject/Status/CurrentStatusErdos287C0UnitaryFourier.lean`
- `RequestProject/Status/CurrentStatusErdos287TransverseCarrier.lean`
- `RequestProject/Status/AxiomAuditErdos287C0UnitaryFourier.lean`
- `ERDOS287_C0_UNITARYFOURIER_SAFE_BANK_REPORT.md` (this file)

Paths follow the repository's own conventions (`CurrentProgramme/` for mathematics,
`Status/` for ledgers and axiom audits), which is where all earlier deltas live.

## FILES MODIFIED

- `RequestProject/Main.lean` — eight appended `import` lines, nothing reordered or removed.

---

## NEW KERNEL THEOREMS (unconditional, `sorry`-free)

### `Erdos287.ReciprocalUnitaryFourier`

| name | statement |
|---|---|
| `norm_sum_mul_sq_le` | finite Cauchy–Schwarz over `ℂ` |
| `unitaryFourierKernel` | `F_C(y,z) = e_x(C y z)` (definition) |
| `unitaryFourierKernel_symm`, `unitaryFourierKernel_norm` | symmetry; `‖F_C(y,z)‖ = 1` |
| `unitaryFourier_mulConj_sum` | **full Gram**: `∑_z F_C(y,z) conj F_C(y',z) = x·[y=y']`, i.e. `F_C F_C^* = x I` |
| `unitaryFourier_column_energy` | `∑_y ‖∑_z B z F_C(y,z)‖² = x ∑_z ‖B z‖²` (exact) |
| `unitaryFourier_bilinear_bound` | `‖∑_{y,z} A y B z F_C(y,z)‖² ≤ x ‖A‖₂² ‖B‖₂²` |
| `unitaryFourier_finset_bilinear_bound` | same for arbitrary finite supports (zero extension) |
| `isUnit_zmod_inv`, `zmod_inv_inv_of_isUnit`, `zmod_inv_bijOn_units` | inversion permutation of the units |
| `reciprocalUnitaryFourier_bilinear_bound` | **principal new theorem**: `‖∑_{r,s unit} A r B s e_x(C r⁻¹ s⁻¹)‖² ≤ x ‖A‖₂² ‖B‖₂²` |
| `transverseTwoCarrierUnitaryFourier` | naming alias of the previous line for modulus `m`, unit `Gamma` (no second proof) |
| `unitaryFourier_mulConj_sum_composite` | explicit instance at the **composite** modulus `x = 12`, `C = 5` |

### `Erdos287.BalancedBUnitaryFourier`

| name | statement |
|---|---|
| `norm_sum_sq_le_card` | `‖∑_{i∈s} f i‖² ≤ #s ∑_{i∈s} ‖f i‖²` |
| `residueAggregate` | aggregation of a coefficient sequence over one residue class (definition) |
| `residueAggregate_l2_le_maxFiber` | `∑_r ‖agg r‖² ≤ M ∑_n ‖A n‖²` for any uniform fibre bound `M` |
| `interval_residue_fibre_card_le` | an interval of length `N` meets a class mod `x` in `≤ N / x + 1` points (`ℕ`-division) |
| `intervalResidueAggregate_l2_bound` | interval corollary of the aggregation inequality |
| `reciprocalPhase_fiberwise` | exact regrouping of a reciprocal-phase double sum by residues |
| `balancedReciprocalFourier_compiler` | `‖∑_{n,e} A n β e e_x(C n⁻¹ e⁻¹)‖² ≤ x M_N M_E E_A E_B` on unit support |
| `balancedFourier_contraction_identity` | `x(1+N/x)(1+E/x)/B = x/B + 1/E + 1/N + 1/x` when `B = N E` |
| `coprime_product_left / _middle / _right / _all` | non-unit firewall: each factor of `b = ℓ d e` coprime to `x` |
| `productConvolutionEnergy_not_automatic` | the convolution-energy interface can fail |

### `Erdos287.AffineBilinearReciprocalNumerator`

`zmod_inv_mul_of_isUnit`, `affineNumerator_reciprocal_decomposition`,
`affineBilinearNumerator_reciprocal_decomposition`
(`(B₀+B₁S₁+B₂S₂+B₃S₁S₂)(S₁S₂)⁻¹ = B₀S₁⁻¹S₂⁻¹ + B₁S₂⁻¹ + B₂S₁⁻¹ + B₃`),
`affineNumerator_character_factorisation`, `affineBilinearNumerator_character_factorisation`,
`affineBilinear_rankOne_reduction`.

### Interfaces with non-automaticity witnesses

`perronNuclearNormalisation_not_automatic`, `omegaHL2Normalisation_not_automatic`,
`c0PhysicalNormalisation_not_automatic`, `c0PhysicalNormalisation_satisfiable`,
`usableTwoCarrierPair_not_automatic`, `usableTwoCarrierPair_satisfiable`,
`transverseCarrierCase_no_exhaustiveness_claimed`,
plus the status-layer ledger theorems and `inv_sqrt_comparison_not_automatic`,
`constant_order_acyclic`.

### Conditional compilers (explicit hypotheses only)

- `Erdos287.BalancedBUnitaryFourier.threeCarrierReciprocalFourier_of_productEnergy`
  — hypothesis `ProductConvolutionEnergyHypothesis`.
- `Erdos287.C0PhysicalNormalisation.c0_balanced_branch_bound_of`
  — hypotheses: unit conditioned coefficient, unit carrier support, residue-fibre bounds,
  `ProductConvolutionEnergyHypothesis`, `OmegaHL2NormalisationHypothesis`.
  Its conclusion is an **explicit finite inequality**, not a proposition named “C0 closed”, and
  not `True`.
- `Erdos287.C0PhysicalNormalisation.perronNuclear_total_of_normalisation`,
  `omegaHL2_of_pointwise_normalisation`.
- `Erdos287.TransverseCarrier.transverseTwoCarrier_bound_of_unitSupport`,
  `transverseTwoCarrier_bound_with_fibre_weights`.

## REUSED BANK

- `Erdos287.ConditionedInverseConv.OmegaHNormalizationHypothesis` and
  `omegaH_energy_of_normalization` are **reused, not duplicated**: the new `ℓ²` shell is derived
  from the existing pointwise shell by `omegaHL2_of_pointwise_normalisation`.
- The transverse two-carrier mechanism reuses `reciprocalUnitaryFourier_bilinear_bound` verbatim
  through an alias; there is no second proof.
- The earlier C0 source-lift and COMMON-x ledgers are re-checked and proved preserved
  (`sourceLift_ledger_still_preserved`, `c0_ledger_still_preserved`).

## RETRACTED ARCHITECTURE (not re-encoded anywhere)

- old post-conditioning index `n = j (u')⁻¹ mod x` — `retracted`;
- old wrap `1 + U U' / B` — `retracted`;
- the common raw factor `b u'` is cancelled before projective conditioning and is not
  reintroduced.

The conditioned Kloosterman kernel of the research source is `S(-a_ρ b_ρ⁻¹, j; x)`; the finite
theorems of this delta are stated for the abstract reciprocal kernel `e_x(C r⁻¹ s⁻¹)` and are
independent of that identification.

## C0 ANALYTIC STATUS

```
C0 ANALYTIC CORE:
    CLOSED.

C0 PHYSICAL/FORMAL NORMALISATION:
    OPEN SOURCE PIN.

Therefore:
    C0 ANALYTICALLY CLOSED
    CONDITIONAL ON FORMAL NORMALISATION.
```

The bare phrase “C0 CLOSED” is used nowhere.  No Lean theorem asserts C0 closure.

## FORMAL SOURCE PINS

- `SHAREDGCD-OMEGAH-NORMALISATION-SOURCEPIN45` — represented by
  `OmegaHNormalizationHypothesis` (pointwise, pre-existing) and
  `OmegaHL2NormalisationHypothesis` (`ℓ²`, new).  Never assumed.
- complete Perron / nuclear normalisation — `PerronNuclearNormalisationHypothesis`.  Never
  assumed, no constant guessed.
- Bundle: `C0PhysicalNormalisationData` / `C0PhysicalNormalisationHypothesis`, proved neither
  automatic nor contradictory.

## TRANSVERSE CONDITIONAL MECHANISM

For modulus `m` and unit `Gamma`, with unit-supported carriers and arbitrary `ℓ²` coefficients,

```
| ∑_{S1,S2} α(S1) β(S2) e_m(Gamma S1⁻¹ S2⁻¹) |² ≤ m M₁ M₂ ‖α‖₂² ‖β‖₂².
```

This is the same finite theorem as the C0 reciprocal bound.  Its analytic validity does **not**
require the pointwise definition of `Ω_H`: the statement quantifies over arbitrary coefficient
vectors, and only their `ℓ²` masses appear.

## TRANSVERSE UNPROVED CARRIER FACTORISATION

Not proved, and not encoded:

- exact atomic carrier factorisation of `Q_*^red`;
- exact dependence of `B_*^red` on each carrier;
- existence of two simultaneously long usable signless carriers (`E = e/a₁`, `R = r₂/c₂`);
- `E · R > m L^K`;
- completeness of a single-carrier residual classification;
- `THREEFACTOR-TRANSVERSE-SINGLECARRIER-RESIDUAL45` as an exact fact.

Only the source interface `TransverseCarrierPacket` (three **unfilled** `Prop` fields), the
predicate `UsableTwoCarrierPair` and the bare trichotomy datatype `TransverseCarrierCase` exist.
No exhaustiveness theorem is stated.

## PARALLEL b-DIAGONAL

`BDIAGONAL-AFFINEA-SURVIVING-VERTEX-RECT45` : **OPEN / PARALLEL / UNTOUCHED**.  It is a separate
ledger row; `no_double_spending` records that the C0 row, the transverse row and the b-diagonal
row are distinct entries with distinct labels.

## AXIOM AUDIT

`#print axioms` is run for every declaration of this delta in
`RequestProject/Status/AxiomAuditErdos287C0UnitaryFourier.lean`.  Result: every declaration
depends on a subset of `propext`, `Classical.choice`, `Quot.sound`; several depend on no axioms
at all.

- no `sorryAx`;
- no custom `axiom`;
- no `unsafe`, no `opaque`, no `implemented_by`, no `native_decide`;
- decidable ledger facts use `decide +kernel`.

A token scan over the eight new files finds none of `sorry`, `admit`, `axiom`, `unsafe`,
`opaque`, `implemented_by`, `native_decide` as a code construct (they occur only in the audit
docstring that lists them).

## BUILD STATUS

```
NEW MODULE BUILD:    PASS  (each of the eight new modules built individually)
DEFAULT lake build:  PASS  (8298 jobs, 0 errors)
```

No pre-existing failure was encountered, and no legacy module was touched.

## CURRENT 287 LEDGER

KERNEL-PROVED / SAFE FORMAL BANK:

```
finite reciprocal unitary Fourier Gram;
reciprocal unitary bilinear bound;
unit-restricted / inverse-residue version;
residue aggregation inequalities;
four-term contraction identity;
affine/bilinear numerator reciprocal decomposition;
fixed-depth convolution energy: EXPLICIT HYPOTHESIS ONLY (not formalised as a theorem).
```

ANALYTIC RESEARCH BANK (metadata; not Lean theorems):

```
FIXEDRATIO-BALANCED-b-UNITARYFOURIER45                                : PASS.
EXACTPRODUCT-CONDITIONED-FIXEDRATIO-BALANCEDDOUBLEFRACTION-LEVEL45    : ANALYTICALLY CLOSED.
EXACTPRODUCT-CONDITIONED-INVERSECONV-LEVELLS45                        : ANALYTICALLY CLOSED.
EXACT PRODUCT COLLISION                                               : ANALYTICALLY CLOSED.
DOUBLE TYPE II                                                        : ANALYTICALLY CLOSED.
```

C0:

```
ANALYTICALLY CLOSED CONDITIONAL ON FORMAL SOURCE NORMALISATION.
```

FORMAL SOURCE PINS:

```
SHAREDGCD-OMEGAH-NORMALISATION-SOURCEPIN45;
complete Perron/nuclear normalisation unless absorbed into the same named pin.
```

TRANSVERSE SAFE NEW OBSERVATION:

```
the two-carrier reciprocal unitary Fourier theorem is valid for arbitrary L2 coefficients;
affine/bilinear moving numerators preserve finite-rank reciprocal Fourier structure;
the Omega_H pointwise formula is not needed by the analytic theorem.
```

TRANSVERSE NOT YET PROVED: as listed above.

NEXT EXACT ANALYTIC RESEARCH TARGET:

```
THREEFACTOR-TRANSVERSE-CARRIERFACTORIZATION-PAIR-EXISTENCE45.
```

PARALLEL:

```
BDIAGONAL-AFFINEA-SURVIVING-VERTEX-RECT45 : OPEN.
```

ERDOS287:

```
OPEN.
```

---

## HOSTILE FINAL AUDIT

1. No theorem claims C0 unconditionally closed. **PASS**
2. No theorem assumes the Perron nuclear bound without an explicit hypothesis. **PASS**
3. No theorem assumes an `Ω_H` norm without an explicit hypothesis. **PASS**
4. No theorem assumes `E` and `R` are both long. **PASS**
5. No theorem assumes a two-carrier transverse pair exists. **PASS**
6. No SINGLECARRIER residual is promoted as exact. **PASS**
7. `x` and `X` are not silently identified; `inv_sqrt_comparison_not_automatic` exhibits a
   failure of the comparison. **PASS**
8. D4 unit routing appears only as research metadata (transverse status layer §3); the formal
   content is the coprimality firewall. **PASS**
9. The finite Fourier theorem works for composite modulus; witnessed at `x = 12`. **PASS**
10. No squarefree assumption anywhere in the delta. **PASS**
11. No `φ(x)/x` density factor in any `ℓ²` statement. **PASS**
12. No pointwise divisor maximum in the product-energy interface. **PASS**
13. Projective fourth moment is not reused. **PASS**
14. C0 and transverse savings are separate ledger rows (`no_double_spending`). **PASS**
15. Parallel b-diagonal remains separate and untouched. **PASS**

---

## STRICT FINAL OUTPUT

```
FILES ADDED:                      8 (listed above)
FILES MODIFIED:                   RequestProject/Main.lean (appended imports only)

RECIPROCAL UNITARY FOURIER:       PASS
COMPOSITE MODULUS:                PASS
UNIT-RESTRICTED VERSION:          PASS
INVERSION PERMUTATION:            PASS
RESIDUE AGGREGATION:              PASS
PRODUCT ENERGY:                   EXPLICIT HYPOTHESIS
FOUR-TERM CONTRACTION IDENTITY:   PASS
AFFINE/BILINEAR NUMERATOR:        PASS
THREE-CARRIER CONDITIONAL COMPILER: PASS (conditional on the explicit energy hypothesis)
OMEGA_H-BLIND FINITE THEOREM:     PASS
C0 PHYSICAL NORMALISATION INTERFACE: CREATED
PERRON NORMALISATION:             SOURCE PIN
OMEGA_H NORMALISATION:            SOURCE PIN

C0 STATUS:
    ANALYTICALLY CLOSED
    CONDITIONAL ON FORMAL NORMALISATION

TRANSVERSE TWO-CARRIER MECHANISM: FORMALLY AVAILABLE
TRANSVERSE CARRIER FACTORISATION: OPEN
TWO-LONG-CARRIER EXISTENCE:       NOT PROVED

NEXT EXACT TRANSVERSE TARGET:
    THREEFACTOR-TRANSVERSE-CARRIERFACTORIZATION-PAIR-EXISTENCE45

PARALLEL b-DIAGONAL:              OPEN / UNTOUCHED

AXIOM AUDIT:                      only propext, Classical.choice, Quot.sound (inherited);
                                  no sorryAx, no custom axiom, no unsafe/opaque/native_decide

NEW MODULE BUILD:                 PASS
DEFAULT lake build:               PASS

DOUBLE-SPENDING AUDIT:            PASS

STRONGEST SAFE NEW FORMAL BANK:
    reciprocalUnitaryFourier_bilinear_bound
    (finite reciprocal unitary Fourier bilinear bound for arbitrary L2 coefficients
     on units of an arbitrary, possibly composite, modulus),
    together with balancedReciprocalFourier_compiler and
    affineBilinearNumerator_reciprocal_decomposition.

ERDOS287:                         OPEN

FINAL FORMAL VERDICT:
    SAFE APPEND-ONLY BANK UPDATED
```

STOP.
