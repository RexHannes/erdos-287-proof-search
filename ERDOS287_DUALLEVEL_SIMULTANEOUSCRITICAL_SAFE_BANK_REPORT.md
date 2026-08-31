# ERDŐS #287 — DUAL-LEVEL / SIMULTANEOUS-CRITICAL SAFE BANK REPORT

Append-only delta on top of the previous one-conductor / `q_C` bank.
Nothing was deleted, renamed, weakened, relocated or silently strengthened.

---

## FILES ADDED

```
RequestProject/CurrentProgramme/Erdos287TransverseBezoutRowAffine.lean
RequestProject/CurrentProgramme/Erdos287TransverseBezoutThreeAxisFourier.lean
RequestProject/CurrentProgramme/Erdos287TransverseDualLevelReciprocity.lean
RequestProject/CurrentProgramme/Erdos287TransverseDualLevelXiReduction.lean
RequestProject/CurrentProgramme/Erdos287TransverseDualPairwiseFourier.lean
RequestProject/CurrentProgramme/Erdos287TransverseAffineProductEnergyInterface.lean
RequestProject/CurrentProgramme/Erdos287ReciprocalDensityDuality.lean
RequestProject/Status/CurrentStatusErdos287SimultaneousCritical.lean
RequestProject/Status/AxiomAuditErdos287DualLevel.lean
ERDOS287_DUALLEVEL_SIMULTANEOUSCRITICAL_SAFE_BANK_REPORT.md   (this file)
```

## FILES MODIFIED

```
RequestProject/Main.lean   — nine appended `import` lines only (no reordering, no deletion).
```

## FILES DELETED

```
none
```

`git diff --stat` against the pre-delta commit: **10 files changed, 2591 insertions(+), 0 deletions(-)**.

## PREVIOUS ONE-CONDUCTOR BANK PRESERVED

PRESERVED. The seven previously banked modules
(`Erdos287TransverseReducedConductor`, `…OneConductorReciprocity`, `…GammaReduction`,
`…QCUnitaryCompiler`, `…DenseQCInterface`,
`Status/CurrentStatusErdos287TransverseBezoutSingleCarrier`,
`Status/AxiomAuditErdos287TransverseOneConductor`) are byte-identical.
The new status layer re-checks their rows rather than editing them:

```
Erdos287.SimultaneousCriticalStatus.oneConductor_ledger_preserved
Erdos287.SimultaneousCriticalStatus.c0_ledger_preserved_after_dualLevel
Erdos287.SimultaneousCriticalStatus.singleCarrier_row_of_old_ledger_not_rewritten
```

The reciprocal finite Fourier theorem and the one-conductor Γ reduction were **not** re-proved;
they are imported and reused.

---

## NEW UNCONDITIONAL ARITHMETIC THEOREMS

Bézout-row affine CRT algebra (`Erdos287.TransverseBezoutRow`):

```
BezoutRowData                       (structure; every modular inverse is a supplied field
                                     together with its defining congruence)
BezoutRowData.cM_spec
BezoutRowData.gammaG_mod_m
BezoutRowData.gammaG_mod_m_inverse_free
BezoutRowData.gammaG_mod_r0
BezoutRowData.gammaG_affine_slope
affine_residue_unique_of_unit_slope
gammaG_affine_injective_mod_r0
gammaG_affine_injective_zmod
affineGcd_divisor_residue_class
affineGcd_solution_set_subset_class
affineGcd_interval_count            (#{h ∈ interval : d ∣ h·A_m − A_C} ≤ H/d + 1)
```

Dual `Ξ` normal form and `Ξ`-gcd reduction (`Erdos287.TransverseDualXi`):

```
dConst, dConst_dvd_mq, dConst_pos, dConst_dvd_const, dConst_dvd_slope, dConst_dvd_Xi
M0Dual, M0Dual_mul_dConst, M0Dual_pos
c0, s0, Xi0, Xi0_mul_dConst, Xi0_affine_slope
dXi, dXi_dvd_M0Dual, dXi_dvd_Xi0, dXi_pos
MPrime, XiPrime, MPrime_mul_dXi, XiPrime_mul_dXi
xiRed_coprime
xi_divisor_affine_residue_unique
constant_and_variable_xi_gcd_differ   (explicit witness: dConst = 1 while dXi = 3)
```

Dual CRT / reciprocity arithmetic (`Erdos287.TransverseDualLevel`):

```
int_modEq_combine_coprime, int_inverse_unique
Cmqg, Cmqg_mod_m, Cmqg_mod_q
Xi, Xi_affine_slope, Xi_affine_slope_mod
```

Affine-product algebra (`Erdos287.TransverseAffineProduct`):

```
numerator, numeratorAggregate
affineProduct_pushforward
affineProduct_collision_iff
```

Reciprocal-density algebra (`Erdos287.ReciprocalDensityDuality`):

```
reciprocalDensity_product_identity
reciprocalDensity_ratio_identity
reciprocalDensity_geometric_mean_bound
reciprocalDensity_ratio_bound
scaleSaturation_sanity_instance
```

## NEW FINITE FOURIER THEOREMS

```
Erdos287.TransverseBezoutThreeAxis.fiberAggregate(_l2_le_maxFiber, _sum)
Erdos287.TransverseBezoutThreeAxis.aggregatedFourier_bilinear_bound
Erdos287.TransverseBezoutThreeAxis.bezoutRowThreeAxisFourier_bound
Erdos287.TransverseBezoutThreeAxis.bezoutThreeAxis_contraction_identity
Erdos287.TransverseDualPairwise.doubleAggregatedFourier_bound
Erdos287.TransverseDualPairwise.dualPairwise_Delta_r_bound
Erdos287.TransverseDualPairwise.dualPairwise_Delta_ell_bound
Erdos287.TransverseDualPairwise.dualPairwise_ell_r_bound
Erdos287.TransverseDualPairwise.dualPairwise_min_bound
Erdos287.TransverseDualPairwise.dualPairwise_contraction_identity(_symmetric)
Erdos287.TransverseDualLevel.addPhase(_norm,_add,_period,_congr,_split)
Erdos287.TransverseDualLevel.transverseDualCRT_split(_int)
Erdos287.TransverseDualLevel.additiveReciprocity_coprime, additiveReciprocity_phase
Erdos287.TransverseDualLevel.transverseDualLevelReciprocity
```

## NEW CONDITIONAL ANALYTIC COMPILERS

Each carries its analytic input as a **visible hypothesis**, and each hypothesis shell has a
kernel-checked "not automatic" companion theorem, so nothing is silently discharged.

```
GroupedQEnergyHypothesis        + groupedQEnergy_not_automatic
transverseAllQAtomicGrouped_of_productEnergy
XiGcdTailBound                  + xiGcdTailBound_not_automatic + xiGcdTailBound_satisfiable
AffineProductEnergyBound        + affineProductEnergy_not_automatic
dualAffineProductFourier_of_energy
OmegaWeightedDivisorMomentBound + omegaWeighted_not_implied_by_l2 + omegaWeighted_satisfiable
SimultaneousCriticalPacket      + simultaneousCriticalPacket_fields_unfilled
```

## BEZOUT THREE-AXIS BANK

`f_g(ℓ,q) := γ_g(ℓ)·q⁻¹ mod M_g` with `M_g = m·r₀`, under explicit unit hypotheses
(`fG`, `fG_mul_q`). The fibre implications are proved:

* `fG_fibre_q_congr` : `f_g(ℓ,q)=v ⟹ v·q ≡ −A_C·g⁻¹ (mod m)`, so `q` lies in one class mod `m`;
* `fG_fibre_ell_congr` : `f_g(ℓ,q)=v ⟹ v·q ≡ k_g + A_m·ℓ (mod r₀)`, so `ℓ` lies in one class mod `r₀`;
* `box_fibre_card_le` : `#f_g⁻¹(v) ≤ (Q/m + 1)·(H₀/r₀ + 1)` in exact `Nat` division form;
* `bezoutRowThreeAxisFourier_bound` : the finite `L²` inequality
  `‖∑_Δ∑_{(ℓ,q)} a_Δ b_{ℓ,q} e_{M_g}(Δ f_g(ℓ,q))‖² ≤ M_g (∑‖a‖²)(K ∑‖b‖²)`
  for any explicit fibre bound `K`, with fully coupled `b_{ℓ,q}`;
* `bezoutThreeAxis_contraction_identity` : the exact eight-term expansion
  `M_g(1+D₀/M_g)(1+H₀/r₀)(1+Q/m)/(D₀H₀Q) = M_g/(D₀H₀Q)+g/(HQ)+r/(D₀H)+m/(D₀Q)+g/(mH)+g/(rQ)+1/D₀+g/(mr)`
  under `M_g = m r₀`, `r = g r₀`, `H = g H₀`. It is an identity, not a saving.

## DUAL CRT SPLIT

`transverseDualCRT_split` (with its integer form `transverseDualCRT_split_int`) proves the exact
coprime-modulus factorisation of `e_{m r₀}(Δ γ_g(ℓ) q⁻¹)` into
`e_m(Δ c_m (q r₀)⁻¹) · e_{r₀}(Δ d_ℓ (m q)⁻¹)` under **exact** coprimality hypotheses
`gcd(q,m)=gcd(q,r₀)=gcd(m,r₀)=1`; all inverses are supplied with their defining congruences.
No global `gcd(r,m)=1` is assumed anywhere.

## DUAL RECIPROCITY

`additiveReciprocity_coprime` / `additiveReciprocity_phase` give the reciprocity identity in a
robust integer / additive-character formulation (no brittle real equality).
`DualReciprocityData` packages modulus `m·q`, `Ξ`, the Archimedean parameter `archDual` and its
norm-one property; `transverseDualLevelReciprocity` states the arithmetic-character equality with
the Archimedean factor carried, and `archDual_is_a_free_parameter` proves that every modulus-one
complex number occurs — so no theorem here determines or discharges it.

## Ξ REDUCTION

`Ξ(ℓ) = C_{mqg} − k_g − A_m ℓ (mod m q)` with exact affine slope `Ξ(ℓ+1) − Ξ(ℓ) ≡ −A_m`.
Constant gcd `dConst = gcd(C−k_g, A_m, m q)` divides every `Ξ(ℓ)`; `M0Dual = (m q)/dConst` is
formed only with an explicit divisibility proof. The **variable** gcd `dXi(ℓ) = gcd(Ξ₀(ℓ), M0Dual)`
is kept strictly separate — `constant_and_variable_xi_gcd_differ` exhibits a witness where they
differ. `xiRed_coprime` proves `gcd(Ξ'(ℓ), M') = 1` on a packet, and
`xi_divisor_affine_residue_unique` is the unconditional residue-uniqueness statement.
The weighted large-`dXi` closure is **not** derived from residue uniqueness; it remains the
explicit interface `XiGcdTailBound`.

## DUAL PAIRWISE FOURIER

`fDual(ℓ,r₀) := Ξ'(ℓ)·r₀⁻¹ mod M'`, with `fDual_r_unique`, `fDual_ell_unique`, and exact interval
fibre counts `fDual_r_fibre_interval_count`, `fDual_ell_fibre_interval_count`
(`≤ R₀/M' + 1`, `≤ H₀/M' + 1`). Three finite `L²` inequalities are proved with the unused source
coordinate absorbed into the coefficient vector: `dualPairwise_Delta_r_bound`,
`dualPairwise_Delta_ell_bound`, `dualPairwise_ell_r_bound`.
`dualPairwise_min_bound` is the no-double-spending firewall: the packet may use the **minimum** of
the available bounds; `dualPairwise_min_is_not_product` exhibits an explicit witness (2,2) showing
the minimum is strictly weaker than the product, so the bounds can never be multiplied.
`dualPairwise_contraction_identity` records `M'/(D₀R₀) + 1/D₀ + 1/R₀ + 1/M'` and its symmetric
variant as exact algebra.

## AFFINE-PRODUCT INTERFACE

`numerator(Δ,ℓ) := Δ·Ξ'(ℓ) mod M'`, aggregate `A_t`, and the exact pushforward identity
`affineProduct_pushforward` rewriting the dual operator as `∑_{t,r₀} A_t c_{r₀} e_{M'}(t r₀⁻¹)`.
`affineProduct_collision_iff` is the exact collision equation. The Cochrane–Shi-type modular
energy is **not** reproduced: it is the explicit hypothesis `AffineProductEnergyBound` with a
parameterised constant `K_energy`, and the conditional compiler
`dualAffineProductFourier_of_energy` concludes an explicit finite `L²` inequality from it.
No `8^ω(M) τ(M) log³M` constant is asserted as a proved Lean theorem.

## RECIPROCAL-DENSITY DUALITY

`ρ_old = D₀H₀Q/(mR₀)`, `ρ_dualPair = D₀R₀/(mQ)`, `ρ_dualFull = D₀H₀R₀/(mQ)`, with the two exact
identities `ρ_old·ρ_dualFull = (D₀H₀/m)²` and `ρ_dualFull/ρ_old = (R₀/Q)²`, and the safe
deterministic implications `reciprocalDensity_geometric_mean_bound`,
`reciprocalDensity_ratio_bound`. The scale-saturation face is recorded as an exact monomial
instance (`t = X^{1/3}`): old density `= 1` (natural), dual pair density `= t > 1`
(supercritical), full dual density `= t²`. `reciprocalDensity_duality_is_not_closure` is the
firewall: the algebra alone bounds nothing.

## OMEGA WEIGHTED NORM PIN

`OmegaWeightedDivisorMomentBound` (`N_Ω,C := ∑_E |Ω_E|² C(E)/E²`) remains an explicit pin.
`omegaWeighted_not_implied_by_l2` proves it is not implied by the plain `L²` shell, and
`omegaWeighted_satisfiable` shows the shell is non-vacuous.
`omega_norms_are_separate_pins` in the status layer keeps it distinct from the earlier
`SHAREDGCD-OMEGAH-NORMALISATION-SOURCEPIN45`.

## SUPERSEDED FRONTIERS

```
THREEFACTOR-TRANSVERSE-CRITICAL-BEZOUTNUMERATOR-SINGLECARRIER45
    → superseded as first frontier; structural content NOT marked false
      (singleCarrier_absorbed_not_false, SingleCarrierAbsorption metadata:
       "single-carrier atomic classification absorbed by three-axis grouping").

BRANCHI-ULTRANEAR-BEZOUTROW-CRITICALDENSITY-MOBIUSLEVEL45
    → strictly reduced / superseded as first frontier, not deleted, not declared false.

OLD SCALE-SATURATION FACE / DUAL-DENSITY SUPERCRITICAL POLYTOPE
    → recorded as analytically closed at research level; formal content is the algebra above.

CROSS-PACKET TWO-AXIS
    → retracted (structural failure), status metadata only; no universal impossibility theorem.
```

## CURRENT FRONTIER

```
THREEFACTOR-TRANSVERSE-BRANCHI-SIMULTANEOUSCRITICAL-DUALLEVEL-AFFINEPRODUCT-MOBIUS45 : open
```

recorded by `simultaneousCritical_is_first_frontier`. Boundary constraints
(`D₀H₀ ≤ m L^C`, `Q ≍ R₀ L^{O(1)}`) are metadata only (`SimultaneousCriticalBoundary`,
`boundary_constraints_are_metadata`); no `~` is encoded as a theorem.
The outer `μ(r₀)` sign remains linear (`mobius_sign_remains_linear`); **no** Möbius cancellation
theorem was invented, and it is not squared away in metadata.
Level Type-I / Type-II statuses are recorded separately (`level_typeI_typeII_status`).

## B-DIAGONAL FIREWALL

```
BDIAGONAL-AFFINEA-SURVIVING-VERTEX-RECT45 : open / untouched
```

`bdiagonal_untouched` records that no theorem of this delta touches it and no C0 gain is reused.

## FORMAL SOURCE PINS

```
SHAREDGCD-OMEGAH-NORMALISATION-SOURCEPIN45            (preserved)
complete physical Perron / nuclear normalisation      (preserved)
weighted Ω divisor-moment norm  N_Ω,C                 (new, explicit)
grouped-q product energy                              (explicit)
large-g weighted router                               (explicit / status)
large-Ξ-gcd weighted router (XiGcdTailBound)          (explicit)
affine-product modular energy (Cochrane–Shi type)     (explicit)
physical source-length margins                        (explicit / status)
```

None of these is collapsed into an analytic theorem.

## AXIOM AUDIT

`RequestProject/Status/AxiomAuditErdos287DualLevel.lean` runs `#print axioms` on **161**
declarations of this delta.

```
53   declarations depend on NO axioms
108  declarations depend only on subsets of {propext, Classical.choice, Quot.sound}
0    sorryAx
0    custom axioms
0    native_decide / Lean.ofReduceBool
0    unsafe / opaque / implemented_by
```

A textual scan of all nine new files finds `sorry`, `axiom`, `unsafe`, `native_decide`,
`implemented_by`, `opaque` only inside docstring prose, never as a code construct.

## BUILD STATUS

```
Per-module builds:  all nine new modules build individually, 0 errors.

Default `lake build`:
    Build completed successfully (8314 jobs).
    errors:   0
    warnings: only pre-existing linter notes in legacy files (unused simp arguments,
              unused variables); none in the new modules.
```

The previous run reported 8305 jobs; the count immediately after this delta is **8314**, reported
as measured.  After the additional semantic re-anchoring layer
(`Status/SemanticFirewallsErdos287`, `Status/CurrentAuthoritativeStatusErdos287`,
`Status/AxiomAuditErdos287SemanticReanchor`, documented in
`ERDOS287_HOSTILE_SEMANTIC_REANCHOR_AUDIT.md`) the final default build is **8317 jobs, 0 errors**.

## CURRENT ERDŐS287 LEDGER

```
C0:                          ANALYTICALLY CLOSED, CONDITIONAL ON FORMAL SOURCE NORMALISATION
EXACT PRODUCT COLLISION:     ANALYTICALLY CLOSED (research level)
DOUBLE TYPE II:              ANALYTICALLY CLOSED (research level)
TRANSVERSE ONE-CONDUCTOR:    PASS
qC UNITARY:                  PASS
BEZOUT THREE-AXIS:           PASS
DUAL-LEVEL RECIPROCITY:      PASS
DUAL PAIRWISE FOURIER:       PASS
RECIPROCAL-DENSITY DUALITY:  PASS (algebra kernel-proved; physical closure NOT claimed)
AFFINE-PRODUCT ENERGY:       PASS CONDITIONAL ON WEIGHTED Ω NORM
OLD SATURATION FACE:         CLOSED ANALYTICALLY / SUPERSEDED
TRANSVERSE:                  STRICTLY REDUCED / OPEN
FIRST ANALYTIC RESIDUAL:     THREEFACTOR-TRANSVERSE-BRANCHI-SIMULTANEOUSCRITICAL-
                             DUALLEVEL-AFFINEPRODUCT-MOBIUS45
B-DIAGONAL:                  OPEN
ERDOS287:                    OPEN
```

---

## STRICT FINAL OUTPUT

```
FILES ADDED:                      9 Lean files + this report (listed above)
FILES MODIFIED:                   RequestProject/Main.lean (appended imports only)
FILES DELETED:                    none
PREVIOUS ONE-CONDUCTOR BANK:      PRESERVED
BEZOUT ROW AFFINE SOURCE:         PASS
gamma_g MOD m:                    PASS
gamma_g MOD r0:                   PASS
AFFINE INJECTIVITY:               PASS
BEZOUT THREE-AXIS FIBRE:          PASS
BEZOUT THREE-AXIS FOURIER:        PASS
ALL-q GROUPED COMPILER:           CONDITIONAL (explicit product-energy hypothesis)
LARGE-g FORMAL CORE:              PASS (residue class + interval count; router left as interface)
DUAL CRT SPLIT:                   PASS
DUAL RECIPROCITY:                 PASS (Archimedean factor retained as free parameter)
Xi AFFINE NORMAL FORM:            PASS
CONSTANT Xi GCD:                  PASS
VARIABLE Xi GCD RESIDUE UNIQUENESS: PASS
XiRED COPRIME:                    PASS
DUAL FREQUENCY FIBRES:            PASS
DUAL PAIRWISE FOURIER:            PASS
PACKETWISE MIN FIREWALL:          PASS
RECIPROCAL-DENSITY PRODUCT IDENTITY: PASS
RECIPROCAL-DENSITY RATIO IDENTITY:   PASS
RECIPROCAL-DENSITY-DUALITY45:     FORMAL ALGEBRA PASS (physical closure status-only)
AFFINE-PRODUCT PUSHFORWARD:       PASS
AFFINE-PRODUCT COLLISION:         PASS
AFFINE-PRODUCT ENERGY:            CONDITIONAL INTERFACE
OMEGA WEIGHTED NORM:              EXPLICIT PIN (not discharged)
SUPERSEDED FRONTIER 1:            CRITICAL-BEZOUTNUMERATOR-SINGLECARRIER45 — SUPERSEDED
SUPERSEDED FRONTIER 2:            BRANCHI-ULTRANEAR-BEZOUTROW-CRITICALDENSITY-MOBIUSLEVEL45
                                  — STRICTLY REDUCED
CURRENT FIRST ANALYTIC FRONTIER:  THREEFACTOR-TRANSVERSE-BRANCHI-SIMULTANEOUSCRITICAL-
                                  DUALLEVEL-AFFINEPRODUCT-MOBIUS45
TRANSVERSE:                       STRICTLY REDUCED / OPEN
B-DIAGONAL:                       OPEN / UNTOUCHED
FORMAL NORMALISATION:             still an explicit source pin (unchanged)
ERDOS287:                         OPEN
AXIOM AUDIT:                      161 declarations; 53 axiom-free; 108 Mathlib-standard only;
                                  no sorryAx, no custom axiom, no native_decide
NEW MODULE BUILDS:                all PASS individually
DEFAULT lake build:               PASS — 8314 jobs, 0 errors
DOUBLE-SPENDING AUDIT:            PASS (dualPairwise_min_bound; min, never product)
OVERCLAIM AUDIT:                  PASS (no Category-C item converted into a theorem;
                                  no theorem concludes `True`)
STRONGEST SAFE NEW FORMAL BANK:   Bézout-row affine CRT algebra + three-axis fibre/Fourier bank
                                  + dual CRT split and reciprocity + Ξ normal form and reduction
                                  + dual pairwise finite Fourier with min firewall
                                  + affine-product pushforward/collision
                                  + reciprocal-density identities
FINAL FORMAL VERDICT:             SAFE APPEND-ONLY BANK UPDATED
```

STOP.
