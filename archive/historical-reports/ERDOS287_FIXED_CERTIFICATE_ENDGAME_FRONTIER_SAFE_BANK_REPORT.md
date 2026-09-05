# Erdős #287 — fixed-certificate endgame frontier (append-only safe bank)

**Erdős #287 is NOT claimed proved.**  No external analytic theorem was formalised, no
source/analytic socket was inhabited, and no `axiom` was added.  Everything below is either
finite algebra/combinatorics kernel-proved in Lean, an explicit *uninhabited* typed socket,
or clearly labelled metadata.

## Files added (append-only; nothing was deleted, renamed or weakened)

- `RequestProject/CurrentProgramme/Erdos287FixedCertificateRepairedData.lean`
  — `c₂ = +1` as explicit data; the perturbed certificate
  `g_ε(x) = g₀(x)·1_{|x| ≤ 1/2 − 2ε}` as an *indicator truncation*, with the kernel-proved
  separation `gPerturb_is_not_a_scalar_shrink`.
- `RequestProject/CurrentProgramme/Erdos287PhysicalSupportPartition.lean`
  — the four literal support classes, the regions `P_X, N1_X, N2_X, U_X`, the finite set
  identity `I_X = P_X ⊎ N1_X ⊎ N2_X ⊎ U_X` (union, six disjointness statements, cardinality,
  region-wise sum decomposition); the physical weights
  `a_X(n) = W(n/X)[Λ(2n−1)+Λ(2n+1)]`, `b_X(n) = 4W(n/X)Bsrc(n)`, `w_X = a_X − b_X`,
  `H_X = H_ε`, with `bX_determines_Bsrc` forbidding substitution of an unrelated `B`;
  the channels `E_T`, `E_L`, `E_2`, `E_M`, `Bmass` defined by the literal classes only.
- `RequestProject/CurrentProgramme/Erdos287FourErrorTransference.lean`
  — `fourRegion_transference`:
  `primeMass ≥ (1+Cc)·Bmass − E_T − E_L − E_2 − E_M` (**no factor 3**), and
  `primeMass_pos_of_channel_budget`; the positive-margin firewall (published limiting
  margin `6·10⁻⁶` recorded as metadata; no explicit `ε₀` manufactured).
- `RequestProject/CurrentProgramme/Erdos287EndgameSourceSockets.lean`
  — `FordSourceIndex` (k, J, T, large-prime leaves, u/v, selected E, Perron/Mellin labels,
  orientation, source sign, owner), the reused six-constructor `Owner`,
  `MasterSourceToTypedPerronPacketsInput`, `FixedCertificateN2LambdaCollarInput`
  (+ `N2CollarVanishing`, + the guard that the bounded-sequence `N2` theorem is *not* a
  literal inhabitant for the physical `Λ` weight), `GlobalBsrcComparisonMarginInput`,
  `Ford83ExplicitOEpsilonCollarConstants`.  All four sockets uninhabited, each with a
  counterguard.
- `RequestProject/CurrentProgramme/Erdos287FCLWindowPairBridgeTwelve.lean`
  — `windowPairSupply_of_positiveFCLMass_twelve`: for `M ≥ 12`, `FCL_W(M/2) →
  WindowPairSupply M`, both the plus (`2q+1 = r^a`) and minus (`2q−1 = r^a`) cases, every
  literal field discharged; non-vacuity at `M = 12` (`q = 5`, `2q+1 = 11`).
- `RequestProject/CurrentProgramme/Erdos287EndgameConditionalFCLCompiler.lean`
  — the `E_T` channel from master source + analytic kernel; the `E_L` channel from the
  `U`-source subset, with the firewall `leakage_not_implied_by_total`; the conditional FCL
  compiler `fixedCertificatePositiveMass_of_all_sockets`.
- `RequestProject/CurrentProgramme/Erdos287EndgameEffectivityAndClosure.lean`
  — `AsymptoticFCL` / `EffectiveFCL` / `EffectiveWindowPairSupply` kept separate; the
  effectivity socket (`ε₀`, `X₀`, `M₀ ≤ 4·10⁹`); the end-to-end conditional chain to
  `Erdos287Statement`.
- `RequestProject/Status/CurrentStatusErdos287FixedCertificateEndgameFrontier.lean`
  — the new layer `fixedCertificateEndgameFrontier`, proved strictly later than every
  earlier layer, with earlier ledgers re-checked rather than rewritten.
- `RequestProject/Status/AxiomAuditErdos287FixedCertificateEndgameFrontier.lean`
  — `#print axioms` on every principal new theorem.
- `RequestProject/Main.lean` — nine new `import` lines appended.

## STRICT FINAL OUTPUT

```
LAKE BUILD:                 PASS
JOB COUNT:                  8379
NEW WARNINGS:               none in the new modules
SORRYAX:                    NONE
CUSTOM AXIOM:               NONE
SUPPORT PARTITION:          PASS
FOUR-ERROR ALGEBRA:         KERNEL-PROVED
MASTER SOURCE SOCKET:       UNINHABITED
N2 LAMBDA-COLLAR SOCKET:    UNINHABITED
BSRC COMPARISON SOCKET:     UNINHABITED
POSITIVE MARGIN SOCKET:     UNINHABITED
CONDITIONAL FCL COMPILER:   KERNEL-PROVED (conditional)
FCL->WINDOWPAIR:            KERNEL-PROVED (conditional)
BRIDGE THRESHOLD:           12
EFFECTIVITY SOCKET:         UNINHABITED
Erdos287ClosureInputs:      UNINHABITED
ERDOS287:                   OPEN
FIRST FORMAL RESEARCH SOCKET:
                            the master-source → typed-Perron-packets reconstruction
PROOF CLAIM CERTIFIED:      NO
STOP.
```

Every audited new declaration reports `[propext, Classical.choice, Quot.sound]`, a subset of
it, or no axioms at all.  Scans of the new code found no `sorry`, `sorryAx`, `admit`,
`axiom`, `unsafe`, `opaque`, `native_decide` or `implemented_by`.
