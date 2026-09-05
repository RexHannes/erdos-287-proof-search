# Erdős #287 — 287A / shared-other45 addendum, append-only safe bank

All work is **append-only**.  No historical file was deleted or rewritten.
No external analytic theorem was proved.  No source/analytic socket was inhabited.
**Erdős #287 is not claimed.**

## Files added in this pass

| File | Content |
|---|---|
| `RequestProject/CurrentProgramme/Erdos287TwoLaneMasterCompilerV2.lean` | V2 two-lane master compiler socket, paper-closed N2 λ-collar and Bsrc/N1 inputs, conditional asymptotic FCL, explicit thresholds, end-to-end chain |
| `RequestProject/CurrentProgramme/Erdos287HeathBrownSourceRecords.lean` | Heath-Brown source records and the majorant firewall |
| `RequestProject/CurrentProgramme/Erdos287N2FiniteSublemmas.lean` | Finite `N2` sublemmas (`Ω ≤ 6`, subvector expansion, root counts) |
| `RequestProject/CurrentProgramme/Erdos287SharedOtherRawArchitecture.lean` | §1–§8: dependent raw packet, Tot exclusion firewall, deterministic `E*`, `A_η`/`B_η`, determinant line, centred two-copy identity, coefficient preservation |
| `RequestProject/CurrentProgramme/Erdos287SharedOtherConductorAndSocket.lean` | §9–§14: proof-local conductor/shared-gcd data, Δ-router, Ford-7.22 generated-uniformity socket with census metadata, `k = 0` `β_g` firewall |
| `RequestProject/CurrentProgramme/Erdos287SharedOtherAdaptersAndCompiler.lean` | §3, §15–§16: Tot census reconstruction, Type-I `o(X/log X)` socket, `E_L` compiler, two independent adapters, conditional asymptotic FCL |
| `RequestProject/Status/CurrentStatusErdos287TwoLaneFCLFrontier.lean` | Two-lane FCL status layer (index 4) |
| `RequestProject/Status/AxiomAuditErdos287TwoLaneFCLFrontier.lean` | Axiom audit for that layer |
| `RequestProject/Status/CurrentStatusErdos287SharedOtherFrontier.lean` | §17: 287A / shared-other45 status layer (index 5) |
| `RequestProject/Status/AxiomAuditErdos287SharedOtherFrontier.lean` | §18: axiom audit for that layer |

`RequestProject/Main.lean` gained the corresponding imports (append-only).

## Leanify / repair pass

Twenty-eight pre-existing linter warnings were repaired at the root (unused `simp`
arguments removed, one unused hypothesis removed from `topExp_le_one_of_lt_sq`, two unused
lambda binders replaced by `_`).  No linter was disabled and no `nolint` was added.
The five remaining warnings are the deliberately kept, docstring-documented hypotheses that
the original problem statements request but the proofs do not need
(`Window.hqM`, `RoughPrime.hℓ2`, `GoodPrime.hhalf`, `CeilingCRT.hx`/`x`).

## Point-by-point

1. **Dependent raw packet** — `RawPacket X = RawDataTot X ⊕ RawDataU X`;
   `rawPacket_is_a_two_lane_sum`, `rawPacket_lanes_are_disjoint`.
2. **Tot constructor exclusion** — `tot_constructor_excludes_forbidden_fields` (no `k`, `J`,
   HB leaves, `𝓔`, `E*`, shared `gcd`, `Δ`) and the semantic
   `tot_datum_is_determined_by_its_listed_fields`.
3. **Tot reconstruction / Type-I** — `raw_census_union/_disjoint/_card`,
   `tot_reconstruction_finite`, `totCensus_carries_no_U_datum`.  The Type-I estimate is the
   explicit `TypeIEstimatePaperInput` whose conclusion is `IsLittleOXOverLogX`;
   `E_T_bound_of_typeI` is the only route to an `E_T` bound and consumes it.
   `littleO_is_a_genuine_constraint` shows the conclusion is not automatic.
4. **U constructor** — `RawDataU` carries exactly `k`, `J`, the literal HB grammar, `𝓔`, the
   deterministic `E* = E*(𝓔)`, the `u`/`v` source, the dyadic/Perron skeleton and the source
   signs; `EStar_is_deterministic`.
5. **Generated coefficients** — `A_eta`, `B_eta`, with support and dependence lemmas.
6. **Determinant line** — `determinant_line_invariant`, `determinant_line_forward`,
   `determinant_line_converse`, `census_determinant_line`.
7. **Centred two-copy identity** — `centred_two_copy_identity`, `centred_two_copy_normSq`,
   `centred_two_copy_is_not_the_uncentred_square`.
8. **Coefficient preservation** — `coefficient_preservation`,
   `coefficient_preservation_diagonal`.
9. **Proof-local conductor data** — `SharedConductorData`, indexed by two copies, with
   `q_factorisations`, `reduced_factors_coprime`, `Delta`,
   `Delta_is_a_genuine_two_copy_object`.
10. **Δ-router** — `deltaRoute` with the three exact biconditionals,
    `deltaRoute_exists_unique` and `deltaRoute_is_routing_only`.
11. **Owner analytic structures not inhabited** —
    `Ford722OtherParentGeneratedUniformityInput` is left uninhabited;
    `ford722_socket_is_a_genuine_constraint` and `ford722_socket_needs_k_at_least_one`.
12. **Generated contract, not the `k = 0` `β_g` profile** —
    `betaG_profile_does_not_determine_the_generated_coefficients`.
13. **Census metadata** — carried literally as fields and read out by
    `ford722_census_metadata`.
14. **Analytic covariance uninhabited** — yes; only counterguards are proved.
15. **Two independent adapters** — `TwinOtherParentAdapter` (parametric in the other
    project's conclusion, never inhabited here) and `Erdos287HardUAdapter`
    (`erdos287HardUAdapter_holds`); `adapters_are_independent`.
16. **Conditional #287 compiler** — `E_L_bound_of_sharedOtherParent` and
    `asymptoticFCL_of_shared_other_parent`.
17. **Status** — `Erdos287.SharedOtherFrontierStatus.sharedOtherLedger`.
18. **Audit** — see below.
19. **No external statement called kernel-proved** —
    `paperClosedExternal_is_not_kernelProved` is kernel-checked.

## Strict final output

```
LAKE BUILD:                 PASS
JOB COUNT:                  8391
NEW WARNINGS:               NONE  (28 pre-existing warnings repaired; 5 documented
                                   intentional-hypothesis warnings remain)
SORRYAX:                    NONE
CUSTOM AXIOM:               NONE
AXIOMS OBSERVED:            propext, Classical.choice, Quot.sound  (and subsets)
DEPENDENT RAW PACKET:       PASS
TOT EXCLUSION FIREWALL:     PASS
DETERMINANT LINE:           KERNEL-PROVED
CENTRED TWO-COPY IDENTITY:  KERNEL-PROVED
COEFFICIENT PRESERVATION:   KERNEL-PROVED
CONDUCTOR / SHARED-gcd:     KERNEL-PROVED
DELTA ROUTER:               KERNEL-PROVED (routing only)
TYPE-I E_T SOCKET:          PAPER-CLOSED EXTERNAL / UNINHABITED
N2 LAMBDA-COLLAR SOCKET:    PAPER-CLOSED EXTERNAL / UNINHABITED
BSRC / N1 / E_M SOCKET:     PAPER-CLOSED EXTERNAL / UNINHABITED
FORD 7.22 HARD-U SOCKET:    OPEN EXTERNAL / UNINHABITED
POSITIVE MARGIN SOCKET:     UNINHABITED
E_L COMPILER:               KERNEL-PROVED CONDITIONAL
TWO ADAPTERS:               KERNEL-PROVED, MUTUALLY INDEPENDENT
ASYMPTOTIC FCL:             KERNEL-PROVED CONDITIONAL
EFFECTIVITY SOCKET:         UNINHABITED
Erdos287ClosureInputs:      UNINHABITED
ERDOS287:                   OPEN
FIRST FORMAL RESEARCH SOCKET:
                            Erdos287.SharedOtherParent.Ford722OtherParentGeneratedUniformityInput
PROOF CLAIM CERTIFIED:      NO
```

STOP.
