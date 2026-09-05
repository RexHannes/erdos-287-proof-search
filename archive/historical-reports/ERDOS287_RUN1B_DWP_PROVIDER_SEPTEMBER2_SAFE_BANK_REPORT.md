# RUN1B d*wp provider / neutral shared Ford layer / September-2 Erdős-287 frontier — safe bank report

All work is **append-only**.  No historical file, theorem or status layer was deleted or
rewritten.  **Erdős #287 is not claimed.  The twin-prime conjecture is not claimed.  No
paper-level analytic theorem was turned into an axiom or into a disguised structure-field
proof.**

## Files added

**RUN1B `d·w'` provider (project-neutral namespace `Run1B`)**

| file | content |
|---|---|
| `RequestProject/CurrentProgramme/Run1BAdditiveCharacters.lean` | `e_r(x) = exp(2πi x/r)`: character law, `e_r(x)=1 ↔ r ∣ x`, congruence invariance, `e_r(x)^r = 1`, conjugation, `‖e_r(x)‖ = 1`, and the exact **unnormalised** finite orthogonality `∑_{u<r} e_r(a u) = r·[r ∣ a]`. |
| `Run1BDwpSourceType.lean` | the source-exact record `DwpSource` (`q = d·w'`, `α_d`, `β_{w'}`, `r`, `A`) with literal hypotheses `gcd(d,r)=gcd(w',r)=1`, dyadic `D`,`W` ranges, `Q ≤ DW ≤ 4Q`, `D,W ≥ x^{1/3−ε}`, `Q ≥ x^{13/18−ε}`, `r ≤ x^{1/2+ε}`; the literal bilinear sum; an explicit inhabitant; and the counterguard that **no analytic inequality is a field of the record**. |
| `Run1BEffectiveModulus.lean` | `s = gcd(A,r)`, `r♯ = r/s`, `A♯ = A/s`; `gcd(A♯,r♯)=1`; the exact identity `e_r(A t) = e_{r♯}(A♯ t)`; inverse descent; and the requested identity `e_r(A u⁻¹) = e_{r♯}(A♯ u⁻¹)`. |
| `Run1BFiniteFourierMatrix.lean` | `K(u,v) = e_{r♯}(−A♯uv)`; row/column relabelling; multiplication by an invertible `A♯` is a permutation of `ZMod r♯` and of the sum; exact finite orthogonality; `∑_v ‖(Kx)(v)‖² = r♯ ∑_u ‖x(u)‖²`, i.e. **operator norm exactly `√r♯`** in the stated unnormalised convention, plus a counterguard that the normalisation is not hidden. |
| `Run1BResidueClassEnergy.lean` | residue-class multiplicity `#{d < D : d ≡ c} ≤ 1 + D/r♯` (also for any support in `[0,D)`); inverse-residue pushforwards and the `ℓ²`-invariance of inversion; the finite `L²` bilinear inequality `|S| ≤ √r♯ ‖X‖₂‖Y‖₂`. |
| `Run1BLargeModulusCompiler.lean` | the algebraic large-`r♯` compiler: energy bounds + `L²` bound ⟹ `S² ≤ (r♯+D)(r♯+W)/r♯ · E_X E_Y`; counterguard that this is **not** a log-saving. |
| `Run1BSmallModulusFourier.lean` | finite Fourier inversion, Parseval, `L¹ ≤ √r♯ L²`; the periodic reciprocal phase `u ↦ e_{r♯}(A u⁻¹)` and its expansion; the **`PAPER_CLOSED_EXTERNAL`** `MobiusPolynomialPhaseInput` (never proved, shown to be a genuine constraint) and the conditional compiler from it to the small-modulus estimate. |
| `Run1BCenteringAndSourceRouter.lean` | `h = 0` cancellation for the centred weight, exact retention of the principal term (nothing is deleted), the Ramanujan coefficient identity at a prime modulus; the seven-class source router with totality, exhaustiveness, pairwise distinctness, surjectivity and the firewall that routing ignores analytic fields. |
| `Run1BConditionalCompiler.lean` | `Run1BSourceExhaustiveInput` (finite, **inhabited**, kernel-proved) kept separate from `PhysicalQMuPrimeReciprocalPaperInput` (**paper-closed external**, uninhabited here) and `CenteringLocalInput`; the conditional compiler to `Run1BConclusion`, plus the counterguard that the finite input alone does not give the conclusion. |

**Neutral shared Ford layer and adapters**

| file | content |
|---|---|
| `NeutralFordSharedOtherParent.lean` | project-neutral `SharedFord` namespace: the other-parent source object and covariance; the two ultra source subclasses (cross-block / same-block prime pair) with exhaustiveness; the **open external** `UltraNearHalfCovarianceInput`; the conditional shared other-parent conclusion from ultra + RUN1B; the two mutually independent adapters `TwinOtherParentAdapter`, `Erdos287HardUAdapter`; the `Erdos287HardUSharedFordAdapterInput` whose obligation is **source equality only**, with the firewall that label/name agreement never discharges it. |

**Erdős-287 frontier bank and status**

| file | content |
|---|---|
| `Erdos287N2EffectiveConstantsBank.lean` | banked constants `C_2LF = 1078`, `C_ps = 3`, `C_Bps = 25`, `K_collar ≤ 107222726423465`, `ε = 1/2·10²¹`, `X_N2 = ⌈exp(2·10²²)⌉`; kernel-proved `¬(2·X_N2 ≤ 4·10⁹)` and `4·10⁹ < X_N2`, i.e. the finite splice **fails** for the current constants; the `Ω_H` provenance firewall (`unresolved`, no silent default). |
| `RequestProject/Status/CurrentStatusErdos287September2Frontier.lean` | the latest authoritative status layer with the seven-value vocabulary, the b-diagonal hostile downgrade, the exact dependency graph, the Gate-1A exclusion, the retention of every open node, and the honest high-assurance validation record. |
| `RequestProject/Status/AxiomAuditErdos287September2Frontier.lean` | `#print axioms` on all 98 principal new declarations. |

`RequestProject/Main.lean` gained the thirteen corresponding imports.

## Strict final output (RUN1B / d*wp bank)

```
LAKE BUILD:                        PASS  (8404 jobs)
NEW WARNINGS:                      NONE in the new modules
                                   (5 pre-existing, documented, intentional remain)
EFFECTIVE MODULUS IDENTITY:        KERNEL-PROVED
FOURIER MATRIX ORTHOGONALITY:      KERNEL-PROVED  (unnormalised; diagonal value r♯)
LARGE-rSharp COMPILER:             CONDITIONAL KERNEL-PROVED
SMALL-rSharp FOURIER:              KERNEL-PROVED  (inversion, Parseval, L¹ ≤ √r♯ L²)
MOBIUS POLYPHASE INPUT:            PAPER-CLOSED EXTERNAL  (uninhabited, genuine constraint)
d*wp PROVIDER:                     PAPER-CLOSED EXTERNAL  (uninhabited, genuine constraint)
RUN1B SOURCE EXHAUSTIVE INPUT:     INHABITED  (finite routing, kernel-proved)
RUN1B FINAL STATUS:                PAPER-CLOSED EXTERNAL, subject to source-exhaustiveness audit
ULTRA-NEAR-HALF:                   OPEN EXTERNAL
SHARED OTHER:                      CONDITIONAL
TWIN ADAPTER:                      CONDITIONAL  (downstream conclusion never inhabited)
ERDOS287 ADAPTER:                  CONDITIONAL  (source-equality obligation UNINHABITED)
TWIN PRIME:                        OPEN
ERDOS287:                          OPEN
SEMANTIC FAILURES:                 NONE FOUND
                                   (source record carries no conclusion field; every
                                    external estimate stays an explicit hypothesis;
                                    routing shown analytics-independent; no True-like input)
CUSTOM AXIOM:                      NONE
SORRYAX:                           NONE
OVERCLAIM AUDIT:                   PASS
```

## Strict final output (September-2 Erdős-287 frontier)

```
LATEST STATUS LAYER:               PASS  (CurrentStatusErdos287September2Frontier)
FINITE BANK:                       KERNEL BANKED, M ≤ 4·10⁹, unchanged and not weakened
E_T:                               PAPER-CLOSED EXTERNAL
E_2 ASYMPTOTIC:                    PAPER-CLOSED EXTERNAL
E_2 EFFECTIVE:                     PAPER-CLOSED EXTERNAL, enormous threshold
N2 SPLICE:                         FAIL  (kernel-proved: ¬(2·X_N2 ≤ 4·10⁹))
BSRC/N1/E_M:                       PAPER-CLOSED EXTERNAL
RUN1B SHARED PROVIDER:             PAPER-CLOSED EXTERNAL, in the neutral shared Ford layer
ULTRA-NEAR-HALF:                   OPEN EXTERNAL
#287 HARD-U ADAPTER:               UNINHABITED  (source-equality obligation only)
E_L:                               OPEN / CONDITIONAL
BDIAGONAL:                         STRICTLY REDUCED / OPEN  (hostile downgrade recorded)
PERRON LEDGER:                     OPEN
RECTANGLE PIN:                     OPEN
OMEGA_H:                           UNRESOLVED  (no silent default; kernel-proved)
ASYMPTOTIC FCL:                    OPEN / CONDITIONAL
FCL->WINDOWPAIR:                   CONDITIONAL KERNEL-PROVED (M ≥ 12, unchanged)
GLOBAL EFFECTIVITY:                OPEN
M0<=4e9:                           NOT PROVED
GATE1A ON #287 CRITICAL PATH:      NO  (absent from every antecedent list; kernel-proved)
LEAN SEMANTIC FAILURES:            NONE FOUND
LEAN4CHECKER:                      NOT RUN
COMPARATOR:                        NOT RUN
EXTERNAL CHECKER:                  NOT RUN
ERDOS287:                          OPEN
FIRST MATHEMATICAL RESIDUAL:       the ultra-near-half covariance (FM722-OTHERPARENT-COARSE2-
                                   TWOPRIME-ULTRANEARHALF-ANCHOR2-COVARIANCE45)
FIRST SOURCE/COMPILER RESIDUAL:    Erdos287HardUSharedFordAdapterInput — literal source
                                   equality of the hard-U generated packets with the neutral
                                   shared Ford other-parent source
FIRST EFFECTIVITY RESIDUAL:        the global FCL threshold; the banked N2 splice fails
FIRST FORMAL RESIDUAL:             the b-diagonal hostile-audit obligations (Perron nuclear
                                   ledger, rectangle pin, Ω_H provenance, short-edge owner
                                   completeness, source coprimalities)
OVERCLAIM AUDIT:                   PASS
```

STOP.
