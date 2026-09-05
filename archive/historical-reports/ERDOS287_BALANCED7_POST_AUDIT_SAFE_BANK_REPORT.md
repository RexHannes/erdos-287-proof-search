# Erdős #287 — Balanced7 post-audit safe bank / repair compiler

Append-only continuation of the existing repository.  No historical V20 / V21 / V22 / SP-2 /
V23 / V24 bank was modified, no historical status row was deleted or rewritten, and
`ARISTOTLE_SUMMARY.md` was not touched.  All new material lives in

```
RequestProject/CurrentProgramme/
RequestProject/Status/CurrentStatusErdos287Balanced7Repair.lean
RequestProject/Status/AxiomAuditErdos287Balanced7Repair.lean
```

`RequestProject/Main.lean` was extended with import lines only.

Note on the brief: this repository has no `TwinPrimeProject.CurrentProgramme` namespace, no
`CurrentStatus.lean`, and no `ERDOS287_CURRENT_RESEARCH_LEDGER_2026-08-29.md`; the existing
convention is the `Erdos287.*` namespace with per-pass `Status/…Status.lean` modules, so the
new layer follows that convention under `Erdos287.CurrentProgramme` and
`Erdos287.Balanced7RepairStatus`.  Nothing from an August-29 Gate1B append-only module was
duplicated (the repository contains `Challenges/Gate1B_SourceOpenedSWYang.lean` and
`TrustedBank/Gate1B/*`, which are untouched).

## Files added

| file | content |
|---|---|
| `RequestProject/CurrentProgramme/LogRRepairBank.lean` | source-minimal identity `Λ(n) = ∑_{qr=n} μ(q) log r` (and its affine specialisation at `2P+s`); `C_ext = 0` retraction record; `C_ext = 1`; `C_var = 5`, `C_var − 2C_ext = 3 > 0`; firewall that the exponent ledger yields no analytic theorem |
| `RequestProject/CurrentProgramme/EulerUniformityFirewall.lean` | literal full-`q` principal sum `J_P(z)`, its exact split at any cutoff, the firewall that a full-`q` identity may not be assigned to one cell, uninhabited full-`q` Euler socket with `H_P(0) = 2B(P)` and contour metadata |
| `RequestProject/CurrentProgramme/ExactQRPartition.lean` | exact `SmallQ / SmallR / Hard` predicates at a cutoff `U`: cover, pairwise disjointness, unique sharp ownership, exact sum and cardinality reassembly, `U² < N` sharpness, `q ↔ r` non-symmetry |
| `RequestProject/CurrentProgramme/ThreePlusFourProductAlgebra.lean` | labelled `k`-fold convolutions `a₃`, `b₄` with **no injectivity assumption**; exact fibrewise multiplicity and energy identities; collision/Cauchy bound `∑|a|² ≤ repMult · ∏ energy`; explicit repeated-prime and multiplicity ≥ 2 witnesses; uninhabited prime-density socket for the asymptotic targets |
| `RequestProject/CurrentProgramme/SmallQ34LSRoute.lean` | source-mismatch theorems (`q ∣ 2P+s`, not `P`), routing record superseding the Type-I adapter as controlling frontier, uninhabited `BalancedSevenSmallQ34LSInput` with all literal obligations, conditional consumer |
| `RequestProject/CurrentProgramme/ImprimitiveConductorBookkeeping.lean` | explicit replacement for `C_ind`: conductor divides level, `μ(q) ≠ 0 ⇒ q` squarefree, lifts ≤ `d(q)`, `q/φ(q) ≥ 1`, vanishing on non-units, `ConductorRecord`, uninhabited total-cost socket |
| `RequestProject/CurrentProgramme/SmallROwnerSubtraction.lean` | `S_sr = D_sr + M_sr_prin` (unconditional), uniqueness of the defect, `|D_sr| ≤ E₁+E₂` and the reverse reassembly, uninhabited SmallR defect analytic socket |
| `RequestProject/CurrentProgramme/HardThetaDelta.lean` | `1/3 − 2/7 = 5/7 − 2/3 = 1/21`, `(1/21)/20 = 1/420`; for the literal real powers `T = X^{5/7−θ}`, `z = T^{1/20}`: `log z = (1/20)(5/7−θ) log X`, `log z ≥ (1/420) log X`, `1/log z ≤ 420/log X`, and the `1/log z → O(1/log X)` compiler; open-interval `(2/7, 5/7)` has no uniform `δ` |
| `RequestProject/CurrentProgramme/ShortTShiuSockets.lean` | uninhabited `BalancedSevenShortTSieveInput` stated with `1/log z` (not `1/log X`), its physical-range consumer via `δ = 1/21`, `log z < log X`; uninhabited `BalancedSevenShiuInput` on the literal affine sequence `2w'm + s` |
| `RequestProject/CurrentProgramme/OwnerMap.lean` | finite owner/cell types, the mandated owner map, unique ownership, disjoint accounts, `no_double_spending` (owners' accounts reassemble the total exactly), Euler principal account = the three principal cells |
| `RequestProject/CurrentProgramme/PostAuditFullQCompiler.lean` | `BalancedSevenPostAuditInputs → BalancedSevenAsymptoticConclusion`, proved purely logically; the bundle is refutable and is **not** constructed |
| `RequestProject/Status/CurrentStatusErdos287Balanced7Repair.lean` | append-only ledger with `no_closed_rows`, `ledger_is_honest`, `erdos287_open`, `balanced7_open`, `first_residual_is_smallq_34LS_normalisation`, the effectivity firewall and the downstream firewall |
| `RequestProject/Status/AxiomAuditErdos287Balanced7Repair.lean` | `#print axioms` for every principal new declaration |

## Status rows (new ledger)

```
BALANCED7-EULER-UNIFORMITY45              : externallyAudited
C-EXT-LOGR-REPAIR45                       : provedAlgebraic
BALANCED7-QPACKET-STRUCTURAL-PARTITION45  : provedFinite
AFFINE287-SP2-SMALLQ-TYPEI-ADAPTER45      : supersededAsControllingFrontier
AFFINE287-SP2-SMALLQ-34LS-NORMALIZATION45 : sourceOpen        (residual rank 1)
AFFINE287-SP2-SMALLR-OWNER-SUBTRACTION45  : provedAlgebraic
HARD-THETA-PHYSICAL-DELTA45               : provedAlgebraic   (rational/capacity only)
BALANCED7-SHORTT-SIEVE45                  : analyticOpen
BALANCED7-SHIU45                          : analyticOpen      (conservative)
IMPRIMITIVE-CONDUCTOR-BOOKKEEPING45       : sourceOpen
3+4 FINITE ALGEBRA                        : provedFinite
ALL-Q-NO-DOUBLE-SPENDING45                : conditionalCompiler
SP2-BALANCED7-FULL-Q45                    : conditionalCompiler
BALANCED7                                 : open_
287-EFFECTIVE-POLYLOG-MODULUS-REPLACEMENT45 : analyticOpen
287-K0-SP2-UNIFORM-FRAGMENTATION-REASSEMBLY45 : notActivated
FCL                                       : open_
ERDOS287                                  : open_
```

`no_closed_rows` is a kernel-checked theorem about this ledger.  The historical research
claim `BALANCED7 : CLOSED` remains visible in the historical reports and is not controlling.

## Final block

```
C_ext:
    1

EULER UNIFORMITY:
    RESEARCH PASS / formal status: externallyAudited, carried by an
    uninhabited full-q socket; only H_P(0) = 2B(P) is an internal theorem

OLD SMALL-q TYPE-I ROUTE:
    SUPERSEDED / SOURCE MISMATCH (q | 2P+s, not P); not refuted

FIRST EXACT RESIDUAL:
    AFFINE287-SP2-SMALLQ-34LS-NORMALIZATION45

SMALL-r OWNER SUBTRACTION:
    LEAN_PROVED ALGEBRAIC/FINITE COMPILER
    (S_sr = D_sr + M_sr_prin unconditional; |D_sr| <= E1 + E2 conditional)

HARD delta:
    1/21   (log z >= (1/420) log X, 1/log z <= 420/log X, both proved)

SHORT-t SIEVE:
    EXTERNAL / OPEN   (socket stated in 1/log z, never 1/log X)

SHIU:
    EXTERNAL / OPEN, conservatively analyticOpen; literal affine
    sequence 2 w' m + s recorded

NO DOUBLE-SPENDING:
    finite owner compiler proved; the full-q consequence stays CONDITIONAL / OPEN

BALANCED7:
    OPEN — NARROW REPAIR

EFFECTIVE BALANCED7:
    OPEN   (effectivity_firewall: no asymptotic -> computable M0)

FCL:
    OPEN

ERDOS287:
    OPEN

LAKE BUILD:
    lake build succeeds — 8203 jobs, 0 errors, 0 warnings in the new files

TRUST SCAN:
    zero occurrences of sorry, admit, axiom, opaque, unsafe, native_decide
    or @[implemented_by] in the new files; #print axioms on every principal
    new declaration reports only propext / Classical.choice / Quot.sound;
    no source or analytic interface is inhabited
```

## FINAL FIREWALL

```
Research audit metadata is not Lean proof.
The old Type-I residual is superseded by the 3+4 large-sieve route.
The remaining SmallQ obligation is coefficient/source normalization,
not exponent capacity.
The hard physical theta range survives with the delta=1/21 repair.
Balanced7 remains OPEN until exact owner reassembly and a fresh hostile
audit pass.
Erdős #287 remains OPEN.
```
