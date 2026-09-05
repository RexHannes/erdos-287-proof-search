# Erdős Problem #287 — Authoritative Current Status

**Checkpoint:** 5 September 2026  
**Global verdict:** **OPEN — no solution claimed.**

This file separates the **audited mathematical baseline** from the **current source-minimal proof-search route**. A newer dependency reassembly can change which theorem is strategically controlling without promoting unaudited subresults into the bank.

## 1. Thirty-second status

```text
AUDITED BASELINE:
    R12 effectivity synthesis — 5 Sep 2026

AUDITED SUBTOTAL:
    5.257263872e-7

AUDITED REMAINING CAPACITY:
    3.603386128e-7

CURRENT LIVE PHYSICAL PARENT:
    R_012 = signed (j=0 + j=1 + active j=2)
    OPEN

NEXT DOWNSTREAM:
    signed floor              OPEN
    Maynard effectivization   NOT ENTERED
    finite/asymptotic splice NOT ENTERED

ERDŐS #287:
    OPEN
```

## 2. Banked foundation

The current trusted bank retains, at each result's stated evidence scope:

- physical `B_src` normalization;
- corrected odd half-divisor algebra;
- exact `c=1/c=2` reflection/splice;
- full unselected `Z(s,s)=0` at the scope stated in the audited bank;
- Perron algebra / variable change, without conflating it with the open directed truncation estimate;
- complete `V<1000` finite edge closure;
- complete-period endpoint/Farey covariance main;
- exact R12 capacity arithmetic and finite certificates.

See [`banked/`](banked/) for the evidence-class index and [`paper/audited-release/2026-09-05-r12/`](paper/audited-release/2026-09-05-r12/) for the latest independently audited synthesis.

## 3. Current proof-search parent

The latest source reassembly is

```text
corrected selector Γ
    |
    +-- j>=4      CANDIDATE-EMPTY
    +-- j=3       CANDIDATE-CLOSED, reported |R_3| < 3e-9 B_X
    |
    +-- j=0
    +-- j=1
    +-- active j=2
            |
            v
          R_012
            OPEN
```

The active `j=2` census is reduced to

```text
c=1: 71 prefix families
c=2: 37 prefix families.
```

The current hard content inside `R_012` is concentrated in:

```text
complete low-divisor fibres      cancellation available in current chart
incomplete low-divisor fibres    OPEN
rough defect                     OPEN
selector-sensitive Perron        OPEN at the required directed estimate
large ratio-frequency decay      OPEN
active j=2 finite source census  71 + 37 families
```

`j>=4` and `j=3` are newer candidate reductions and are **not promoted into R12** merely by appearing here. See [`frontier/current-parent/`](frontier/current-parent/) and [`frontier/candidate-results/`](frontier/candidate-results/).

## 4. What happened to medium-k and the old covariance chain?

The audited R12 checkpoint correctly recorded

```text
C_F + 2 C_ED + C_DD + C_S < 283/37500
```

as a sufficient weighted covariance residual and recorded medium-`k` as strictly reduced/open.

Later source work reassembled the physical source so that

```text
F / ED / DD / S,
all-q discrepancy,
Ramanujan charts,
medium-k,
two-high
```

are no longer required as a linear sequence of independent gates. In particular:

```text
medium-k is RETIRED AS AN INDEPENDENT SEQUENTIAL NODE,
not declared globally proved.
```

Its mathematics is absorbed into the signed selector parent and can still appear as a local coordinate or diagnostic subproblem. This distinction is recorded under [`graveyard/superseded/`](graveyard/superseded/).

## 5. Selected diagonal zero

The full unselected identity `Z(s,s)=0` remains banked at its stated scope. The active selector produces a live defect

```text
Z_{Theta,c}(s,s) = -H_c(s).
```

A candidate auxiliary completion `Ztilde_c = Z_{Theta,c}+H_c` restores the diagonal zero, with reported finite-height correction `<2.4e-13 B_X`. This does **not** prove the remaining large ratio-frequency / incomplete-fibre estimate. The selected repair remains candidate until audit.

## 6. Downstream entry guards

```text
R_012 signed parent             OPEN
        |
        v
signed floor                    OPEN
        |
        v
Maynard effectivization         NOT ENTERED
        |
        v
finite / asymptotic splice      NOT ENTERED
        |
        v
Erdős #287                      OPEN
```

No downstream stage is considered entered merely because a structural compiler or finite bank already exists.

## 7. Evidence and strategy firewall

Use these categories precisely:

```text
BANKED      trusted result at stated evidence scope
CANDIDATE   substantial new result awaiting independent audit
OPEN        current missing theorem / estimate / instantiation
RETIRED     do not use as controlling route; not necessarily false
SUPERSEDED  older coordinate replaced by a better parent
FALSE       explicit counterexample / retraction
```

The audited R12 numbers remain the public quantitative baseline until a later audit explicitly replaces them. New proof-search recompilations change the dependency graph, not the historical truth of the R12 checkpoint.

## 8. Read next

- [`PROOF_MAP.md`](PROOF_MAP.md) — canonical dependency map;
- [`CLAIMS_LEDGER.md`](CLAIMS_LEDGER.md) — claim/evidence/status matrix;
- [`banked/`](banked/) — trusted inputs;
- [`frontier/`](frontier/) — live parent, candidates, downstream;
- [`graveyard/`](graveyard/) — false, retired, superseded routes;
- [`archive/`](archive/) — historical material, preserved rather than deleted.

**ERDŐS PROBLEM #287 REMAINS OPEN.**
