# Reviewer Dependency Graph

The canonical public theorem map is [`../PROOF_MAP.md`](../PROOF_MAP.md). This file shows how **evidence ownership** and the **live proof-search dependency** fit together without conflating them.

## Evidence layer

```text
finite / formal bank
    RequestProject/
          |
          +-----------------------------+
                                        |
source-exact algebra / analytic bank    |
    banked/                             |
          |                             |
          +-----------------------------+
                                        v
R12 audited effectivity release --> audited quantitative baseline
    paper/audited-release/          subtotal 5.257263872e-7
                                    remaining 3.603386128e-7
```

R12 remains the latest independently audited numerical checkpoint. Its weighted covariance residual is a valid sufficient chart and is not erased by later proof-search work.

## Live dependency layer

Later source reassembly shortens the strategic DAG:

```text
banked source / algebra
        |
        v
corrected selector Γ
        |
        +-- j>=4   candidate-empty
        +-- j=3    candidate-closed, reported <3e-9 B_X
        |
        v
R_012 = signed (j=0 + j=1 + active j=2)
        OPEN
        |
        +-- incomplete fibres                 OPEN
        +-- rough defect                      OPEN
        +-- selected Perron / ratio decay     OPEN
        +-- active j=2                        71 + 37 prefixes
        |
        v
signed floor                                  OPEN
        |
        v
Maynard effectivization                       NOT ENTERED
        |
        v
finite / asymptotic splice                    NOT ENTERED
        |
        v
Erdős #287                                    OPEN
```

## Why this does not contradict R12

R12 used the coordinate chart

\[
C_F+2C_{ED}+C_{DD}+C_S<\frac{283}{37500}
\]

as a sufficient residual and recorded medium-`k` as strictly reduced/open. Later transformations show that `F/ED/DD/S`, all-`q`, Ramanujan, medium-sector, and higher-selector terms are better treated as coordinates or sibling pieces of one signed physical parent.

Thus the current source-minimal graph **supersedes the requirement that those nodes be proved sequentially**. It does not retroactively certify the old residual or promote unaudited candidate reductions into the bank.

## Reviewer rule

For theoremhood and numerical constants, audit the evidence path under `banked/` and the R12 release. For the question “what theorem must be proved next?”, follow `frontier/current-parent/`. For dead or obsolete routes, consult `graveyard/` before reopening anything.
