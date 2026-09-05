# Dependency Graph

The canonical public dependency graph is [`../PROOF_MAP.md`](../PROOF_MAP.md). This file supplies the reviewer-oriented evidence routing beneath that map.

```text
Problem statement
    |
    +--> finite exact / formal bank --------------------+
    |        RequestProject/                            |
    |                                                   |
    +--> source + asymptotic reductions                 |
    |        paper/formal modules                       |
    |                                                   v
    +--> R12 effectivity synthesis ----------------> audited capacity ledger
             |                                          |
             +--> V<1000 certificate                    |
             +--> complete-period endpoint              |
             +--> aggregate conditional compiler        |
                                                        v
                                         remaining weighted covariance
                                                        |
                                                        v
                                                   medium-k OPEN
                                                        |
                                +-----------------------+------------------+
                                v                       v                  v
                            two-high              signed floor          Maynard
                           NOT ENTERED                OPEN             NOT ENTERED
                                \_______________________|__________________/
                                                        |
                                                        v
                                               Erdős #287 OPEN
```

## Current audited residual

The R12 route requires

\[
C_F+2C_{ED}+C_{DD}+C_S<\frac{283}{37500}.
\]

The full physical `lambda(b)` weight belongs to this node. No downstream node should be displayed as closed while this audited residual remains open.

## Candidate overlay

The current live candidate work does **not** replace the DAG above. It overlays the medium/effectivity region with a proposed static Ramanujan freeze:

```text
primitive/static r <= 200     candidate-closed
moving Ramanujan window        candidate-removed
static signed r > 200 tail     OPEN
```

This overlay becomes part of the audited graph only after independent replay and ledger reconciliation.
