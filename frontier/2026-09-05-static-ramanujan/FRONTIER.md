# Live Candidate Frontier — Static Ramanujan Signed Tail

**Date:** 5 September 2026  
**Evidence class:** **LIVE CANDIDATE / NOT YET INDEPENDENTLY AUDITED**  
**Global verdict:** **Erdős Problem #287 remains OPEN.**

This file records the latest research-session snapshot separately from the R12 audited release. Nothing in this file changes the audited R12 capacity ledger until an independent audit promotes it.

## Candidate ledger

```text
Audited R12 subtotal:               5.257263872e-7
Audited R12 remaining capacity:     3.603386128e-7

Candidate subtotal:                 6.341463872e-7
Candidate remaining global capacity:2.519186128e-7
```

The second pair is **candidate-only**.

## Candidate reduction

```text
primitive/static r <= 200:
    CANDIDATE-CLOSED
    independent audit pending

moving Ramanujan window:
    CANDIDATE-REMOVED / SUPERSEDED

static signed r > 200 tail:
    OPEN — controlling live candidate residual
```

The live research direction freezes the relevant Ramanujan coefficient structure rather than paying again for a moving-window formulation. The exact physical signed tail above `r=200` remains the point requiring proof.

## Downstream state

```text
medium-k:
    STRICTLY REDUCED / OPEN

two-high:
    NOT ENTERED

signed floor:
    OPEN

Maynard effectivization:
    NOT ENTERED

Erdős #287:
    OPEN
```

## Promotion rule

Before any candidate closure or candidate capacity is moved into `CURRENT_STATUS.md` as an audited fact, it should receive:

1. an exact source/dictionary check;
2. a numerical/certificate replay where applicable;
3. an independent hostile audit of constants and double-counting;
4. a reconciliation against the R12 exact directed ledger;
5. an update to `CLAIMS_LEDGER.md` identifying the new audited owner.

Until then, the audited baseline remains R12.
