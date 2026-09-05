# Erdős Problem #287 — Current Status

**Checkpoint:** 5 September 2026  
**Global verdict:** **OPEN — no solution claimed.**

This is the concise public status file. It distinguishes the **latest audited baseline** from newer **live candidate research**. Where a candidate snapshot and an audited release differ, the audited release controls until a later independent audit promotes the candidate result.

## 1. Audited baseline — R12 effectivity synthesis

The current independently audited release is:

[`paper/audited-release/2026-09-05-r12/README.md`](paper/audited-release/2026-09-05-r12/README.md)

Its exact directed capacity ledger is

```text
AUDITED TARGET:       8.860650000e-7
AUDITED SUBTOTAL:     5.257263872e-7
AUDITED REMAINING:    3.603386128e-7
```

with the exact identity

\[
C_{\rm cert}+C_{\rm rem}=C_{\rm target}.
\]

### Audited nodes

```text
V < 1000 edge:
    CLOSED — FINITE-CERTIFIED / AUDITED

complete-period endpoint main:
    CLOSED — KERNEL-PROVED / FINITE-CERTIFIED / AUDITED
    C_endpoint < 469/75000

aggregate sufficient target:
    C_agg <= 69/5000
    ANALYTICALLY-PROVED / CONDITIONAL implication
    physical aggregate estimate itself OPEN

remaining covariance allowance:
    283/37500

required physical residual:
    C_F + 2 C_ED + C_DD + C_S < 283/37500
    OPEN

medium-k:
    STRICTLY REDUCED / OPEN

two-high:
    OPEN / NOT ENTERED

signed floor:
    OPEN

Maynard effectivization:
    OPEN / NOT ENTERED

Erdős #287:
    OPEN
```

The outer coefficient `lambda(b)` is part of the physical norm and may not be dropped. The factor `2` in front of `C_ED` is mandatory.

## 2. Latest live candidate frontier — not audited into R12

The newest research-session snapshot is recorded separately at:

[`frontier/2026-09-05-static-ramanujan/FRONTIER.md`](frontier/2026-09-05-static-ramanujan/FRONTIER.md)

Its current candidate ledger is

```text
LATEST UNAUDITED / CANDIDATE FRONTIER:
    static Ramanujan r > 200 signed tail

LATEST CANDIDATE SUBTOTAL:
    6.341463872e-7

LATEST CANDIDATE GLOBAL CAPACITY:
    2.519186128e-7

primitive/static r <= 200:
    CANDIDATE-CLOSED / awaiting independent audit

moving Ramanujan window:
    CANDIDATE-REMOVED / superseded by static freeze

static signed r > 200 tail:
    OPEN

medium-k:
    STRICTLY REDUCED / OPEN

two-high:
    NOT ENTERED

signed floor:
    OPEN

Maynard:
    NOT ENTERED

Erdős #287:
    OPEN
```

> **Candidate numbers do not supersede the audited R12 ledger until independently reviewed.**

In particular, `6.341463872e-7` and `2.519186128e-7` are not certified R12 numbers and must not be quoted as audited capacity.

## 3. Corrections / firewalls that remain active

The following statements are retired or prohibited:

1. unweighted per-fibre `C_joint <= 0.09` — **FALSE**; a one-point physical fibre gives `C_joint >= 9/64`;
2. inserting the global singular-series factor independently at each prime — **SOURCE-MISMATCHED**;
3. retaining both the old `V<50` charge and the `V<1000` replacement — **DOUBLE COUNTING**;
4. combining the full half-divisor replacement chart with the incremental medium chart — **INVALID**, because they are alternative decompositions;
5. using `Z(s,s)=0` as a bound for the directed anti-diagonal Perron truncation — **INVALID INFERENCE**;
6. identifying the complete-period endpoint main with the complete joined covariance — **INVALID INFERENCE**.

See [`CORRECTIONS_AND_RETRACTIONS.md`](CORRECTIONS_AND_RETRACTIONS.md) and the R12 audited status ledger.

## 4. Formal verification firewall

The formal source tree remains at [`RequestProject/`](RequestProject/). The R12 formal map records which results are kernel-checked and where the formal scope stops.

A Lean theorem for a finite algebraic identity does not automatically establish an infinite Euler product, a contour shift, an analytic estimate, or the existence of a populated physical certificate. Conditional compilers remain conditional until their analytic inputs are supplied.

## 5. Source-of-truth order

For public status questions, read the repository in this order:

1. `CURRENT_STATUS.md` and `CLAIMS_LEDGER.md` for the concise public state;
2. the latest audited release in `paper/audited-release/` for mathematical detail and exact capacity;
3. `RequestProject/` plus the formal module map for kernel-checked scope;
4. `frontier/` for newer candidate research;
5. `archive/` for historical provenance and superseded routes.

The former 2 September R10 `CURRENT_STATUS.md` has been preserved in the historical archive and no longer controls the public frontier.

**ERDŐS PROBLEM #287 REMAINS OPEN.**
