# Erdős Problem #287 — Current Frontier after V16 Consolidation

**Date:** 28 August 2026  
**Status:** OPEN.

## Unconditional public result

No exact counterexample has maximum denominator at most

```text
4,000,000,000.
```

This is publicly Lean-checked.

## Exact global closure interface

The public Lean compiler reduces the remaining problem to effective eventual

```text
Erdos287.WindowPairSupply M.
```

This supply is not proved for all large `M`.

## Current source-minimal research front

### Hard affine μ-log source

```math
Λ(2mn+s)=Σ_{qr=2mn+s} μ(q)log r,
qr-2mn=s=±1.
```

The identity, exact partition, and affine-line parametrization are exact algebra. Their V15 Lean source is present in the supplied midpoint archive; final public replay is pending. Analytic cancellation remains open.

### Balanced-seven source

```text
Q=X^(3/5), Y=X^(1/7).
```

The seven labelled boxes admit an exact squarefree torus polarization. The current exact balanced-seven residuals are:

```text
AFFINE287-POLARIZED-OMEGA7-SIGNED-EOD45          OPEN ANALYTIC
AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45       OPEN SOURCE
```

Passing both closes the balanced-seven modulus-average cell, but not all remaining fixed-certificate packets or FCL.

## Current distance ledger

| Node | Status |
|---|---|
| Exact problem predicate | PUBLIC LEAN-CHECKED |
| Finite exclusion to 4e9 | PUBLIC LEAN-CHECKED |
| WindowPairSupply compiler | PUBLIC LEAN-CHECKED / CONDITIONAL |
| V14 Vaughan structural spine | PUBLIC LEAN-CHECKED ALGEBRA |
| V15 μ-log / polarization source | FORMALIZATION REPLAY PENDING |
| Hard μ-log analytic cancellation | OPEN |
| Polarized signed EOD | OPEN |
| Comparison low-conductor match | OPEN |
| Remaining fixed-g_* packet census | OPEN |
| FCL | OPEN |
| Eventual WindowPairSupply | OPEN |
| Erdős #287 | OPEN |

The clean public paper is `ERDOS287_PUBLIC_REVIEW_CURRENT.pdf`; historical route audits are retained in the technical ledger and archive.
