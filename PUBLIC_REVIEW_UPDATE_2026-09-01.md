# Public Review Addendum — 1 September 2026

**Erdős Problem #287 remains open.**

This addendum supersedes only the *controlling-frontier description* in the 31-August public checkpoint. It does not retract the earlier C0/transverse work.

## New source-specific endpoint

The latest physical Balanced7 analysis closes, at paper/research level, the concrete super-square-root `q`-cell needed by that source family. The key `2+5` split is literal, not an arbitrary coefficient substitution:

```text
m = p1 p2,
M = X^(2/7),

w = p3 p4 p5 p6 p7,
W5 = X^(5/7).
```

The congruence is

```math
q \mid 2mw+s
\iff
w \equiv -s(2m)^{-1}\pmod q.
```

The direct centered variance gives

```math
|D_{Q,s}| \ll X L^{-5/2+o(1)}
```

for each dyadic `Q` in the hard band and

```math
\sum_Q |D_{Q,s}| \ll X L^{-3/2+o(1)} = o(X/L)
```

after dyadic reassembly.

This closes the **physical Balanced7 endpoint**, not the stronger generic arbitrary-log-power theorem.

## Strength distinction

Still open:

```text
SP2-LABELLED-SINGLETON-CENTERED-QCELL-SUPERSQRT45
```

when interpreted as the reusable statement demanding `X L^(-A)` for every fixed `A`.

Paper/research closed:

```text
SP2-BALANCED7-SUPERSQRT-DIRECT3221-DEFECT45
SP2-BALANCED7-FULL-Q45
BALANCED7
```

## Current first residual

The controlling research node is now

```text
287-K0-SP2-UNIFORM-FRAGMENTATION-REASSEMBLY45.
```

The remaining issue is source-exhaustive fragmentation/reassembly with a strict log budget. Since the direct physical endpoint has exponent `-3/2` and the final physical threshold is strictly below `-1`, naive reassembly can spend **less than one half of a logarithm**. Any larger bookkeeping cost requires joint/pre-triangle reassembly rather than a raw triangle inequality.

## Formal status

The repository now contains an append-only Lean status/interface layer for:

- the generic-vs-physical supersqrt firewall;
- the half-log reassembly ledger;
- explicit uninhabited external analytic provider interfaces;
- an axiom-audit entry point.

These additions do not encode the Selberg sieve or Shiu theorem as axioms and do not claim an unconditional Lean proof of #287.

## Next audit target

A serious review should now attack, in order:

1. exact K0-SP2 fragment census;
2. source exhaustivity and overlaps;
3. owner routing and double-spending;
4. total log-cost exponent;
5. full-source local analytic kernel;
6. exact final compiler to the original Erdős #287 statement.

**ERDŐS PROBLEM #287 REMAINS OPEN.**
