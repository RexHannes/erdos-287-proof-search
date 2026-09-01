# Erdős Problem #287 — 1 Sep 2026 Direct3221 / K0-SP2 Reassembly Update

**Public status: ERDŐS #287 REMAINS OPEN.**

This note records the latest research-status correction after the physical Balanced7 super-square-root calculation. It is intentionally narrower than a proof claim.

## What moved

The exact physical `2+5` grouping is

```text
m = p1 p2,      M = X^(2/7)
w = p3 p4 p5 p6 p7,   W5 = X^(5/7)
```

and the source congruence is

```math
q \mid 2mw+s
\quad\Longleftrightarrow\quad
w \equiv -s(2m)^{-1} \pmod q.
```

This matches the existing inverse-sampled 3221 dictionary.

For the source-specific centered Balanced7 defect, the direct raw-minus-principal variance route gives, at research/paper level,

```math
|D_{Q,s}| \ll X(\log X)^{-5/2+o(1)}
```

for each dyadic super-square-root `Q` cell, and after dyadic reassembly

```math
\sum_Q |D_{Q,s}| \ll X(\log X)^{-3/2+o(1)} = o(X/\log X).
```

This is sufficient for the **physical Balanced7 endpoint**.

## What did NOT move

The stronger reusable socket demanding

```math
X(\log X)^{-A}
```

for every fixed `A` is **not** proved. The physical endpoint and the generic arbitrary-`A` Type-II-style socket are now treated as different objects.

Accordingly:

```text
SP2-LABELLED-SINGLETON-CENTERED-QCELL-SUPERSQRT45
    generic arbitrary-A form: OPEN

SP2-BALANCED7-SUPERSQRT-DIRECT3221-DEFECT45
    physical source-specific form: PAPER/RESEARCH CLOSED

SP2-BALANCED7-FULL-Q45
    PAPER/RESEARCH CLOSED under the frozen source/comparison bank

BALANCED7
    PAPER/RESEARCH CLOSED
```

No Lean theorem is claimed for the external Selberg-sieve/Shiu analytic providers merely by writing this status note.

## New controlling residual

The first downstream research residual is now

```text
287-K0-SP2-UNIFORM-FRAGMENTATION-REASSEMBLY45
```

rather than the physical super-square-root cell.

The direct endpoint leaves only a half-log of naive reassembly room:

```text
base exponent       = -3/2
physical threshold  < -1
available cost      < +1/2
```

Hence `polylogarithmically many fragments` is not a sufficient statement. The exact fragmentation multiplicity and all external logarithmic costs must be compiled. If the naive cost is at least `L^(1/2)`, the fragments must be recombined before triangle inequality or handled by a joint square-sum/cancellation argument.

## Formal layer added in this update

The 1 Sep append-only formal status layer contains:

- `RequestProject/Status/CurrentStatusErdos287Direct3221Reassembly.lean`
- `RequestProject/CurrentProgramme/Erdos287K0SP2LogBudget.lean`
- `RequestProject/CurrentProgramme/Erdos287Direct3221Interfaces.lean`
- `RequestProject/Status/AxiomAuditErdos287Direct3221Reassembly.lean`

These files deliberately formalize only status/type firewalls and deterministic exponent arithmetic. External analytic estimates remain explicit interfaces, not axioms.

## Downstream firewall

```text
physical Balanced7 closure
    != generic arbitrary-A supersqrt closure
    != full K0-SP2 source reassembly
    != FULL-SOURCE-LOCAL-ANALYTIC-KERNEL45
    != WindowPairSupply
    != Erdős #287.
```

**ERDŐS PROBLEM #287 REMAINS OPEN.**
