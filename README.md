# Erdős Problem #287 — public research and Lean audit repository

**Status:** open research programme / partial formal verification.  
**ERDŐS PROBLEM #287 REMAINS OPEN.**

This repository is scoped to **Erdős Problem #287**. The authoritative living ledger is [`CURRENT_STATUS.md`](CURRENT_STATUS.md); historical manuscripts and reports are retained for provenance, but the later living ledger controls whenever statuses conflict.

## Start here

- [Authoritative current status](CURRENT_STATUS.md)
- [Current research frontier](RESEARCH_FRONTIERS/CURRENT_FRONTIERS.md)
- [Current Aristotle / Lean summary](ARISTOTLE_SUMMARY.md)
- [Clean 1-Sep formal entrypoint](RequestProject/CurrentErdos287.lean)
- [1 Sep 2026 research update](PUBLIC_REVIEW_UPDATE_2026-09-01.md)
- [1 Sep 2026 changelog](CHANGELOG_2026-09-01.md)
- [1 Sep 2026 contamination audit](CONTAMINATION_AUDIT_2026-09-01.md)
- [Living public review — stable path](ERDOS287_PUBLIC_REVIEW_CURRENT.pdf)
- [Corrections and retractions](CORRECTIONS_AND_RETRACTIONS.md)
- [Project-scope firewall](PROJECT_SCOPE.md)

## Strongest unconditional public theorem

The existing Lean-checked finite theorem excludes every exact counterexample with maximum denominator

```text
M <= 4,000,000,000.
```

The large-`M` interface `Erdos287.WindowPairSupply` remains conditional. No eventual supply theorem, effective final threshold, or unconditional solution of Erdős #287 is claimed.

## 1 September 2026 analytic milestone

The newest research layer isolates the physical Balanced7 super-square-root cell and uses the literal `2+5` source split

```text
m = p1*p2,
w = p3*p4*p5*p6*p7,
q | 2*m*w+s  <->  w = -s*(2*m)^(-1) mod q.
```

The direct centered raw-minus-principal variance gives, at the research/paper level,

```text
per dyadic Q:
    |D_{Q,s}| << X L^(-5/2+o(1));

after the full super-square-root dyadic band:
    sum_Q |D_{Q,s}| << X L^(-3/2+o(1)) = o(X/L).
```

Accordingly the source-specific physical status is

```text
SP2-BALANCED7-SUPERSQRT-DIRECT3221-DEFECT45:
    PAPER / RESEARCH CLOSED.

SP2-BALANCED7-FULL-Q45:
    PAPER / RESEARCH CLOSED.

BALANCED7:
    PAPER / RESEARCH CLOSED.
```

This does **not** close the stronger reusable socket asking for `X L^(-A)` for every fixed `A`. That generic arbitrary-`A` statement remains open.

## Current controlling frontier

The first downstream research residual is now

```text
287-K0-SP2-UNIFORM-FRAGMENTATION-REASSEMBLY45
```

The key audit is source exhaustivity plus the logarithmic reassembly budget. The physical super-square-root estimate has base exponent `-3/2`, while the final criterion requires an exponent strictly below `-1`; therefore naive absolute reassembly may spend **strictly less than one half logarithmic power**.

Still open:

```text
287-K0-SP2-UNIFORM-FRAGMENTATION-REASSEMBLY45
FULL-SOURCE-LOCAL-ANALYTIC-KERNEL45
WindowPair
ERDOS287
```

## Formal status

The living formal entrypoint is `RequestProject/CurrentErdos287.lean`. It imports the established #287 `RequestProject.Main` spine plus only the new #287 1-Sep direct3221/K0-SP2 layer.

The new Lean files are deliberately **interfaces, exact finite algebra, geometry, status declarations, and log-budget firewalls**. They do not turn the external Selberg-sieve/Shiu estimates, the paper-level direct3221 endpoint, or the K0-SP2 reassembly bound into axioms or automatic inhabitants.

Earlier formal banks remain valid only under their stated hypotheses. The public repository is rebuilt by CI after current-layer changes; a successful historical build is not treated as proof of the newest analytic research claims.

## Contamination firewall

The active 1-Sep status, frontier and `RequestProject/CurrentErdos287.lean` entrypoint are Erdős-287-only. Neither the living entrypoint nor its `RequestProject.Main` base imports the legacy `TrustedBank/Gate1A` / `TrustedBank/Gate1B` banks.

Those older cross-project-named banks remain only as **legacy/noncontrolling provenance** for reproducibility of historical runs. Compilation of a legacy generic lemma is not theorem ownership; no legacy problem-specific source/status/compiler statement is admissible in the living #287 chain without an explicitly #287-owned reintroduction and fresh audit.

The separate Twin-Prime programme is maintained in its own repository and is not an active dependency here.

**ERDŐS PROBLEM #287 REMAINS OPEN.**
