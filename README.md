# Erdős Problem #287 — Lean-Verified Finite Reduction

Status: partial formal verification / public research draft.  
This repository does **NOT** claim an unconditional proof of Erdős #287.

Machine-checked in Lean:

- exact public Erdős-287 counterexample predicate;
- public-counterexample -> Gap2CE bridge;
- top-layer p-adic obstruction;
- sign-sensitive Sophie blockers;
- maximum-divisor prime blockers;
- interval-certificate engine;
- no exact counterexample with maximum denominator
  `3 <= M <= 4,000,000,000`.

Not formalised/proved here:

- the large-`M` `WindowPairSupply` statement;
- `AFFINE287-DET1-HYBRID-MQ45`;
- `k=0` smooth-parity closure;
- the full fixed-certificate leakage estimate;
- the remaining literal Gate-1B/provider stability dictionaries;
- a Ford–Maynard analytic lower-bound application proving the large-`M` supply;
- the final theorem Erdős #287.

The exact formal remaining supply interface is `Erdos287.WindowPairSupply`. A Sophie-type
prime witness is sufficient for it but is stronger than necessary.

## Current research frontier — 27 Aug 2026

Research/frontier material is in [`frontier/`](frontier/):

- [Current frontier status](frontier/ERDOS287_FRONTIER_STATUS_2026-08-27.md)
- [Current determinant-one hybrid frontier](frontier/ERDOS287_PENDING_DET1_HYBRID_FRONTIER_2026-08-27.md)
- [Next determinant-one hybrid attack](frontier/ERDOS287_NEXT_AFFINE287_DET1_HYBRID_MQ45.md)
- [Earlier singleton reduction](frontier/ERDOS287_PENDING_SINGLETON_FRONTIER_2026-08-27.md)
- [Earlier Aristotle V12 smooth-parity reproof prompt](frontier/ERDOS287_ARISTOTLE_V12_SMOOTH_PARITY_REPROOF.md)

### Latest reduction

The singleton/provider audit has now been completed far enough to rule out the naive identification

```text
singleton generated Type II = Gate-1B common-conductor signed covariance.
```

Exact coprimality shows that the Ford outer Möbius carrier and the shifted-output Gate-1B complement Möbius carrier are different variables. The direct dictionary therefore fails.

At the same time, the selected Type-II coefficient can be shortened further to

```text
1 <= |E| <= 2,
X^epsilon* < m_E <= X^(3/20+o(1)).
```

Large shifted-output blocks are routed to the existing one-outer/F3 sector; a Wright-compatible AP child gives only a conditional low/moderate-modulus subrange; and all multiouter algebraic sources can be regrouped exactly into generated two-outer form.

The current first general analytic open is therefore

`AFFINE287-DET1-HYBRID-MQ45`

with equivalent descriptive label

`HYBRID-MQ-KLOOSTERMAN-LARGE-SIEVE`.

The core determinant-one relation is

```text
(qa)b - (2m)n = +/-1,
```

hence after fixing `q,a,m` one has the exact affine parametrisation

```text
b = b0 + 2m t,
n = n0 + qa t.
```

The remaining theorem must control the resulting coherent `q,a,m` family with the actual generated outer coefficient grammar, affine sign, Möbius provenance, conductor structure and exceptional strata intact.

This frontier material is research-level and does not alter the trusted Lean status above.

## Existing formal/update files

- [Aristotle V13 update](ARISTOTLE_V13_UPDATE.md) — conservative formal-status update; no analytic
  claim is promoted into the Lean bank.
- [Gate 1A V13 draft update](ERDOS287_GATE1A_V13_DRAFT_UPDATE.md) — Gate 1A is treated as
  an **optional analytic packet provider**, not a mandatory global prerequisite for #287.
- `RequestProject/Status/Erdos287V13Frontier.lean` — records the repaired open
  `LCBetaUpperHalf` interface and regression pins to the existing finite closure compiler.

Earlier public-review PDF:
[ERDOS287_PUBLIC_REVIEW_DRAFT_V2_FINAL.pdf](ERDOS287_PUBLIC_REVIEW_DRAFT_V2_FINAL.pdf)

AI assistance: The project used Aristotle and LLM-assisted mathematical research. All public claims are stated at the status level indicated above.
