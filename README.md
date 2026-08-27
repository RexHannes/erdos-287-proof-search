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
- `AFFINE287-PRIME-MODULUS-MU-TWOOUTER45`;
- `VAUGHAN-TYPEI-GENERATED-KAPPA45` / comparison-side Vaughan source matching;
- `k=0` smooth-parity closure;
- the full fixed-certificate leakage estimate;
- the remaining literal Gate-1B/provider stability dictionaries;
- a Ford–Maynard analytic lower-bound application proving the large-`M` supply;
- the final theorem Erdős #287.

The exact formal remaining supply interface is `Erdos287.WindowPairSupply`. A Sophie-type
prime witness is sufficient for it but is stronger than necessary.

## Current public review / research frontier — 27 Aug 2026

**Stable public-review PDF (current V14 source update):**
[ERDOS287_PUBLIC_REVIEW_DRAFT_V2_FINAL.pdf](ERDOS287_PUBLIC_REVIEW_DRAFT_V2_FINAL.pdf)

Research/frontier material is in [`frontier/`](frontier/):

- [Current frontier status](frontier/ERDOS287_FRONTIER_STATUS_2026-08-27.md)
- [Prime-modulus Möbius two-outer frontier](frontier/ERDOS287_PENDING_PRIME_MODULUS_MU_TWOOUTER_FRONTIER_2026-08-27.md)
- [V14 controlling source update inserted into the public-review PDF](frontier/ERDOS287_LATEST_SOURCE_UPDATE_V14.tex)
- [Earlier determinant-one hybrid frontier](frontier/ERDOS287_PENDING_DET1_HYBRID_FRONTIER_2026-08-27.md)
- [Earlier singleton reduction](frontier/ERDOS287_PENDING_SINGLETON_FRONTIER_2026-08-27.md)

### Latest source correction

The older generic determinant-one object

`AFFINE287-DET1-HYBRID-MQ45`

is now **superseded as the controlling source**. The actual affine prime term is first decomposed literally from

```text
Lambda(2mn+s),  s = +/-1,
```

using the exact Vaughan identity with `U=V=X^(1/3)`.

This gives:

- `AFFINE287-VAUGHAN-PRIME-SOURCE45: PASS`;
- proper prime-power outer terms: `PASS / negligible`, with relative margin `X^(-1/6+o(1))`;
- literal Vaughan cofactor well-factorability: **FALSE**;
- direct canonical Gate-1A adapter: **FAIL**;
- direct native QK56 dictionary: **not established**;
- prime-modulus Möbius two-outer structural map: **PASS**.

The current first true analytic open is

`AFFINE287-PRIME-MODULUS-MU-TWOOUTER45`.

Its source-exact prime-modulus form is schematically

```text
sum_{p~P} log p
  sum_{2mn == -s (mod p)}
    xi_pi(m) kappa_pi(n)
    Delta^{mu,1}_{D,R}((2mn+s)/p)
  - source-matched main term,
```

where

```text
Delta^{mu,1}_{D,R}(u)
 = sum_{dr=u, d~D, r~R} mu(d) W_D(d) W_R(r).
```

Required saving: `o(X/log X)` or a sufficiently small fixed constant multiple preserving the fixed-certificate margin.

### Current distance ledger

| Node | Status |
|---|---|
| fixed Ford certificate / transference | PASS (research/source layer) |
| Ford generated depth | PASS, safe `N0=112` |
| exact affine Vaughan prime source | PASS |
| proper prime-power outer | PASS / negligible |
| comparison Vaughan matching | OPEN source pin |
| Vaughan Type-I generated-`kappa` | OPEN adapter |
| Vaughan cofactor well-factorability | FALSE |
| direct Gate-1A canonical map | FAIL |
| direct native QK56 map | NOT ESTABLISHED |
| prime-modulus Möbius two-outer structural map | PASS |
| `AFFINE287-PRIME-MODULUS-MU-TWOOUTER45` | **FIRST TRUE ANALYTIC OPEN** |
| `k=0` smooth packet | OPEN |
| remaining fixed-`g_*` packet census | OPEN |
| fixed-certificate leakage / FCL | OPEN |
| Ford lower-bound completion | CONDITIONAL/OPEN |
| Erdős #287 | OPEN |

This research frontier does not alter the trusted finite Lean status.

## Existing formal/update files

- [Aristotle V13 update](ARISTOTLE_V13_UPDATE.md) — conservative formal-status update; no analytic
  claim is promoted into the Lean bank.
- [Gate 1A V13 draft update](ERDOS287_GATE1A_V13_DRAFT_UPDATE.md) — Gate 1A is treated as
  an **optional analytic packet provider**, not a mandatory global prerequisite for #287.
- `RequestProject/Status/Erdos287V13Frontier.lean` — records the repaired open
  `LCBetaUpperHalf` interface and regression pins to the existing finite closure compiler.

AI assistance: The project used Aristotle and LLM-assisted mathematical research. All public claims are stated at the status level indicated above.
