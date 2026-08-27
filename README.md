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
- M/Vaughan branch `AFFINE287-PRIME-MODULUS-MU-TWOOUTER45`;
- balanced-seven V-branch `AFFINE287-POLARIZED-OMEGA7-SIGNED-EOD45`;
- `AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45`;
- `VAUGHAN-TYPEI-GENERATED-KAPPA45` / comparison-side Vaughan source matching;
- `k=0` smooth-parity closure;
- the full fixed-certificate leakage estimate;
- the remaining literal Gate-1B/provider stability dictionaries;
- a Ford–Maynard analytic lower-bound application proving the large-`M` supply;
- the final theorem Erdős #287.

The exact formal remaining supply interface is `Erdos287.WindowPairSupply`. A Sophie-type
prime witness is sufficient for it but is stronger than necessary.

## Current public review / research frontier — 28 Aug 2026

**Stable public-review PDF (current V15 source update):**  
[ERDOS287_PUBLIC_REVIEW_DRAFT_V2_FINAL.pdf](ERDOS287_PUBLIC_REVIEW_DRAFT_V2_FINAL.pdf)

Research/frontier material is in [`frontier/`](frontier/):

- [Current frontier status](frontier/ERDOS287_FRONTIER_STATUS_2026-08-27.md)
- [Balanced-seven polarized endpoint frontier](frontier/ERDOS287_PENDING_BALANCED7_POLARIZED_EOD_FRONTIER_2026-08-28.md)
- [Next balanced-seven endpoint attack](frontier/ERDOS287_NEXT_POLARIZED_OMEGA7_SIGNED_EOD45.md)
- [V15 controlling balanced-seven source update inserted into the public-review PDF](frontier/ERDOS287_LATEST_BALANCED7_UPDATE_V15.tex)
- [M/Vaughan prime-modulus Möbius two-outer frontier](frontier/ERDOS287_PENDING_PRIME_MODULUS_MU_TWOOUTER_FRONTIER_2026-08-27.md)
- [V14 controlling Vaughan source update](frontier/ERDOS287_LATEST_SOURCE_UPDATE_V14.tex)
- [Earlier determinant-one hybrid frontier](frontier/ERDOS287_PENDING_DET1_HYBRID_FRONTIER_2026-08-27.md)
- [Earlier singleton reduction](frontier/ERDOS287_PENDING_SINGLETON_FRONTIER_2026-08-27.md)

### Current two-front analytic picture

The V14 source audit remains in force on the M/Vaughan side:

- exact affine Vaughan prime source: **PASS**;
- proper prime-power outer terms: **PASS / negligible**;
- literal Vaughan cofactor well-factorability: **FALSE**;
- direct canonical Gate-1A adapter: **FAIL**;
- prime-modulus Möbius two-outer structural map: **PASS**;
- `AFFINE287-PRIME-MODULUS-MU-TWOOUTER45`: **OPEN**.

The latest V15 audit concerns the balanced-seven V-branch. Set

```text
Q = X^(3/5),   Y = X^(1/7).
```

The raw seven labelled prime boxes admit an exact squarefree torus polarization into a family of
ordinary smooth-supported multiplicative functions `f_z`. Repeated-prime tuples cost only
`X^(6/7+o(1))`.

The following broad routes are now explicitly nonclosing / unavailable for the exact cell:

- separate multiplicative large sieve: `X^(1/10)` deficit;
- separated high-moment route: same deficit;
- equal-seven Proposition 6.3 three-block dictionary: **FALSE**;
- termwise prime-box Vaughan/Heath-Brown repair: **nonexhaustive**;
- q-Möbius micro-switch as an exhaustive closure: **nonexhaustive** because the prime-q sector survives.

The first exact balanced-seven analytic residual is

`AFFINE287-POLARIZED-OMEGA7-SIGNED-EOD45`.

It asks only for one signed torus coefficient:

```text
integral_{T^7} conjugate(z1...z7)
  sum_{q~X^(3/5)} mu(q)
  Delta_LC(f_z; X, q, -s/2)
= o(X/log X).
```

The same source decomposition also requires the comparison pin

`AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45`.

Together these two statements imply

`AFFINE287-BALANCED7-MODULUS-AVERAGE45 CLOSED`.

### Current distance ledger

| Node | Status |
|---|---|
| fixed Ford certificate / transference | PASS (research/source layer) |
| Ford generated depth | PASS, safe `N0=112` |
| exact affine Vaughan prime source | PASS |
| proper prime-power outer | PASS / negligible |
| prime-modulus Möbius two-outer structural map | PASS |
| `AFFINE287-PRIME-MODULUS-MU-TWOOUTER45` | **M/VAUGHAN BRANCH OPEN** |
| balanced-seven character parent | PASS |
| separate multiplicative LS / high moments | NONCLOSING: `X^(1/10)` deficit |
| P6.3 equal-seven dictionary | FALSE |
| repeated-prime router | PASS: `X^(6/7+o(1))` |
| squarefree torus polarization | PASS |
| smooth multiplicative class dictionary | PASS |
| `AFFINE287-POLARIZED-OMEGA7-SIGNED-EOD45` | **FIRST EXACT V-BRANCH ANALYTIC OPEN** |
| `AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45` | SOURCE OPEN |
| balanced-seven cell | REDUCED, NOT CLOSED |
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
