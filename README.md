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
- `287-SMOOTH-PARITY-SINGLETON-GENERATED-TYPEII45`;
- the full fixed-certificate leakage estimate;
- the remaining literal Gate-1B/provider dictionaries;
- a Ford–Maynard analytic lower-bound application proving the large-`M` supply;
- the final theorem Erdős #287.

The exact formal remaining supply interface is `Erdos287.WindowPairSupply`. A Sophie-type
prime witness is sufficient for it but is stronger than necessary.

## Current research frontier — 27 Aug 2026

Research/frontier material is in [`frontier/`](frontier/):

- [Frontier status](frontier/ERDOS287_FRONTIER_STATUS_2026-08-27.md)
- [Pending singleton provider frontier](frontier/ERDOS287_PENDING_SINGLETON_FRONTIER_2026-08-27.md)
- [Aristotle V12 hostile reproof prompt](frontier/ERDOS287_ARISTOTLE_V12_SMOOTH_PARITY_REPROOF.md)

### Latest reduction

The literal `k=0` smooth-parity branch has now been structurally reduced to a **canonical singleton**

```text
X^(sigma/3) < m <= X^sigma < X^(1/6)
```

against a source-generated fixed-depth complement. The former depth-5 target is retired as controlling.

The new first analytic open is

`287-SMOOTH-PARITY-SINGLETON-GENERATED-TYPEII45`.

The next research action is

`SINGLETON-TO-GATE1B-LITERAL-PROVIDER-DICTIONARY45`.

That audit must preserve the literal complement grammar rather than replacing it by an arbitrary `tau_39`
coefficient class. Möbius-singleton, model-singleton, QK56/direct, and Gate-1A common-weight routes must be
tested only by literal source dictionaries.

The standalone V12 dossier remains the current local research manuscript; the repository mirror of its
reproducible PDF/TeX is being kept separate from the trusted formal status and should not be read as a Lean
result.

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
