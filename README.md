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
- the proposed fixed-certificate analytic leakage estimate;
- Gate-1B H8/H9 source-to-Kummer analytic closure;
- a Ford–Maynard analytic lower-bound application proving the large-`M` supply;
- the final theorem Erdős #287.

The exact formal remaining supply interface is `Erdos287.WindowPairSupply`.  A Sophie-type
prime witness is sufficient for it but is stronger than necessary.

## Current update files

- [Aristotle V13 update](ARISTOTLE_V13_UPDATE.md) — conservative status update; no analytic
  claim is promoted into the Lean bank.
- [Gate 1A V13 draft update](ERDOS287_GATE1A_V13_DRAFT_UPDATE.md) — Gate 1A is treated as
  an **optional analytic packet provider**, not a mandatory global prerequisite for #287.
- `RequestProject/Status/Erdos287V13Frontier.lean` — records the repaired open
  `LCBetaUpperHalf` interface and regression pins to the existing finite closure compiler.

Paper:
[ERDOS287_PUBLIC_REVIEW_DRAFT_V2_FINAL.pdf](ERDOS287_PUBLIC_REVIEW_DRAFT_V2_FINAL.pdf)

AI assistance: The project used Aristotle and LLM-assisted mathematical research. All public claims are stated at the status level indicated above.
