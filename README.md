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
- the fixed-certificate smooth-parity analytic estimate;
- the full fixed-certificate leakage estimate;
- Gate-1B H8/H9 source-to-Kummer analytic closure;
- a Ford–Maynard analytic lower-bound application proving the large-`M` supply;
- the final theorem Erdős #287.

The exact formal remaining supply interface is `Erdos287.WindowPairSupply`. A Sophie-type
prime witness is sufficient for it but is stronger than necessary.

## Current research frontier — 27 Aug 2026

The latest standalone research dossier is in [`frontier/`](frontier/):

- [V12 standalone verification dossier (PDF)](frontier/ERDOS287_STANDALONE_VERIFICATION_DOSSIER_V12.pdf)
- [V12 LaTeX source](frontier/ERDOS287_STANDALONE_VERIFICATION_DOSSIER_V12.tex)
- [Frontier status](frontier/ERDOS287_FRONTIER_STATUS_2026-08-27.md)
- [Aristotle V12 hostile reproof prompt](frontier/ERDOS287_ARISTOTLE_V12_SMOOTH_PARITY_REPROOF.md)

The controlling research correction is that fixing a Ford certificate does **not** reduce
the leakage census to H8/H9 alone. The first literal uncovered analytic packet is
`287-FIXED-CERTIFICATE-SMOOTH-PARITY45`, a truncated Möbius-parity correlation.
The generic seven-prime Kummer estimate is retained only as a conditional child provider.

This frontier material is research-level and does not alter the trusted Lean status above.

## Existing update files

- [Aristotle V13 update](ARISTOTLE_V13_UPDATE.md) — conservative formal-status update; no analytic
  claim is promoted into the Lean bank.
- [Gate 1A V13 draft update](ERDOS287_GATE1A_V13_DRAFT_UPDATE.md) — Gate 1A is treated as
  an **optional analytic packet provider**, not a mandatory global prerequisite for #287.
- `RequestProject/Status/Erdos287V13Frontier.lean` — records the repaired open
  `LCBetaUpperHalf` interface and regression pins to the existing finite closure compiler.

Earlier public-review PDF:
[ERDOS287_PUBLIC_REVIEW_DRAFT_V2_FINAL.pdf](ERDOS287_PUBLIC_REVIEW_DRAFT_V2_FINAL.pdf)

AI assistance: The project used Aristotle and LLM-assisted mathematical research. All public claims are stated at the status level indicated above.
