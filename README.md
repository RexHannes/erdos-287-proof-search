# Erdős Problem #287 — Audited Proof / Proof-Search Programme

> **Status: OPEN. No solution of Erdős Problem #287 is claimed.**

This repository contains the formal, analytic, computational, audit, and proof-search work for Erdős Problem #287. The public information architecture is organized by **mathematical role**, not by revision number.

## The problem

For

\[
1=\frac1{n_1}+\cdots+\frac1{n_k},
\qquad n_1<\cdots<n_k,
\]

Erdős Problem #287 asks whether necessarily

\[
\max_i(n_{i+1}-n_i)\ge 3.
\]

The problem remains open.

## Start here — six links

1. **[`PROOF_MAP.md`](PROOF_MAP.md)** — canonical theorem/dependency map: what is banked, what is current, what is superseded.
2. **[`CURRENT_STATUS.md`](CURRENT_STATUS.md)** — concise current state and downstream entry guards.
3. **[`CLAIMS_LEDGER.md`](CLAIMS_LEDGER.md)** — claim-by-claim evidence and strategy classification.
4. **[`banked/`](banked/)** — trusted mathematics, separated by evidence class.
5. **[`frontier/`](frontier/)** — current parent, candidate reductions, and downstream nodes.
6. **[`graveyard/`](graveyard/)** / **[`archive/`](archive/)** — what not to reopen, and the full historical research archaeology.

A new reader should not need to infer the current theorem from filenames such as `R7`, `R10`, `R12`, `V16`, or dozens of historical safe-bank reports.

## Current proof-search route

```text
BANKED SOURCE / ALGEBRA
    |
    +-- B_src normalization
    +-- odd half-divisor correction
    +-- c1/c2 splice
    +-- full unselected Z(s,s)=0 at banked scope
    +-- V<1000 finite closure
    +-- complete-period endpoint main
    |
    v
corrected selector Γ
    |
    +-- j>=4      CANDIDATE-EMPTY
    +-- j=3       CANDIDATE-CLOSED, reported <3e-9 B_X
    +-- j=0 + j=1 + active j=2
            |
            v
           R_012
           OPEN
            |
            v
       signed floor
           OPEN
            |
            v
   Maynard effectivization
        NOT ENTERED
            |
            v
  finite/asymptotic splice
        NOT ENTERED
            |
            v
       Erdős #287
           OPEN
```

Inside `R_012`, the live obstacles are incomplete low-divisor fibres, rough defect, selector-sensitive Perron/hyperbola terms, and large ratio-frequency decay. The active `j=2` source has been reduced in the latest proof-search census to `71` prefix families for `c=1` and `37` for `c=2`; these reductions remain candidate-level until independently promoted.

## Audited baseline versus live proof search

The current independently audited quantitative baseline is the **R12 effectivity synthesis, 5 September 2026**:

```text
certified subtotal:  5.257263872e-7
remaining capacity:  3.603386128e-7
V<1000 edge:         CLOSED / FINITE-CERTIFIED / AUDITED
complete endpoint:   CLOSED at its stated scope
Erdős #287:          OPEN
```

R12 is retained at [`paper/audited-release/2026-09-05-r12/`](paper/audited-release/2026-09-05-r12/).

The live proof map is newer than R12 as a **dependency reassembly**. This does not silently upgrade candidate `j`-sector results or rewrite R12 history. It means several R12-era coordinates are no longer treated as mandatory standalone gates.

## The four researcher-facing buckets

```text
banked/
    trusted inputs, with formal / audited-analytic / certificate / manuscript distinctions

frontier/
    current controlling physical parent
    candidate results awaiting audit
    guarded downstream stages

graveyard/
    false
    retired / nonclosing / source-mismatched
    superseded coordinate systems

archive/
    historical reports, manuscripts, source packs, old frontier notes
```

`banked` is intentionally not called `proven`: kernel-checked algebra, audited analytic work, and finite certificates are different evidence classes.

`graveyard` does intentionally distinguish **false** from **retired** and **superseded**. An old route can stop controlling the proof without its mathematics becoming false.

## Technical evidence stores

The following paths remain because they are useful or required for reproducibility; they are **backing stores**, not competing proof ontologies:

- [`RequestProject/`](RequestProject/) — Lean source and formal modules;
- [`paper/`](paper/) — audited release packages;
- [`certificates/`](certificates/) — certificate navigation/material;
- [`reviews/`](reviews/) — audit/review navigation;
- [`scripts/`](scripts/) — reproducibility utilities;
- [`.github/`](.github/) — CI/build workflows.

Historical root clutter has been moved into `archive/` on the cleanup branch rather than deleted. Git history is preserved.

## Hard publication firewall

Do not infer any of the following from folder names or source transformations:

- a candidate result is audited because it is newer;
- a superseded node is proved;
- a retired theorem is false unless an explicit counterexample/retraction exists;
- a finite or Lean theorem supplies an external analytic estimate;
- diagonal cancellation by itself supplies the required directed ratio-frequency bound;
- Erdős #287 is solved.

See [`CORRECTIONS_AND_RETRACTIONS.md`](CORRECTIONS_AND_RETRACTIONS.md) for the dated no-reopen ledger.

**ERDŐS PROBLEM #287 REMAINS OPEN.**
