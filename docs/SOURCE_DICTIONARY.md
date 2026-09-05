# Source, Evidence, and Strategy Dictionary

This document explains the public information architecture. It is not a new mathematical theorem.

## Researcher-facing ontology

| Bucket | What it means | What it must not imply |
|---|---|---|
| `banked/` | trusted result at a precisely stated evidence scope | that every item is Lean-proved or that downstream analytics are automatic |
| `frontier/` | current parent, candidate reductions, or guarded downstream nodes | that a candidate is audited or that a downstream gate has been entered |
| `graveyard/` | false, retired, or superseded routes | that every graveyard item is mathematically false |
| `archive/` | historical manuscripts, reports, source packages, old frontier snapshots | current authority from filename/date/revision alone |

## Evidence classes inside the bank

| Evidence class | Backing location | What it may establish | What it may not be silently promoted to |
|---|---|---|---|
| `KERNEL-PROVED` | `RequestProject/` + formal map | exact Lean theorem at literal hypotheses | missing analytic estimates or physical instantiation |
| `FINITE-CERTIFIED` | `certificates/` and release certificates | deterministic exact/outward-rounded finite statement | unencoded asymptotic theorem |
| `ANALYTICALLY-PROVED` | audited paper/source proof | analytic theorem at stated hypotheses/source dictionary | Lean formalization or stronger coefficient class |
| `AUDITED` | audited release/review layer | independently checked claim at stated scope | automatic downstream closure |
| `CONDITIONAL` | theorem/compiler with visible hypothesis | implication from that hypothesis | truth of the hypothesis |
| `CANDIDATE` | `frontier/` | substantial live proof-search result | audited baseline or certified capacity |

## Current two-level source order

For **theoremhood, evidence, and numerical capacity**:

1. latest independently audited release and status ledger;
2. kernel-checked formal result at exact scope;
3. deterministic finite certificate at exact scope;
4. audited analytic proof;
5. live candidate result;
6. historical archive.

For **what theorem to attack next**:

1. [`../PROOF_MAP.md`](../PROOF_MAP.md);
2. [`../frontier/current-parent/`](../frontier/current-parent/);
3. candidate subresults under [`../frontier/candidate-results/`](../frontier/candidate-results/);
4. downstream entry guards;
5. check [`../graveyard/`](../graveyard/) before reopening an old route.

This two-level rule is essential: the R12 audited weighted-covariance chart remains the quantitative evidence baseline, while the later signed `R_012` source is the current source-minimal proof-search parent. A strategic supersession is not a theoremhood promotion.

## Physical versus abstract statements

Every public claim should identify whether it is:

- abstract finite/algebraic;
- source-specific and physically instantiated;
- conditional on an analytic input;
- numerically certified;
- audited paper-level mathematics;
- or a live candidate route.

If two sources disagree, do not average or merge them silently. Determine whether the disagreement is about **truth/evidence** or merely about **which coordinate is strategically controlling**.
