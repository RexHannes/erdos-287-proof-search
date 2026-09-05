# Erdős Problem #287 — Audited Proof-Search Programme

> **Status: OPEN. No solution of Erdős Problem #287 is claimed.**

This repository contains a public research programme combining paper proofs, Lean-checked finite/algebraic modules, deterministic certificates, independent audits, and live proof-search work.

## The problem

For a representation

\[
1=\frac1{n_1}+\cdots+\frac1{n_k},
\qquad n_1<\cdots<n_k,
\]

Erdős Problem #287 asks whether one must have

\[
\max_i (n_{i+1}-n_i)\ge 3.
\]

The problem remains open in this repository.

## Start here

- **[Read the audited R12 release](paper/audited-release/2026-09-05-r12/README.md)** — latest independently audited effectivity synthesis.
- **[View the proof map](PROOF_MAP.md)** — the theorem/dependency DAG and the audited-vs-candidate firewall.
- **[View current status](CURRENT_STATUS.md)** — concise controlling status and capacity ledger.
- **[View the live research frontier](frontier/README.md)** — newer candidate work, kept separate from the audited baseline.
- **[View the claims ledger](CLAIMS_LEDGER.md)** — claim-by-claim status, evidence class, and current/retired designation.
- **[View formal verification](RequestProject/)** — Lean source; exact scope is mapped in the audited release.

## Current audited baseline — 5 September 2026

| Node | Status |
|---|---|
| Certified subtotal | `5.257263872e-7` |
| Remaining capacity | `3.603386128e-7` |
| `V<1000` edge | **FINITE-CERTIFIED / AUDITED / CLOSED** |
| Complete-period endpoint | **KERNEL-PROVED / FINITE-CERTIFIED / AUDITED** |
| Medium-`k` | **STRICTLY REDUCED / OPEN** |
| Two-high | **OPEN / NOT ENTERED** |
| Signed floor | **OPEN** |
| Maynard effectivization | **OPEN / NOT ENTERED** |
| Erdős #287 | **OPEN** |

The audited residual requires the physical `lambda(b)`-weighted covariance bound

\[
C_F+2C_{ED}+C_{DD}+C_S<\frac{283}{37500},
\]

or its exactly equivalent all-`q` discrepancy formulation. No current audited result proves this residual.

## Audited vs live research

The repository has two deliberately separate public layers:

**AUDITED RELEASE.** Results in `paper/audited-release/` have an explicit status ledger, provenance record, formal-scope map, and certificate where applicable.

**LIVE CANDIDATE FRONTIER.** Newer research in `frontier/` may strictly reduce the problem, but it does not alter the audited numerical ledger until independently reviewed.

Candidate numbers do not supersede the audited ledger until independently reviewed.

## Repository layout

```text
README.md                       public landing page
PROOF_MAP.md                    proof/dependency map
CURRENT_STATUS.md               concise controlling status
CLAIMS_LEDGER.md                evidence and claim-status matrix
CORRECTIONS_AND_RETRACTIONS.md  retired/false claims

paper/                          audited releases
frontier/                       live candidate research
RequestProject/                 Lean/formal source tree
certificates/                   public certificate index/material
reviews/                        audit and formal-review navigation
archive/                        historical manuscripts, safe banks, source packages
scripts/                        reproducibility utilities
.github/                        CI/build workflows
```

`RequestProject/` deliberately keeps its historical path in this cleanup so that Lean imports and reproducibility are not broken merely for cosmetic reasons.

## Provenance

Historical files have not been discarded. They are moved under [`archive/`](archive/) with a legacy-path index, while Git history remains intact. This reorganisation changes the public information architecture; it does not rewrite load-bearing mathematics.

See also [Corrections and retractions](CORRECTIONS_AND_RETRACTIONS.md).
