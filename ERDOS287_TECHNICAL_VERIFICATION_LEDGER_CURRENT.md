# Erdős #287 — Current Technical Verification Ledger

**Date:** 28 August 2026  
**Status:** research ledger; Erdős #287 remains open.

This file is the technical companion to `ERDOS287_PUBLIC_REVIEW_CURRENT.pdf`. The public paper is intentionally coherent and short; this ledger preserves exact programme labels, failed dictionaries, and historical route provenance.

## A. Public Lean bank

| Node | Status | Public file / theorem |
|---|---|---|
| Exact counterexample predicate | PUBLIC LEAN-CHECKED | `ProblemStatement.lean`; `Erdos287Counterexample` |
| Ordered public statement compiler | PUBLIC LEAN-CHECKED | `erdos287_seq_of_no_counterexample` |
| Adjacent-hole obstruction | PUBLIC LEAN-CHECKED | `Gap2CE.holes_isolated` |
| Prime-power window blocker | PUBLIC LEAN-CHECKED | `Gap2CE.blocker_window` |
| Finite exclusion to 4e9 | PUBLIC LEAN-CHECKED | `no_Erdos287Counterexample_of_max_le_4e9` |
| Exact large-M predicate | PUBLIC LEAN-CHECKED DEFINITION | `WindowPairSupply` |
| End-to-end compiler | PUBLIC LEAN-CHECKED / CONDITIONAL | `no_Erdos287Counterexample_of_closure` |
| V14 Vaughan structural spine | PUBLIC LEAN-CHECKED ALGEBRA | `Erdos287VaughanV14Status.lean` |

## B. Midpoint V15 formalization source

These files were present in the supplied midpoint archive but were not on public `main` at the audit cutoff. Status: **FORMALIZATION REPLAY PENDING**.

- `AffineMuLogIdentity.lean`
- `AffineMuLogHardSource.lean`
- `AffineMuLogLine.lean`
- `AffineMuLogExponentLedger.lean`
- `BalancedSevenFinite.lean`
- `BalancedSevenPolarization.lean`
- `Erdos287V15Status.lean`

The archive SHA-256 is:

```text
609b139eb09a69b6ed39654e661dd3ea50d0e590eee371dbed18d014f4b5cb4e
```

Static source audit: no Lean-code `sorry`, `admit`, user `axiom`, `opaque`, `unsafe`, `native_decide`, or `@[implemented_by]` detected. Independent V15 kernel replay was not performed in the present environment.

## C. Current analytic branches

### C1. Source-minimal hard μ-log branch

Exact source:

```math
Λ(2mn+s)=Σ_{qr=2mn+s} μ(q)log r,
```

with hard class `q,r>U` and determinant-one relation

```math
qr-2mn=s=±1.
```

Status:

- exact identity / partition / affine line: algebraically proved;
- analytic hard-line cancellation: OPEN;
- physical comparison matching: OPEN;
- V14 prime-modulus Möbius two-outer packet: valid alternative child, not the source-minimal parent.

### C2. Balanced-seven V-branch

Source scale:

```math
Q=X^(3/5), Y=X^(1/7).
```

| Node | Status |
|---|---|
| Character parent | PASS algebraically |
| Separate multiplicative LS | NONCLOSING: `X^(1/10)` deficit |
| Separate high moments | NONCLOSING: same deficit |
| Equal-seven P6.3 dictionary | FALSE |
| Prime-box termwise repair | NONEXHAUSTIVE |
| Modulus micro-switch | NONEXHAUSTIVE |
| Repeated-prime router | PASS: `X^(6/7+o(1))` |
| Squarefree torus polarization | PASS algebraically |
| Smooth class-C dictionary | PASS algebraically |
| `AFFINE287-POLARIZED-OMEGA7-SIGNED-EOD45` | OPEN ANALYTIC |
| `AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45` | OPEN SOURCE |
| Balanced-seven cell | REDUCED, NOT CLOSED |

Exact compiler:

```text
POLARIZED-OMEGA7-SIGNED-EOD45
+ MULOG-COMPARISON-LOWCOND-MATCH45
=> BALANCED7-MODULUS-AVERAGE45 CLOSED.
```

## D. Downstream closure ledger

```text
finite exact theorem                          PUBLIC LEAN-CHECKED
WindowPairSupply compiler                     PUBLIC LEAN-CHECKED / CONDITIONAL
source-minimal affine algebra                 EXACT; V15 replay pending
balanced-seven polarization                   EXACT; V15 replay pending
hard μ-log cancellation                       OPEN
polarized signed EOD                          OPEN
comparison low-conductor match                OPEN
remaining fixed-g_* packet census             OPEN
fixed-certificate leakage / FCL               OPEN
positive affine prime/almost-prime mass       OPEN
large-M WindowPairSupply                      OPEN
effectivity / final bridge                    OPEN
Erdős #287                                    OPEN
```

## E. Failed or retired direct routes

These statements are not hidden; they are separated from the public paper because they are route diagnostics, not main results.

- Direct singleton = Gate-1B common-conductor packet: **FALSE by source provenance/coprimality**.
- Literal Vaughan cofactor well-factorability: **FALSE**.
- Direct canonical Gate-1A determinant adapter: **FAIL** (`2k` versus determinant `±1`).
- Equal-seven Pascadi Proposition 6.3 dictionary: **FALSE**.
- Ordinary separate multiplicative large sieve: **NONCLOSING**.
- Modulus micro-switch as exhaustive closure: **FALSE/NONEXHAUSTIVE** because prime moduli survive.
- V14 Vaughan route itself: **NOT FALSE**; retained as a valid nonminimal alternative source decomposition.

## F. Archive policy

- `archive/ERDOS287_TECHNICAL_DOSSIER_V15_PATCHSTACK.pdf`: immutable previous public patch-stack PDF.
- `archive/PUBLIC_REVIEW_DRAFT15_PATCHSTACK.tex`: immutable previous source.
- Historical dated files under `frontier/`: preserved, not treated as current controlling status.
- `ERDOS287_PUBLIC_REVIEW_CURRENT.pdf`: canonical clean public paper.
- `ERDOS287_PUBLIC_REVIEW_DRAFT_V2_FINAL.pdf`: legacy forum path, now an alias to the canonical clean paper.
