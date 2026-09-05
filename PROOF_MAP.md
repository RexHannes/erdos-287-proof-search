# Erdős Problem #287 — Public Proof Map

**Global status: OPEN. No solution is claimed.**

This file is the public navigation layer for the proof-search programme. It separates the latest independently audited release from live candidate research. A candidate result does **not** supersede the audited ledger until it has been independently reviewed and incorporated into a later audited release.

## 1. Proof DAG

```text
ERDŐS #287
│
├── finite exact bank
│     └── finite exclusion / certificate layer
│           AUDITED / FORMAL + COMPUTATIONAL
│           (existing finite bank retained)
│
├── asymptotic / source bank
│     └── substantial source and compiler reductions
│           FORMAL / PAPER-BANKED at stated scopes
│
└── effectivity
      │
      ├── AUDITED RELEASE — 2026-09-05 R12
      │     │
      │     ├── V < 1000 edge
      │     │     CLOSED — FINITE-CERTIFIED / AUDITED
      │     │
      │     ├── complete-period endpoint main
      │     │     CLOSED — KERNEL-PROVED / FINITE-CERTIFIED / AUDITED
      │     │
      │     ├── remaining weighted covariance
      │     │     OPEN
      │     │     target:
      │     │       C_F + 2 C_ED + C_DD + C_S < 283/37500
      │     │
      │     └── medium-k
      │           STRICTLY REDUCED / OPEN
      │
      └── LIVE CANDIDATE FRONTIER — 2026-09-05
            │
            ├── primitive/static r <= 200
            │     CANDIDATE-CLOSED / NOT YET AUDITED
            │
            ├── moving Ramanujan window
            │     CANDIDATE-REMOVED / SUPERSEDED
            │
            └── static signed r > 200 tail
                  OPEN
                  │
                  ├── medium-k
                  │     OPEN
                  ├── two-high
                  │     NOT ENTERED
                  ├── signed floor
                  │     OPEN
                  └── Maynard effectivization
                        NOT ENTERED
```

## 2. Audited release

The current audited baseline is **R12, 5 September 2026**.

| Quantity / node | Audited status |
|---|---|
| Target capacity | `8.86065e-7` |
| Certified subtotal | `5.257263872e-7` |
| Remaining capacity | `3.603386128e-7` |
| `V<1000` edge | **CLOSED** |
| Aggregate sufficient target | `C_agg <= 69/5000` — conditional criterion |
| Complete-period endpoint | `< 469/75000` |
| Residual covariance allowance | `283/37500` |
| Medium-`k` | **STRICTLY REDUCED / OPEN** |
| Two-high | **OPEN / NOT ENTERED** |
| Signed floor | **OPEN** |
| Maynard stage | **OPEN / NOT ENTERED** |
| Erdős #287 | **OPEN** |

Primary audited evidence:

- [`paper/audited-release/2026-09-05-r12/README.md`](paper/audited-release/2026-09-05-r12/README.md)
- [`paper/audited-release/2026-09-05-r12/audit/STATUS_LEDGER.md`](paper/audited-release/2026-09-05-r12/audit/STATUS_LEDGER.md)
- [`paper/audited-release/2026-09-05-r12/audit/FORMAL_MODULE_MAP.md`](paper/audited-release/2026-09-05-r12/audit/FORMAL_MODULE_MAP.md)
- [`paper/audited-release/2026-09-05-r12/certificates/ERDOS287_LONGFIBRE_PIVOT_CERTIFICATE.json`](paper/audited-release/2026-09-05-r12/certificates/ERDOS287_LONGFIBRE_PIVOT_CERTIFICATE.json)

## 3. Live candidate frontier

The latest research-session candidate is kept separately at:

- [`frontier/2026-09-05-static-ramanujan/FRONTIER.md`](frontier/2026-09-05-static-ramanujan/FRONTIER.md)

The candidate snapshot records a proposed subtotal `6.341463872e-7` and proposed remaining global capacity `2.519186128e-7`, with the surviving static signed `r>200` tail open. These numbers are **not part of the audited R12 ledger**.

## 4. Formal verification

The Lean source remains under [`RequestProject/`](RequestProject/) to preserve import paths and reproducibility. The public formal map for R12 is linked above. Formal statements are only attributed the scope actually checked by the kernel; finite algebra, conditional compilers, analytic estimates, and instantiated numerical certificates are not silently conflated.

## 5. Status vocabulary

- **KERNEL-PROVED** — checked by Lean at the stated finite/algebraic scope.
- **FINITE-CERTIFIED** — checked by deterministic exact or outward-rounded finite computation.
- **ANALYTICALLY-PROVED** — supplied with a paper proof under the stated hypotheses.
- **AUDITED** — independently replayed or checked against the retained source bank.
- **CANDIDATE** — live research output not yet promoted into the audited baseline.
- **CONDITIONAL** — a correct implication with an unproved hypothesis.
- **OPEN** — a live missing theorem, estimate, or physical instantiation.
- **RETIRED / SUPERSEDED** — false, source-mismatched, quantitatively nonclosing, or replaced by a later formulation.

## 6. Historical provenance

Historical review manuscripts, safe-bank reports, transport/source packages, and superseded frontier documents are preserved under [`archive/`](archive/). See [`archive/INDEX.md`](archive/INDEX.md) for the legacy-path map. Git history is retained; this reorganisation changes navigation, not mathematical provenance.
