# Historical Archive Index

This archive preserves superseded manuscripts, research safe banks, transport/source packages, status snapshots, and earlier frontier notes. **Nothing is deleted from Git history.** The purpose of the archive is to keep research archaeology available without making historical material look current on the repository landing page.

## Public precedence

For current mathematical status, do **not** infer authority from a filename or revision number in this archive. Use:

1. [`../CURRENT_STATUS.md`](../CURRENT_STATUS.md)
2. [`../CLAIMS_LEDGER.md`](../CLAIMS_LEDGER.md)
3. latest release under [`../paper/audited-release/`](../paper/audited-release/)
4. live candidate work under [`../frontier/`](../frontier/)

## Legacy path map

| Former location | New archive location | Meaning |
|---|---|---|
| `.frontier-src/` | `archive/source-packages/frontier-v12/` | historical transport source |
| `.public-review-src/` | `archive/source-packages/public-review/` | historical public-review source packages |
| `.r4-src/` | `archive/source-packages/r4/` | R4 transport source |
| `.r5-src/` | `archive/source-packages/r5/` | R5 transport source |
| `.r7-src/` | `archive/source-packages/r7/` | R7 transport source |
| `.v16-src/` | `archive/source-packages/v16/` | V16 transport bundle |
| `.r12-src/` | `paper/audited-release/2026-09-05-r12/source-package/` | **current audited R12 source package**, not historical |
| old `frontier/` contents | `archive/frontier-legacy/` | superseded dated/frontier notes |
| `RESEARCH_FRONTIERS/` | `archive/research-frontiers-legacy/` | former proof indexes/frontier navigation |
| old root safe-bank/research reports | `archive/historical-reports/` | provenance only unless re-cited by a current release |
| old root public-review manuscripts | `archive/public-review/` | historical review snapshots |
| 2 Sep R10 `CURRENT_STATUS.md` | `archive/status/2026-09-02-r10-current-status.md` | superseded status snapshot |
| 2 Sep R10-era `README.md` | `archive/status/2026-09-02-r10-readme.md` | superseded landing page |

## Why files are moved instead of deleted

Many historical reports contain source dictionaries, counterexamples, retractions, or exact intermediate reductions that remain useful for provenance. They therefore remain accessible here and through Git history. Their archived location means only that they are **not the controlling current status**.

## Revision naming

Going forward, public navigation uses date + semantic name, for example:

```text
paper/audited-release/2026-09-05-r12/
frontier/2026-09-05-static-ramanujan/
```

Internal manuscript revision identifiers such as `R12` or `V16` may remain inside artifacts, but they no longer determine the top-level repository ontology.
