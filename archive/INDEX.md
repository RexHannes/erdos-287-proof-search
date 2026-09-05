# Historical Archive Index

This archive preserves superseded manuscripts, research safe banks, transport/source packages, status snapshots, and earlier frontier notes. **Substantial mathematical content is moved, not discarded.** Git history remains intact.

The purpose of `archive/` is research archaeology: old work remains reviewable without competing with the current proof map.

## Current navigation precedence

Do not infer current authority from a filename, date, or revision number in this archive. Use:

1. [`../PROOF_MAP.md`](../PROOF_MAP.md) — current dependency graph;
2. [`../CURRENT_STATUS.md`](../CURRENT_STATUS.md) and [`../CLAIMS_LEDGER.md`](../CLAIMS_LEDGER.md) — status/evidence firewall;
3. [`../banked/`](../banked/) — trusted inputs by evidence class;
4. [`../frontier/`](../frontier/) — current parent / candidates / downstream;
5. [`../graveyard/`](../graveyard/) — false, retired, superseded routes.

## Legacy path map

| Former location | New location | Meaning |
|---|---|---|
| `.frontier-src/` | `archive/source-packages/frontier-v12/` | historical transport source |
| `.public-review-src/` | `archive/source-packages/public-review/` | historical public-review source packages |
| `.r4-src/` | `archive/source-packages/r4/` | R4 transport source |
| `.r5-src/` | `archive/source-packages/r5/` | R5 transport source |
| `.r7-src/` | `archive/source-packages/r7/` | R7 transport source |
| `.v16-src/` | `archive/source-packages/v16/` | V16 transport bundle |
| `.r12-src/` source parts | `paper/audited-release/2026-09-05-r12/source-package/` | current audited R12 source package |
| legacy `.r12-src/README.md` | `archive/source-packages/r12/LEGACY_R12_SOURCE_README.md` | exact old reconstruction note retained |
| old `frontier/` contents | `archive/frontier-legacy/` | superseded dated/frontier notes |
| `RESEARCH_FRONTIERS/` | `archive/research-frontiers-legacy/` | former proof indexes/frontier navigation |
| old root safe-bank/research reports | `archive/historical-reports/` | provenance only unless re-cited by a current bank/release |
| old root public-review manuscripts | `archive/public-review/` | historical review snapshots |
| 2 Sep R10 `CURRENT_STATUS.md` | `archive/status/2026-09-02-r10-current-status.md` | superseded status snapshot |
| 2 Sep R10-era `README.md` | `archive/status/2026-09-02-r10-readme.md` | superseded landing page |

## Why files are moved instead of deleted

Historical reports repeatedly contain useful source dictionaries, counterexamples, retractions, local identities, and exact intermediate reductions. Moving them into the archive changes only their **authority for current navigation**.

A route can be archived because it is superseded while still containing correct mathematics. For proof-search disposition, consult `graveyard/` rather than treating `archive/` as synonymous with “false”.

## Current semantic naming

The public ontology is now role-based:

```text
banked/
frontier/
graveyard/
archive/
```

Within dated artifacts, semantic names remain useful, for example:

```text
paper/audited-release/2026-09-05-r12/
frontier/current-parent/
frontier/candidate-results/
```

Internal manuscript identifiers such as `R12`, `V16`, or older gate names remain inside historical artifacts where they help provenance, but they no longer determine top-level authority.
