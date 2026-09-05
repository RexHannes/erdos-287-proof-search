# Reviews and Audits

This directory is a navigation layer for review evidence. It does not replace the original formal modules or archived audit reports.

## Current audited release

The R12 release keeps its review-critical material together:

- [`../paper/audited-release/2026-09-05-r12/audit/STATUS_LEDGER.md`](../paper/audited-release/2026-09-05-r12/audit/STATUS_LEDGER.md)
- [`../paper/audited-release/2026-09-05-r12/audit/SOURCE_PROVENANCE_AND_PRECEDENCE.md`](../paper/audited-release/2026-09-05-r12/audit/SOURCE_PROVENANCE_AND_PRECEDENCE.md)
- [`../paper/audited-release/2026-09-05-r12/audit/FORMAL_MODULE_MAP.md`](../paper/audited-release/2026-09-05-r12/audit/FORMAL_MODULE_MAP.md)

## Formal / Aristotle source

Lean source and formal audit modules remain under [`../RequestProject/`](../RequestProject/) to preserve import paths. Historical formal audit reports that formerly occupied the repository root are archived under [`../archive/historical-reports/`](../archive/historical-reports/).

## Reading rule

An audit report may certify only the claims and scope it explicitly checks. In particular, kernel-checked finite algebra is not treated as an analytic theorem, and a live candidate research result is not treated as audited merely because related formal interfaces exist.
