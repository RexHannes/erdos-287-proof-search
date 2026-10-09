# Aristotle source sync — 9 October 2026

**Erdős #287 remains OPEN. This is a source import, not an independent mathematical audit or a proof of the infinite tail.**

The uploaded `f3680730-21fd-4bc3-b8e9-fac9ae820a7d-aristotle (7).tar.gz` was compared against main at `8e0f6d81912a307b060d78237582d8ae1bb65856`, both by original path and by content hash across the reorganised repository.

## Imported material

- 667 additional Lean files under `RequestProject/Erdos287/`, including the research banks, `CurrentTail`, `SourceChain`, physical-source modules and the V100R4S W₄ ledger.
- 89 original Markdown documents, including Aristotle's README, preserved verbatim under [`archive/aristotle/2026-10-09/`](../archive/aristotle/2026-10-09/).
- The subtree audit scripts, external prime-gap transcription cross-check sources/logs, and [`scripts/erdos287_source_fit_audit.py`](../scripts/erdos287_source_fit_audit.py).
- Ten additional imports in `RequestProject/Main.lean`; every pre-existing import is retained.

486 files already present at the same path or elsewhere in the repository were not duplicated. The existing `scripts/certs_body.lean` differs only by a trailing blank line and was retained. Generated Python bytecode was omitted. No pre-existing Lean theorem was replaced or deleted. The toolchain, Mathlib manifest, historical release and public-review PDFs are unchanged.

The complete [import manifest](../archive/aristotle/2026-10-09/IMPORT_MANIFEST.json) maps all 1,257 incoming files to their repository locations or records the reason for omission. Its `sha256` fields refer to the exact incoming bytes. `Main.lean` is an import-preserving merge, so its incoming hash is not the hash of the merged file.

Source archive SHA-256:

```text
b752093fb38e9cf8097f6f3b7e007d6742da9f642a4508067ac43e5abc08d408
```

## Source entry points and exact scope

| Entry | Scope recorded in the incoming material |
|---|---|
| [Current repository census](../archive/aristotle/2026-10-09/ERDOS287_CURRENT_REPOSITORY_CENSUS.md) | Inventory and reported Aristotle builds; historical source claims are not a new local audit. |
| [Actual atom / positive W₄ report](../archive/aristotle/2026-10-09/ERDOS287_ACTUAL_ATOM_W4_FORMAL_REPORT.md) | Conditional tail compilers; physical-source construction and substantive analytic providers remain open. |
| [V100R4S W₄ ledger](../archive/aristotle/2026-10-09/ERDOS287_V100R4S_W4_LEDGER_REPORT.md) | Ratio/exponent algebra and the conditional kernel chain; no unconditional `Tail287Statement`. |
| [Complete W₄ landing source](../archive/aristotle/2026-10-09/05_ERDOS287_PROOFS_W4_LANDING_UPDATED.md) | Complete supplied written source and its hypotheses; author-candidate proof and independent audit status remain distinct. |
| [SourceChain aggregator](../RequestProject/Erdos287/SourceChain.lean) | Imports the formal source, physical interfaces, W₄ ledger and audit modules. |
| [SourceChain repair audit](../RequestProject/Erdos287/SourceChain/RepairAudit.lean) | Prints axiom dependencies of the repair and W₄ results. |

Paths cited inside verbatim reports are the original Aristotle project paths. Use the manifest when a report or input document was moved into this dated archive. The imported `audit.sh` files are also verbatim: their original root-commit/protected-file checks refer to Aristotle's own project history and should not be read as checks of this public repository's distinct history.

## Verification

The sync checks every unchanged/copied source against the manifest, resolves project-local Lean imports, and scans new project Lean code with nested comments and strings excluded. The finite Python replay checks five parity fixtures and the LCM ledger through 1,249; those are finite regressions, not infinite-tail proofs.

Full compilation uses the existing Lean 4.28.0 toolchain and pinned Mathlib dependency:

```bash
lake exe cache get
lake build
lake build RequestProject.Erdos287.SourceChain.RepairAudit
python scripts/erdos287_source_fit_audit.py
```

Local checks passed: all 1,254 byte-exact manifest entries, 2,725 project-local import references, the new-source forbidden-token scan, the finite Python replay and the sync-index links. No new project Lean code contains `sorry`, `admit`, an `axiom` declaration, `native_decide`, `unsafe` or `implemented_by` after comments and strings are excluded.

The local Lean 4.28.0 executable could not start in the editing environment (`error: failed to locate application`), so a local full build is not claimed. The [Lean source workflow](../.github/workflows/lean.yml) performs the full build and W₄ repair audit on GitHub. Its result is available in the Actions run for the sync commit; until that run succeeds, compilation of the merged public tree is pending. The original Aristotle build reports are preserved as reported evidence, not substituted for this replay.

A successful build validates the formal statements with their explicit hypotheses; it does not discharge an analytic provider.
