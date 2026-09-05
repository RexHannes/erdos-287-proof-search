# Audited Release — 2026-09-05 R12 Effectivity Synthesis

**Status:** audited research release.  
**Global verdict:** **Erdős Problem #287 remains OPEN.**

This directory is the canonical public home of the 5 September 2026 R12 effectivity synthesis. It supersedes earlier R-number documents for **public status navigation**, while preserving those documents under `archive/` for provenance.

## Audited capacity snapshot

```text
C_target = 8.860650000e-7
C_cert   = 5.257263872e-7
C_rem    = 3.603386128e-7
```

The exact rational identity `C_cert + C_rem = C_target` has been replayed.

The current audited mathematical frontier is:

```text
V < 1000 edge                     CLOSED
complete-period endpoint main     CLOSED
physical residual covariance      OPEN
medium-k                          STRICTLY REDUCED / OPEN
two-high                          OPEN / NOT ENTERED
signed floor                      OPEN
Maynard effectivization           OPEN / NOT ENTERED
Erdős #287                        OPEN
```

The residual covariance target is

\[
C_F+2C_{ED}+C_{DD}+C_S<\frac{283}{37500},
\]

with the physical outer `lambda(b)` weight retained.

## Contents

- `audit/STATUS_LEDGER.md` — exact audited capacity and downstream status.
- `audit/SOURCE_PROVENANCE_AND_PRECEDENCE.md` — source order and discrepancy handling.
- `audit/FORMAL_MODULE_MAP.md` — theorem-to-Lean map and formal-scope firewall.
- `audit/CHANGELOG_R12.md` — material changes and retired routes.
- `certificates/ERDOS287_LONGFIBRE_PIVOT_CERTIFICATE.json` — deterministic R12 certificate.
- `source-package/` — lossless text package for reconstructing the full journal LaTeX source.

## Reconstruct the manuscript

The source package is intentionally stored as text chunks for reproducibility through the connected GitHub workflow. The exact reconstruction command is documented in `source-package/README.md`; CI verifies the reconstructed source SHA-256 before compiling the PDF.

The expected reconstructed-source SHA-256 is

```text
62bbb029fa34cc0f251e6be35c97adaf399ac6811664fdc8cb037c7b09904b31
```

The locally audited 36-page reference PDF has SHA-256

```text
c84f0516896794ade6d93a0c926cd5d599ce3a922a7fbe166356e8ea89b0b324
```

## Evidence firewall

This release distinguishes:

- **KERNEL-PROVED** finite/algebraic statements;
- **FINITE-CERTIFIED** deterministic computations;
- **ANALYTICALLY-PROVED** paper arguments under stated hypotheses;
- **AUDITED** independently replayed claims;
- **CONDITIONAL** implications with missing hypotheses;
- **OPEN** live obligations.

No category is silently promoted into another.

For the current public proof DAG, see [`../../../PROOF_MAP.md`](../../../PROOF_MAP.md). For newer unaudited research, see [`../../../frontier/README.md`](../../../frontier/README.md).
