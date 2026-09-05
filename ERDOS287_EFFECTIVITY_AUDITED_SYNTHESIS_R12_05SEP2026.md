# Erdős #287 Effectivity — Audited Synthesis R12

**Release date:** 5 September 2026  
**Status:** research draft; **Erdős Problem #287 remains open**.

This release converts the current Aristotle/Lean bank and the latest long-fibre research report into a full journal-style mathematical manuscript. It is deliberately not a compressed progress memo. It preserves the physical source normalisation, the corrected odd half-divisor chart, the `c=1/c=2` splice, the diagonal Euler-product cancellation, the Perron algebra, the exact counterexample to the retired unweighted joined theorem, the corrected `lambda(b)`-weighted norm, the `V<1000` finite edge certificate, the complete-period Farey covariance, the all-`q` resummation, the exact numerical ledger, and every downstream open guard.

## Principal files

- `.r12-src/erdos287_r12.tex.gz.b64.head00` through `head02`, followed by `part01` and `part02` — lossless gzip/base64 chunks of the complete journal LaTeX source.
- `.r12-src/README.md` — reconstruction instructions and controlling source/PDF hashes.
- `.github/workflows/build-erdos287-effectivity-r12.yml` — reconstructs the exact LaTeX source, verifies its SHA-256, compiles the manuscript, and publishes TeX/PDF workflow artifacts.
- `ERDOS287_EFFECTIVITY_R12_AUDIT/docs/STATUS_LEDGER.md` — authoritative status and capacity ledger.
- `ERDOS287_EFFECTIVITY_R12_AUDIT/docs/SOURCE_PROVENANCE_AND_PRECEDENCE.md` — source order, hashes, and discrepancy resolutions.
- `ERDOS287_EFFECTIVITY_R12_AUDIT/docs/FORMAL_MODULE_MAP.md` — theorem-to-Lean-module map and scope firewall.
- `ERDOS287_EFFECTIVITY_R12_AUDIT/docs/CHANGELOG_R12.md` — material changes and retired routes.
- `ERDOS287_EFFECTIVITY_R12_AUDIT/certificates/ERDOS287_LONGFIBRE_PIVOT_CERTIFICATE.json` — exact/fixed-point certificate produced by the audited replay package.

The reconstructed LaTeX source has SHA-256

```text
62bbb029fa34cc0f251e6be35c97adaf399ac6811664fdc8cb037c7b09904b31
```

and the locally audited 36-page reference PDF has SHA-256

```text
c84f0516896794ade6d93a0c926cd5d599ce3a922a7fbe166356e8ea89b0b324
```

## Authoritative frontier

| Node | Status |
|---|---|
| Certified subtotal | `5.257263872e-7` |
| Remaining capacity | `3.603386128e-7` |
| `V<1000` edge | **FINITE-CERTIFIED / AUDITED / CLOSED** |
| Aggregate sufficient target | `C_agg <= 69/5000` |
| Complete-period endpoint | `< 469/75000` |
| Remaining covariance allowance | `283/37500` |
| Medium-`k` | **STRICTLY REDUCED / OPEN** |
| Two-high | **OPEN / NOT ENTERED** |
| Signed floor | **OPEN** |
| Maynard stage | **OPEN / NOT ENTERED** |
| Erdős Problem #287 | **OPEN** |

The sufficient aggregate constant is a conditional closure criterion. The required physical covariance theorem itself is not proved. The remaining live obligation can be expressed either as

```text
C_F + 2 C_ED + C_DD + C_S < 283/37500,
```

or as the equivalent uniform smooth singular-series discrepancy after exact all-`q` resummation. These are two formulations of the same physical residual and must not be charged twice.

## Reconstruct and compile the full manuscript

From the repository root:

```bash
cat .r12-src/erdos287_r12.tex.gz.b64.head00 \
    .r12-src/erdos287_r12.tex.gz.b64.head01 \
    .r12-src/erdos287_r12.tex.gz.b64.head02 \
    .r12-src/erdos287_r12.tex.gz.b64.part01 \
    .r12-src/erdos287_r12.tex.gz.b64.part02 \
  | base64 -d | gzip -dc \
  > ERDOS287_EFFECTIVITY_AUDITED_SYNTHESIS_R12_05SEP2026.tex

sha256sum ERDOS287_EFFECTIVITY_AUDITED_SYNTHESIS_R12_05SEP2026.tex
latexmk -pdf ERDOS287_EFFECTIVITY_AUDITED_SYNTHESIS_R12_05SEP2026.tex
```

The committed finite certificate has global status

```text
STRICT_REDUCTION_NOT_CLOSURE
```

and explicitly does **not** certify the remaining covariance, medium-`k`, two-high, signed floor, Maynard effectivisation, or Erdős #287.

## Status vocabulary

Every substantive assertion is classified as one or more of:

- **KERNEL-PROVED** — accepted by the supplied Lean kernel at the stated finite/algebraic scope;
- **FINITE-CERTIFIED** — checked by deterministic exact or outward-rounded finite computation;
- **ANALYTICALLY-PROVED** — supplied with a paper proof at its stated hypotheses;
- **AUDITED** — independently replayed or checked against the retained source bank;
- **CONDITIONAL** — a correct implication whose hypothesis remains unproved;
- **OPEN** — a live missing theorem, estimate, or physical instantiation;
- **RETIRED** — false, source-mismatched, quantitatively nonclosing, or superseded.

No label may be silently promoted across these categories.
