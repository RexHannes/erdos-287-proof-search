# Erdős #287 Effectivity — Audited Synthesis R12

**Release date:** 5 September 2026
**Status:** research draft; **Erdős Problem #287 remains open**.

This release converts the current Aristotle/Lean bank and the latest long-fibre research report into a full journal-style mathematical manuscript. It is deliberately not a compressed progress memo. It preserves the physical source normalisation, the corrected odd half-divisor chart, the `c=1/c=2` splice, the diagonal Euler-product cancellation, the Perron algebra, the exact counterexample to the retired unweighted joined theorem, the corrected `lambda(b)`-weighted norm, the `V<1000` finite edge certificate, the complete-period Farey covariance, the all-`q` resummation, the exact numerical ledger, and every downstream open guard.

## Principal files

- `ERDOS287_EFFECTIVITY_AUDITED_SYNTHESIS_R12_05SEP2026.tex` — full journal-style LaTeX source.
- `ERDOS287_EFFECTIVITY_R12_AUDIT/docs/STATUS_LEDGER.md` — compact authoritative status and capacity ledger.
- `ERDOS287_EFFECTIVITY_R12_AUDIT/docs/SOURCE_PROVENANCE_AND_PRECEDENCE.md` — source order, hashes, and discrepancy resolutions.
- `ERDOS287_EFFECTIVITY_R12_AUDIT/docs/FORMAL_MODULE_MAP.md` — theorem-to-Lean-module map and scope firewall.
- `ERDOS287_EFFECTIVITY_R12_AUDIT/certificates/ERDOS287_LONGFIBRE_PIVOT_CERTIFICATE.json` — exact/fixed-point numerical certificate.
- `ERDOS287_EFFECTIVITY_R12_AUDIT/scripts/erdos287_longfibre_pivot_verifier.py` — deterministic certificate generator.
- `ERDOS287_EFFECTIVITY_R12_AUDIT/source_reports/` — current analytic and audit reports retained as provenance.

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

## Reproduce the numerical certificate

```bash
python3 ERDOS287_EFFECTIVITY_R12_AUDIT/scripts/erdos287_longfibre_pivot_verifier.py
```

Expected terminal status:

```text
STRICT_REDUCTION_NOT_CLOSURE
```

The verifier certifies the summatory `lambda` bound, the entire `V<1000` edge, the aggregate threshold arithmetic, the complete-period endpoint main term, the revised directed ledger, and 800 exact all-`q` regression checks. It explicitly does **not** certify the remaining covariance, medium-`k`, two-high, signed floor, Maynard effectivisation, or Erdős #287.

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