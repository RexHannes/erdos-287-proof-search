# Source Provenance and Precedence — R12

## Authoritative source order

The manuscript applies the following order whenever retained sources disagree:

1. the uploaded Aristotle formal/status bank, especially the effectivity kernel and 4 September signed-floor reports;
2. the latest long-fibre research report and its generated exact-rational certificate;
3. the half-divisor audit/repair report;
4. the joined-square-function hostile audit;
5. earlier source-bank statements only where not superseded.

The newest independently replayed status is used. Incompatible claims are not silently merged.

## Source hashes

| Source | SHA-256 |
|---|---|
| Uploaded `aristotle (2).tar.gz` | `5afff42b00b4f9ff74e042e28af505662581e611b6d9eb90e2a086f9da99840c` |
| `GOLD_ERDOS287_LONGFIBRE_FREEPIVOT_RESULT.md` | `2da7fd1ec915cc10f73b18dbf7b6a8c3956f51b214ac2fd81b10efa8111963b7` |
| `GOLD_ERDOS287_HALFDIVISOR_AUDIT_REPAIR_RESULT.md` | `5fb92a408cf8f6095bf946205c313157ed74480512b1cb56afa21f0ebe658a55` |
| `GOLD_ERDOS287_JOINED_SQUAREFUNCTION_AUDIT_RESULT.md` | `12dbd4a5bc98850b7c193c51f1a1923ac80a693c8191c15a4b7d3c99c60c22cf` |
| R12 LaTeX source | `62bbb029fa34cc0f251e6be35c97adaf399ac6811664fdc8cb037c7b09904b31` |
| R12 PDF | `c84f0516896794ade6d93a0c926cd5d599ce3a922a7fbe166356e8ea89b0b324` |

The release manifest recomputes the final artifact hashes after all packaging files are added.

## Explicit discrepancy resolutions

### 1. Physical singular-series normalisation

A September abstract local model could be read as attaching a global singular-series factor at each prime. That interpretation is retired. The physical normalisation is

\[
B_{\rm src}(n)=\mathfrak S_2 B_0(n),
\]

and the displayed typed multiplicativity is

\[
\mathfrak S_2 B_{\rm src}(ab)=B_{\rm src}(a)B_{\rm src}(b)
\]

for disjoint odd squarefree inputs. The global factor occurs exactly once.

### 2. Joined square-function target

The unweighted fibrewise theorem `C_joint <= 0.09` is retired because the hostile audit constructs an exact physical one-point fibre with `C_joint >= 9/64`. The live norm retains

\[
\lambda(b)=\prod_{p\mid b}\frac{p-1}{(p-2)^2}.
\]

This is a change of theorem, not merely a sharpening of a constant.

### 3. Edge replacement

The old `V<50` charge `<2.459e-8 B_X` is removed. It is replaced, not supplemented, by the deterministic `V<1000` charge `<7.22e-10 B_X`.

### 4. Current subtotal

After that replacement, the authoritative current subtotal is `5.257263872e-7`, not the earlier `5.495943872e-7` subtotal and not the separate historical kernel subtotal `5.2188738751e-7`.

### 5. Aggregate normalisation coefficient

The manuscript uses the conservative exact-replay value

```text
3.0650024384947045e-6
```

rather than the slightly smaller prose approximation from an earlier narrative pass.

### 6. Complete-period versus terminal covariance

The exact Farey identity closes the complete-period endpoint main only. The finite-period remainder, endpoint–derivative covariance, derivative–derivative covariance, and no-lattice splice remain open with total allowance `283/37500`.

### 7. Equivalent open charts

The weighted `F/ED/DD/S` covariance route, the exact all-`q` smooth singular-series discrepancy route, and the half-divisor/Perron route describe the same physical residual from different coordinates. They are not three independent error terms and receive only one capacity allocation.

## Reproducibility boundary

The manuscript distinguishes finite kernel identities from infinite analytic uses. In particular:

- finite `Z_P(s,s)=0` is kernel-checked;
- infinite `Z(s,s)=0` is asserted only in the displayed absolute-convergence region;
- Perron contour movement and the directed anti-diagonal tail retain explicit hypotheses;
- the signed-floor modules establish structural compilers but do not instantiate a physical boundary-event certificate;
- the packaged Python verifier certifies only the items listed in its JSON output.
