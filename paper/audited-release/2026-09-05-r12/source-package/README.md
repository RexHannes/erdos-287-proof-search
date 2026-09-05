# R12 manuscript source package

The full R12 journal LaTeX source is stored as gzip/base64 text parts so that the repository update remains text-only and reproducible through the connected GitHub interface.

From the repository root, reconstruct it with:

```bash
SRC='paper/audited-release/2026-09-05-r12/source-package'
cat "$SRC/erdos287_r12.tex.gz.b64.head00" \
    "$SRC/erdos287_r12.tex.gz.b64.head01" \
    "$SRC/erdos287_r12.tex.gz.b64.head02" \
    "$SRC/erdos287_r12.tex.gz.b64.part01" \
    "$SRC/erdos287_r12.tex.gz.b64.part02" \
  | base64 -d | gzip -dc \
  > ERDOS287_EFFECTIVITY_AUDITED_SYNTHESIS_R12_05SEP2026.tex
```

Expected SHA-256 of the reconstructed source:

```text
62bbb029fa34cc0f251e6be35c97adaf399ac6811664fdc8cb037c7b09904b31
```

The GitHub Actions workflow `.github/workflows/build-erdos287-effectivity-r12.yml` reconstructs this exact source, verifies the SHA-256, compiles the manuscript, and publishes TeX/PDF workflow artifacts.

The locally audited 36-page reference PDF has SHA-256

```text
c84f0516896794ade6d93a0c926cd5d599ce3a922a7fbe166356e8ea89b0b324
```

The PDF is a rendered convenience artifact. The mathematical source, exact status ledger, provenance record, formal map, and finite certificate are the controlling materials. Erdős Problem #287 remains open.
