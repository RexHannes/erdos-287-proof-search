# R12 manuscript source

The full journal LaTeX source is stored as gzip/base64 text chunks so that the repository update remains text-only and byte-verifiable through the connected GitHub interface.

Reconstruct it from the repository root with:

```bash
cat .r12-src/erdos287_r12.tex.gz.b64.head00 \
    .r12-src/erdos287_r12.tex.gz.b64.head01 \
    .r12-src/erdos287_r12.tex.gz.b64.head02 \
    .r12-src/erdos287_r12.tex.gz.b64.part01 \
    .r12-src/erdos287_r12.tex.gz.b64.part02 \
  | base64 -d | gzip -dc \
  > ERDOS287_EFFECTIVITY_AUDITED_SYNTHESIS_R12_05SEP2026.tex
```

Expected SHA-256 of the reconstructed source:

```text
62bbb029fa34cc0f251e6be35c97adaf399ac6811664fdc8cb037c7b09904b31
```

The GitHub Actions workflow `build-erdos287-effectivity-r12.yml` performs this reconstruction, verifies the hash, and compiles the PDF as a workflow artifact. The locally audited reference PDF has SHA-256

```text
c84f0516896794ade6d93a0c926cd5d599ce3a922a7fbe166356e8ea89b0b324
```

The PDF is a rendered convenience artifact; the mathematical source, exact status ledger, provenance record and finite certificate are the reviewable controlling materials. Erdős Problem #287 remains open.

---

**Archive note.** This is the exact legacy `.r12-src/README.md` text preserved after the source chunks were moved to the semantic audited-release path. The current reconstruction instructions are in `paper/audited-release/2026-09-05-r12/source-package/README.md`.
