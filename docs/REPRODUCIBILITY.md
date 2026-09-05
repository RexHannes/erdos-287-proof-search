# Reproducibility

This guide records the public replay paths after the repository reorganisation.

## 1. R12 manuscript

From the repository root:

```bash
SRC='paper/audited-release/2026-09-05-r12/source-package'
cat "$SRC/erdos287_r12.tex.gz.b64.head00" \
    "$SRC/erdos287_r12.tex.gz.b64.head01" \
    "$SRC/erdos287_r12.tex.gz.b64.head02" \
    "$SRC/erdos287_r12.tex.gz.b64.part01" \
    "$SRC/erdos287_r12.tex.gz.b64.part02" \
  | base64 -d | gzip -dc \
  > ERDOS287_EFFECTIVITY_AUDITED_SYNTHESIS_R12_05SEP2026.tex

sha256sum ERDOS287_EFFECTIVITY_AUDITED_SYNTHESIS_R12_05SEP2026.tex
```

Expected source SHA-256:

```text
62bbb029fa34cc0f251e6be35c97adaf399ac6811664fdc8cb037c7b09904b31
```

The current GitHub Actions workflow performs this exact hash check before compiling the manuscript.

## 2. Lean project

The formal source path is deliberately unchanged by the cleanup:

```text
RequestProject/
lakefile.toml
lake-manifest.json
lean-toolchain
```

With the repository dependencies available, the standard project replay is:

```bash
lake build
```

The R12 formal scope must be interpreted using

```text
paper/audited-release/2026-09-05-r12/audit/FORMAL_MODULE_MAP.md
```

A successful Lean build validates the encoded formal statements. It does not upgrade conditional analytic interfaces into proved physical estimates.

## 3. Numerical certificate

The current R12 certificate is

```text
paper/audited-release/2026-09-05-r12/certificates/
  ERDOS287_LONGFIBRE_PIVOT_CERTIFICATE.json
```

Use the exact status ledger next to the certificate to determine what numerical conclusion is certified. In particular, the certificate records strict reduction, not complete effectivity closure.

## 4. Historical reconstruction

Earlier public-review source packages and transport fragments are preserved under

```text
archive/source-packages/
```

Legacy build workflows are preserved under

```text
archive/workflows/
```

They are intentionally outside `.github/workflows/` so that obsolete builds do not present themselves as current CI.

## 5. Provenance rule

Moving a file into `archive/` does not alter its contents. The cleanup uses existing Git blob/tree objects wherever possible, so the archived object hash remains a direct provenance anchor to its former root version.
