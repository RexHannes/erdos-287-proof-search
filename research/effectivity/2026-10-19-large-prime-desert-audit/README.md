# Large-prime-row desert — scoped audit

**Audit: REPAIR -> PASS at paper-proof scope. AC-287 and Global #287 remain OPEN.**

Start with REPORT.md. CLOSING_CONTRACT.md separates proved implications from the
unproved every-scale two-prime existence statement. No original finite-bank or
pre-effectivity file is modified by this packet.

Run with Python standard library:

```sh
python -S verify_desert.py --output normal.json
python -S -O verify_desert.py --output optimized.json
cmp normal.json optimized.json
python -S verify_desert.py --extract-sources recovered --output restored_check.json
```

SOURCE_RECORD.md.gz preserves the complete UTF-8 source record byte-for-byte.
The verifier reads either the plaintext or the compressed form automatically.
The archive embeds all six original large-prime-desert files and the complete
controlling consumer report, with byte counts and SHA-256. The original claims
remain historical: this audit certifies only its own explicitly stated scope.
To materialize the readable source record and check the manifest:

```sh
gzip -dk SOURCE_RECORD.md.gz
sha256sum -c SHA256.txt
```

CERTIFICATE.json contains exact starting inequalities, numerator/LCM integers,
source hashes and finite regression results. VERIFICATION.json records actual
normal/optimized runs and 16 rejected negative-control executions. These do not
constitute an external theorem proof, a Lean build, a human referee report,
a finite-bank replay, or an AC-287 existence proof.
