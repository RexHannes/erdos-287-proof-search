# Erdős Problem #287 finite-search branch

The standalone finite-verification project supplied for this branch is in
[`finite-search/`](finite-search/README.md). Keeping it in its own project directory avoids
overwriting or colliding with the main repository's existing Lean development.

The supplied project verifies a finite exclusion through

```text
U2 = 3739298103962937078961175187719640178760086558841160733818922
```

This is a finite result only. Erdős Problem #287 remains open.

To replay the Lean project from this branch:

```sh
cd finite-search
lake build
```

The independent certificate audits documented by the project can be run with:

```sh
cd finite-search
python3 scripts/audit.py
python3 scripts/audit_u2.py
```
