# Project contamination audit — 1 September 2026

## Repository audited

`RexHannes/erdos-287-proof-search`

## Active scope

Erdős Problem #287 only.

## 1-Sep update result

The new update contains only #287-owned status, source-neutral finite algebra, direct3221/K0-SP2 interfaces, current public status/frontier documents, and CI/scope firewalls.

The separate Twin-Prime / Gate-1B Aristotle bundle supplied in the surrounding research workflow is **not imported into this #287 update**.

The living formal entrypoint is

```text
RequestProject/CurrentErdos287.lean
```

and its base spine is `RequestProject/Main.lean`.

Direct audit confirms that neither entrypoint imports the legacy `RequestProject/TrustedBank/Gate1A/*` or `RequestProject/TrustedBank/Gate1B/*` modules.

## Pre-existing legacy cross-project names

A deeper whole-tree audit found historical trusted-bank/challenge/status files carrying `Gate1A` / `Gate1B` names. Examples include the old centered-divisibility, squarefree-Möbius-collapse, separable-weight and same-start-injectivity banks.

These files predate the 1-Sep update. Their mathematical cores are finite/source-neutral in several cases, but their project labels belong to an older mixed research-bank phase.

They are therefore classified as:

```text
LEGACY / NONCONTROLLING / NOT IMPORTED BY THE LIVING #287 ENTRYPOINT.
```

They remain in the tree for provenance and reproducibility of historical runs; Git compilation of a legacy module is not theorem ownership and does not make it an analytic input to the current #287 programme.

No legacy problem-specific status/source/compiler statement may enter the current #287 chain without an explicitly #287-owned reintroduction and fresh audit.

## Automated firewall

CI checks:

1. full Lean compilation;
2. the living `RequestProject/Main.lean` / `RequestProject/CurrentErdos287.lean` entrypoints for active cross-project imports/labels;
3. current README/status/frontier files for active `GATE1B`, `TWIN_PRIME`, `FM722`, or `HSTAR` ownership;
4. the new Sep-1 modules for forbidden proof shortcuts.

## Public-status firewall

```text
ERDOS287: OPEN
```

The paper/research closure of the physical Balanced7 direct3221 endpoint is not promoted to the generic arbitrary-`A` socket, the full source-reassembly theorem, or the final problem statement.
