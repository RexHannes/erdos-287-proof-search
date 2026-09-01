# Project scope — Erdős Problem #287

This repository is the authoritative public research/formalization record for **Erdős Problem #287**.

## Active-scope rule

The living status files, current frontier, living Lean entrypoint, and current source-owner graph must contain only #287-owned mathematics and #287-specific external inputs.

The living formal entrypoint is:

```text
RequestProject/CurrentErdos287.lean
```

It imports the established #287 `RequestProject.Main` spine and the newest #287 Sep-1 direct3221/K0-SP2 layer. Neither entrypoint imports the legacy `TrustedBank/Gate1A` or `TrustedBank/Gate1B` banks.

A result from another research programme is **not** an admissible theorem owner, source pin, analytic input, or closure certificate here merely because related sieve/Type-II terminology appears in both projects.

## Legacy-bank rule

Older source files and dated reports carrying historical `Gate1A` / `Gate1B` names remain in the repository for provenance and reproducibility of old runs. They are **legacy/noncontrolling**, not members of the living #287 dependency graph.

Source-neutral finite/algebraic lemmas inside such historical banks do not become #287 analytic inputs by being compilable. Conversely, no problem-specific status/source/compiler claim from those banks may be used by the living #287 programme unless it is reintroduced through an explicitly #287-owned module and independently audited.

Blocking CI enforces the active-scope boundary by building `RequestProject.CurrentErdos287`—which imports the full active `RequestProject.Main` spine—then scanning the two living entrypoint import lists for cross-project imports, scanning the new Sep-1 Lean layer for Twin-Prime-owned symbols, and rejecting forbidden proof shortcuts in the new modules.

A separate manually triggered legacy job can build every historical `RequestProject` module, including quarantined legacy banks. That is a reproducibility audit, not the definition of the living #287 theorem graph.

The living README, status and frontier documents are separately maintained as #287-only public-status views.

## Separate repository rule

The separate fixed-shift / Twin-Prime research programme is maintained in `RexHannes/twin-prime-proof-search` and is not an active dependency of the #287 compiler.

Cross-project references may appear in immutable Git history, legacy source banks, or archived reports as provenance. They are noncontrolling and must not be imported into the current #287 status or proof graph.

## Public-status rule

The repository must continue to state

```text
ERDOS287: OPEN
```

until the source-exhaustive analytic kernel and the final deterministic compiler to the original Erdős #287 statement are genuinely complete.
