# Input inventory for the 3 November 2026 overnight task

Repository baseline: `66a31feb4f8d89edffa96d5377ab1ad9e6603aab`. Lean: `leanprover/lean4:v4.28.0`; Mathlib: `v4.28.0`, with the existing `lake-manifest.json` unchanged.

The exact task brief is in `REQUEST.md`, extracted verbatim from the user attachment. SHA-256 of the entire original attachment: `802afa5c32d4e7594078c1b53d732a42b09bffe0426f7bfaa6e7bf9eede83e53`.

## Available actual bank

- `RequestProject/TrustedBank/Erdos287/CarryTower.lean`
- `RequestProject/TrustedBank/Erdos287/TopLayerConsequences.lean`
- `RequestProject/TrustedBank/Erdos287/BoundedCofactor.lean`
- `RequestProject/Erdos287/Direct.lean`
- `RequestProject/Erdos287/OddHalfDivisor.lean`
- Other `RequestProject/Erdos287/` sources and their status/audit modules. Inspect actual imports and hypotheses before reusing a result.

## Not located in this repository/export

- The complete Gold God 4.1 Positional-Arithmetic Incompatibility manuscript.
- `erdos287_low_height_20261031.lean`
- `erdos287_positional_windows_20261101.lean`
- `erdos287_effectivity_20261101.lean`
- The suggested legacy paths ending in `ConsecutiveReciprocals.lean`, `PrimeAdic.lean`, and `SupplyReduction.lean`.

Do not claim these missing files were restored or compiled. Do not fabricate their declarations. The four-value residue theorem's exact size, primality and localization hypotheses are not fully specified by the brief; record that input gap. The reported Lean 4.19 files are not silently part of this Lean 4.28 build.

Start with the literal finite reciprocal source and rigorously stated upper-half prime exclusion / internal-neighbor forcing. State every endpoint condition. Reuse any actual equivalent bank lemma after comparing its complete type. Continue exact carry/residue algebra only when the required hypotheses can be reconstructed from supplied source; otherwise record the precise unresolved specification. Never turn missing conditions into an unnamed provider or assume the desired residue conclusion.
