import RequestProject.Erdos287.ResearchBankV6
import RequestProject.Erdos287.ResearchBankV7.Epochs
import RequestProject.Erdos287.ResearchBankV7.Absorption
import RequestProject.Erdos287.ResearchBankV7.PolylogCompletion
import RequestProject.Erdos287.ResearchBankV7.StableEntry
import RequestProject.Erdos287.ResearchBankV7.IntervalLifting
import RequestProject.Erdos287.ResearchBankV7.Spine
import RequestProject.Erdos287.ResearchBankV7.ErasureHit
import RequestProject.Erdos287.ResearchBankV7.GuardedBranchHit
import RequestProject.Erdos287.ResearchBankV7.FouvryPin
import RequestProject.Erdos287.ResearchBankV7.FiniteSourceKills
import RequestProject.Erdos287.ResearchBankV7.Numerics
import RequestProject.Erdos287.ResearchBankV7.V6Audit
import RequestProject.Erdos287.ResearchBankV7.Owners
import RequestProject.Erdos287.ResearchBankV7.Ledger
import RequestProject.Erdos287.ResearchBankV7.AxiomAudit

/-!
# Erdős #287 — Research Bank V7 (aggregator)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Strictly **append-only** layer.  `AnchoredV2`, `AnchoredV3`, `AnchoredV4`, `ResearchBankV5` and
`ResearchBankV6` are untouched: no file of those layers is edited, renamed, weakened, moved,
reinterpreted or replaced; V7 only *imports*, *re-exports* and *audits* them.  V6 is re-exported
as a frozen historical milestone with all of its evidence classifications preserved
(`Ledger.v6Frozen`, `Ledger.v6_classifications_preserved`).

## Contents

| module | content | verdict |
| --- | --- | --- |
| `Epochs.lean` | the four research epochs; meta-firewalls (superseded ≠ false; historical openness ≠ current owner; later reductions do not inhabit earlier owners; no status propagation along edges) | KERNEL-BANKED |
| `Absorption.lean` | exact finite charging: `(1−3γ)W ≤ 2z₀+g₀`; at `γ=1/8`, `W ≤ 16/5 z₀ + 8/5 g₀` and `U ≤ 2/5 z₀ + 1/5 g₀`; unguarded specializations; branching-bit budget | KERNEL-BANKED |
| `PolylogCompletion.lean` | finite second moment and disjoint buffer packing | KERNEL-BANKED |
| `PolylogCompletion.lean` | Croot input, PNT prime supply, LLL whole-row completion; the fixed-polylog complete-row law | external/uninhabited; CONDITIONAL-BANKED |
| `StableEntry.lean` | forward direction (ENTRY word ⟹ nonfailed terminal leaf) | KERNEL-BANKED |
| `StableEntry.lean` | the feasibility equivalence (reverse uses the external polylog interface) | CONDITIONAL-BANKED |
| `IntervalLifting.lean` | exact mixed-modulus interval lifting with actual Boolean subsets, non-coprime and repeated directions, and the recursion for successive lifts | KERNEL-BANKED |
| `Spine.lean` | arithmetic-spine extraction from a **supplied** certificate: interval inclusion, support and mass bookkeeping | KERNEL-BANKED |
| `ErasureHit.lean` | ERASURE-HIT: one-sided, arbitrary-fixed-part and complement forms; rational form | KERNEL-BANKED |
| `GuardedBranchHit.lean` | guarded branch-to-HIT: the actual deficit `w = J(S(x₀)−1)` is hit by the spine, giving `S = 1` on the same branch | KERNEL-BANKED (conditional on its hypothesis package) |
| `FouvryPin.lean` | Fouvry/Luca–Young, Selberg, Brun–Titchmarsh, prime counting | external/uninhabited |
| `FouvryPin.lean` | pin-capture inequality; sublinear-support consequence; branch-budget localization | CONDITIONAL-BANKED / KERNEL-BANKED arithmetic |
| `FiniteSourceKills.lean` | finite `p = 2q ± 1` source kills (59, 83, 107, 61, 73) | FINITE-SOURCE-KILL |
| `FiniteSourceKills.lean` | the pattern is not universal; uniform supply | COUNTERFIXTURE; OWNER-OPEN |
| `Numerics.lean` | `J = L₄₄₇` has **194 decimal digits and 644 bits** (corrected metadata) | KERNEL-BANKED |
| `V6Audit.lean` | semantic spot audit of the five load-bearing V6 theorems; re-exported unchanged | KERNEL-BANKED |
| `Owners.lean` | `UpperGapCarryCompression`, `ExactMassIntersection` | SUPERSEDED (never false) |
| `Owners.lean` | `EntryFirstTerminalLeafExistenceOrKill`; the node `GenuineEntryReferenceWord` | OWNER-OPEN |
| `Ledger.lean` | epoch-aware verdict ledger; no `CLOSED` row | bookkeeping |
| `AxiomAudit.lean` | `#print axioms` for every principal V7 theorem | audit |

## Current closure DAG (schematic)

```text
FULL-FROZEN / seed constraints
  → bounded absorption                       (Absorption, kernel)
  → STABLE-ENTRY terminal-leaf criterion     (StableEntry, forward kernel / reverse conditional)
  → genuine ENTRY reference word             (UNINHABITED — no theorem bypasses it)
  → guarded spine / ERASURE-HIT              (Spine, ErasureHit, GuardedBranchHit, kernel)
  → exact S = 1
```

## Status after V7

```text
V6:                                            frozen historical bank
bounded adaptive absorption:                   KERNEL-BANKED
fixed-polylog completion:                      CONDITIONAL (external Croot / PNT / LLL inputs)
STABLE-ENTRY:                                  reduction/equivalence, not existence
exact interval lifting:                        KERNEL-BANKED
arithmetic spine:                              KERNEL-BANKED (certificate theorem)
ERASURE-HIT:                                   KERNEL-BANKED
guarded branch-to-HIT:                         sufficient conditional theorem
Fouvry localization:                           CONDITIONAL, external dependencies explicit
finite source kills:                           finite diagnostics only
UpperGapCarryCompression, ExactMassIntersection: SUPERSEDED (not false)
genuine ENTRY seed / surviving terminal leaf:  OPEN
Erdős #287:                                    OPEN
```
-/
