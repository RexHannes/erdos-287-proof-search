import RequestProject.Erdos287.ResearchBankV5
import RequestProject.Erdos287.ResearchBankV6.UpperGapCarry
import RequestProject.Erdos287.ResearchBankV6.SupportDisjointness
import RequestProject.Erdos287.ResearchBankV6.UpperGapContact
import RequestProject.Erdos287.ResearchBankV6.ContactTarget
import RequestProject.Erdos287.ResearchBankV6.MiddleBand
import RequestProject.Erdos287.ResearchBankV6.OpenOwners
import RequestProject.Erdos287.ResearchBankV6.FullFrozen
import RequestProject.Erdos287.ResearchBankV6.Ledger
import RequestProject.Erdos287.ResearchBankV6.AxiomAudit

/-!
# Erdős #287 — Research Bank V6 (aggregator)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Strictly **append-only** layer.  Anchored V2, V3, V4 and Research Bank V5 are untouched: no file
of those layers is edited, renamed, weakened, moved or replaced; this layer only *imports* and
*re-exports* them.  V6 does **not** claim closure: its purpose is to synchronize the formal bank
with the current mathematical frontier and to prove every elementary/exact part of the new
upper-gap carry reduction, while keeping every genuinely unproved analytic/combinatorial
interface explicitly uninhabited.

## Contents

| module | content | verdict |
| --- | --- | --- |
| `FullFrozen.lean` | FULL-FROZEN prime-power precision as the small-prime denominator-entry mechanism: the counterexample denominator set is disjoint from the excluded physical row | KERNEL-BANKED |
| `ContactTarget.lean` | the finite per-middle-row contact target `H_p(𝒞) ≤ 2π(z) + 4⌊M/z²⌋` (charging inequality) and the exact balancing identity `M/z² = z/l` at `z³ = M l` | KERNEL-BANKED |
| `ContactTarget.lean` | `π(z) ≪ z/log z` and `H_p(𝒞) ≪ M^{1/3}(log M)^{-2/3}` | OWNER-OPEN (external adapter, uninhabited) |
| `MiddleBand.lean` | middle-band same-trace completion from the fixed-cardinality additive interface | CONDITIONAL-BANKED |
| `UpperGapCarry.lean` | `∑_j ε_{pj}/(pj) = T_p/(p L_N)`; denominator entry ⇔ `p ∣ T_p`; carry identity `= k_p/L_N`; same-height aggregation `∑_N K_N/L_N` | KERNEL-BANKED |
| `UpperGapCarry.lean` | replacing the actual cofactor range by `1,…,N` | COUNTERFIXTURE |
| `SupportDisjointness.lean` | `pq > M` ⇒ no shared physical denominator position; pairwise disjointness above `√M` | KERNEL-BANKED |
| `UpperGapContact.lean` | the contact relation `|pj − qℓ| = 1`: symmetry, coprimality, `≤ 2` contacts per position (sharp), partner uniqueness for primes `≥ 3` | KERNEL-BANKED |
| `OpenOwners.lean` | `UpperGapCarryCompression` (four labelled candidate interfaces) | OWNER-OPEN |
| `OpenOwners.lean` | `ExactMassIntersection` and the firewall `den(S) ∣ J` is not closure | OWNER-OPEN + KERNEL-BANKED firewall |
| `Ledger.lean` | verdict ledger, three-route bookkeeping, closure DAG with proved edges only | bookkeeping |
| `AxiomAudit.lean` | `#print axioms` for every principal V6 theorem | audit |

## Status after V6

```text
Erdős #287:                                   OPEN
FULL-FROZEN / contact-core finite kernel:     BANKED as far as proved
middle same-trace completion:                 CONDITIONAL (uninhabited additive interface)
upper-gap carry identity:                     KERNEL-PROVED
same-height carry aggregation:                KERNEL-PROVED
upper-gap support disjointness:               KERNEL-PROVED
upper-gap carry compression:                  OPEN
exact S = 1 mass intersection:                OPEN
```
-/
