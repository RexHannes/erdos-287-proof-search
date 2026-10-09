# Erdős #287 — Research Bank V6 report (append-only layer)

**Erdős #287 is OPEN. No closure is claimed.**

## 1. Scope and discipline

Strictly append-only. Nothing in `AnchoredV2*`, `AnchoredV3*`, `AnchoredV4*` or `ResearchBankV5*`
was edited, renamed, moved, weakened or replaced; the whole delivery is the new layer
`RequestProject/Erdos287/ResearchBankV6/` with aggregator
`RequestProject/Erdos287/ResearchBankV6.lean`. The V5 `ResearchStatus × EvidenceKind` discipline is
imported and reused, not redefined.

## 2. Exact files added

| file | content |
| --- | --- |
| `RequestProject/Erdos287/ResearchBankV6.lean` | aggregator + status table |
| `RequestProject/Erdos287/ResearchBankV6/FullFrozen.lean` | FULL-FROZEN prime-power precision as denominator-entry mechanism |
| `RequestProject/Erdos287/ResearchBankV6/ContactTarget.lean` | finite per-middle-row contact target; balancing identity; external asymptotic adapter (uninhabited) |
| `RequestProject/Erdos287/ResearchBankV6/MiddleBand.lean` | middle-band same-trace completion, conditional on the uninhabited fixed-cardinality additive interface |
| `RequestProject/Erdos287/ResearchBankV6/UpperGapCarry.lean` | upper-gap cofactor–carry kernel and height aggregation; cofactor-range counterfixture |
| `RequestProject/Erdos287/ResearchBankV6/SupportDisjointness.lean` | upper-gap support disjointness + independence firewall |
| `RequestProject/Erdos287/ResearchBankV6/UpperGapContact.lean` | contact relation `abs(pj − qℓ) = 1`, exact finite lemmas |
| `RequestProject/Erdos287/ResearchBankV6/OpenOwners.lean` | `UpperGapCarryCompression` candidates, `ExactMassIntersection`, denominator firewall |
| `RequestProject/Erdos287/ResearchBankV6/Ledger.lean` | verdict ledger, three-route bookkeeping, closure DAG (proved edges only) |
| `RequestProject/Erdos287/ResearchBankV6/AxiomAudit.lean` | `#print axioms` for every principal V6 theorem |

No existing file was modified.

## 3. Acceptance verdicts

### KERNEL-BANKED (new exact sorry-free theorems)

*Upper-gap carry (`UpperGapCarry.lean`)*

- `rowMass_eq_div` — `∑_j ε_{pj}/(p j) = T_p / (p L_N)` with `T_p = ∑_j ε_{pj} L_N / j`,
  `L_N = lcm(1,…,N)`, over the **actual** cofactor set.
- `den_dvd_iff` — a rational's reduced denominator divides `L` iff it is an integer multiple of `1/L`.
- `prime_removed_iff_dvd_rowNumerator` — denominator entry of the prime `p` ⇔ `p ∣ T_p`.
- `rowMass_eq_carry_div` — with `k_p = T_p/p`: `∑_j ε_{pj}/(p j) = k_p / L_N`.
- `carry_height_aggregation` — `∑_{p} ∑_j ε_{pj}/(p j) = ∑_N K_N / L_N`, `K_N = ∑_{⌊M/p⌋ = N} k_p`.
- supporting: `lcmUpto_pos`, `dvd_lcmUpto`, `allowedCofactors_window`, `allowedCofactors_dvd_lcm`.

*Support disjointness (`SupportDisjointness.lean`)*

- `no_shared_denominator`, `rowSupport_disjoint`, `rowSupport_disjoint_of_sqrt_lt`,
  `rowSupports_pairwiseDisjoint`, plus the firewall
  `shared_support_does_not_give_independence` (disjoint support ⇏ independent row choices).

*Contact relation (`UpperGapContact.lean`)*

- `contact_coprime`, `rowContact_prime_ne`, `contactFibre_card_le` (≤ 2 per position),
  `contact_bound_sharp` (the bound is attained), `traceContacts_card_le`,
  `contact_partner_unique` / `rowContact_partner_unique` (unique partner cofactor for primes ≥ 3),
  `contact_count_not_globally_sparse` (no stronger sparsity is asserted).

*Contact target (`ContactTarget.lean`)*

- `card_le_of_charge` — generic charging inequality.
- `squareMultiples_card` — exactly `⌊M/z²⌋` multiples of `z²` in `[1,M]`.
- `contact_target_bound` / `contact_target_bound_real` — `H ≤ 2 π(z) + 4 ⌊M/z²⌋`.
- `balanced_scale`, `contact_target_at_balanced_scale` — the exact identity `M/z² = z/l` at `z³ = M l`.

*FULL-FROZEN (`FullFrozen.lean`)*

- `row_disjoint_of_window_exclusion`, `row_card_zero_of_window_exclusion` — under the banked
  prime-power window exclusion, the counterexample denominator set is disjoint from the whole
  physical `p^e`-row.

*Firewalls (`OpenOwners.lean`, `Ledger.lean`)*

- `den_dvd_does_not_close`, `den_dvd_not_sufficient` — `den(S) ∣ J` is **not** closure of #287.
- `aggregateMass_eq_active`, `sum_in_lattice`.
- `no_closed_verdict`, `erdos287_ownerOpen`, `erdos287_not_closed_in_v6`,
  `kernelBanked_iff_kernelProof`, `nonKernel_rows_not_proved`, `routes_not_claimed_equivalent`,
  `ownerOpen_row_is_not_a_proof`, `ledger_is_not_a_proof`, `ofV5_injective`,
  `routes_pairwise_distinct`.

### CONDITIONAL-BANKED (implications from explicitly uninhabited interfaces)

- `MiddleBand.restrictedSumset_covers`, `MiddleBand.middleRows_completable`,
  `MiddleBand.middleBand_sameTrace_conditional` — all consume the uninhabited
  `MiddleBand.RestrictedSumsetInput` (a Dias da Silva–Hamidoune type fixed-cardinality additive
  theorem, not proved here and not taken from Mathlib). Not labelled `kernelProof`.
- `ContactTarget.contact_cubeRoot_conditional` — consumes the uninhabited
  `ContactAsymptoticAdapter` and `PrimeCountingAsymptotic`.
- `OpenOwners.mass_single_term_of_support_one`, `OpenOwners.mass_den_dvd_of_granularity`,
  `OpenOwners.no_unit_mass_of_exactMassIntersection` — consume the uninhabited owners.
- The kernel trace bookkeeping `completion_preserves_trace` / `completion_agrees_on_middle` is
  unconditional.

### COUNTERFIXTURE

- `rowNumerator_range_substitution_counterfixture`, `rowMass_range_substitution_counterfixture` —
  replacing the actual (selected/truncated) cofactor range by `1,…,N` changes both the exact row
  numerator and the exact row mass (`N = 2`, `p = 5`, `J = {1}` versus `{1,2}`).

### OWNER-OPEN (uninhabited)

- `OpenOwners.UpperGapCarryCompressionSupport c` (support compression),
  `…Window w` (height-window compression), `…Size c` (size compression),
  `…Granularity D` (lattice/granularity compression) — four clearly labelled candidate
  interfaces, since the mathematics does not yet single out the strongest useful form.
- `OpenOwners.ExactMassIntersection` — the exact `S = 1` step.
- `ContactTarget.PrimeCountingAsymptotic`, `ContactTarget.ContactAsymptoticAdapter`,
  `ContactTarget.ContactCubeRootTarget` — the cube-root asymptotic consequence.
- `MiddleBand.RestrictedSumsetInput`.

### CLOSED

None. `no_closed_verdict` machine-checks that the V6 ledger contains no `closed` row, and
`erdos287_not_closed_in_v6` that #287 in particular is not marked closed.

## 4. Build and placeholder audit

- Build: `lake build RequestProject.Erdos287.ResearchBankV6` succeeds (whole layer, including the
  aggregator and the axiom-audit module).
- No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `opaque` or `@[implemented_by]` occurs
  anywhere in the V6 layer.
- `#print axioms` for all 45 audited principal theorems reports only
  `[propext, Classical.choice, Quot.sound]`, `[propext, Quot.sound]` or `[propext]`.
- Finite diagnostics (`decide` fixtures: `contact_bound_sharp`, the ledger checks) are kernel
  reducible and kept separate from the general mathematical theorems.

## 5. End state

```text
Erdős #287:                                   OPEN
FULL-FROZEN / contact-core finite kernel:     BANKED as far as actually proved
middle same-trace completion:                 CONDITIONAL (uninhabited additive interface)
upper-gap carry identity:                     KERNEL-PROVED
same-height carry aggregation:                KERNEL-PROVED
upper-gap support disjointness:               KERNEL-PROVED
upper-gap carry compression:                  OPEN (4 candidate interfaces)
exact S = 1 mass intersection:                OPEN
```
