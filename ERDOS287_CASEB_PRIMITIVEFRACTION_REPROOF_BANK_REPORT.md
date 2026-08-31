# ERDŐS 287 — CASE-B PRIMITIVE-FRACTION REPROOF BANK (Δ)

Append-only delta over the CASE-B one-level primitive-fraction package.
Nothing previously banked was edited; the only change to a pre-existing file is three new
`import` lines in `RequestProject/Main.lean`.

## Build status

```
LEAN KERNEL BUILD:            PASS   (lake build RequestProject, full default target)
NEW sorry:                    NONE
NEW axiom:                    NONE
unsafe / native_decide:       NONE
kernel dependencies (new):    propext, Classical.choice, Quot.sound   (several rows: none)
```

## Files added

Exact mathematics:
* `RequestProject/CurrentProgramme/CaseBPrimitiveFractionReproof.lean`

Status / audit:
* `RequestProject/Status/CurrentStatusErdos287CaseBFrontier.lean`
* `RequestProject/Status/AxiomAuditErdos287CaseBReproof.lean`

## What was re-verified (already banked, re-checked by a full kernel build)

| Row | Statement | Status |
|---|---|---|
| `DET1-ONELEVEL-PRIMITIVEFRACTION-SPACING45` | separation ≥ 1/(d m₁m₂) ≥ d/(4G²), G = dM | PASS, unconditional |
| FIXED-`d` ALGEBRA | `(A + 4G²/d)(dK) = (Ad + 4G²)K` | PASS, exact |
| `DET1-ONELEVEL-COEFFENERGY45` | `∑_{M≤m<2M} E_{dm}/m² ≤ dB(1+B/G)L^{C_E}` | PASS, conditional on the `E_g` input |
| `DET1-ONELEVEL-PROJECTOR-S1S2-45` | `S1 ≤ c₁(1+log⌊X/H⌋)`, `S2 ≤ 2c₁/H` | PASS, conditional on the Ω_H pin |
| `DET1-ONELEVEL-dRESTRICTED-LS45` | geometric factor `A + 4G²/d` | PASS, conditional on `hLS` |
| `DET1-ONELEVEL-PRIMITIVEFRACTION-GLOBAL45` | global `Q_H` bound and envelope | PASS, conditional |
| normalised ratio | `L₁/B + L₁/G + L₀G²/(HX) + L₀G/(HA)` at `X = AB` | PASS, exact identity |
| Ω_H normalisation, `B`-margin, `G`-margin | — | SOURCE PIN, unchanged |

## What is new in this delta

| Theorem | Content |
|---|---|
| `Erdos287.CaseBReproof.separation_of_distinct_pairs` | spacing in the form used by a large sieve: the hypothesis is that the two pairs `(m,t)` are **distinct**, and injectivity of the standard representatives (needing only `(t,m)=1`) supplies the nonzero numerator. Unconditional. |
| `Erdos287.CaseBReproof.caseB_pipeline_QH_bound` | end-to-end composition energy → fixed `d` → `S1`/`S2` → global `Q_H`, with the coefficient-energy bound inserted verbatim instead of the abstract hypothesis `hGd`. The extra hypothesis `G ≤ M` is explicit. |
| `Erdos287.CaseBReproof.normalised_ratio_le_of_comparable` | the `AB ≍ X` source firewall: with `c₀X ≤ AB`, the four-term decomposition survives, the comparability constant appearing on the `G²/(HX)` term only. |
| `Erdos287.CaseBReproof.rpow_max_eq` | `max(X^a, X^b) = X^{max(a,b)}` for `X > 1`. |
| `Erdos287.CaseBReproof.kappa_le_of_critical_range` | exponential critical range, **exact**: `X^κ ≤ L^K max(X^{2θ-1}, X^{θ-α})` ⟹ `κ ≤ max(2θ-1, θ-α) + K loglog X / log X`. |
| `Erdos287.CaseBReproof.loglog_div_log_tendsto_zero` | `loglog X / log X → 0`. |
| `Erdos287.CaseBReproof.kappa_le_eventually`, `kappa_le_max_zero` | the `o(1)` form: `κ ≤ max(0, 2θ-1, θ-α) + ε` eventually. |
| `Erdos287.CaseBReproof.projector_S1_at_two_G` | `S1 ≤ c₁(1 + log(2G/H))`, the audited `X = 2G` truncation. |

Frontier firewall (`CurrentStatusErdos287CaseBFrontier`): `frontierLedger`, `stage`,
`frontier_no_closed_rows`, `frontier_unique`,
`primitiveFractionCritical_strictly_before_frontier`, `primitiveFractionCritical_not_frontier`,
`chain_is_strictly_increasing`, `frontier_erdos287_open`, `caseB_ledger_preserved`.
These are bookkeeping statements about the ledger only: `passedThrough` records that a strictly
later reduction exists, **not** that a node is closed, and no mathematical content about the
descendant nodes (squarefree projector unfold, `k`–`m` fusion, coprime-pair projector, diagonal
annihilation, fixed-`Δ` rigidity, affine phase exposure, affine-defect normal form) is asserted.

## Promotion ledger after this delta

```
DET1-ONELEVEL-PRIMITIVEFRACTION-SPACING45   PASS — kernel checked, unconditional
  (now also in pair form)
DET1-ONELEVEL-dRESTRICTED-LS45              PASS — conditional reduction (hLS)
DET1-ONELEVEL-COEFFENERGY45                 PASS — conditional reduction (E_g)
DET1-ONELEVEL-PROJECTOR-S1S2-45             PASS — conditional reduction (Ω_H pin)
DET1-ONELEVEL-PRIMITIVEFRACTION-GLOBAL45    PASS — conditional theorem
CASE-B PIPELINE (new)                       PASS — conditional theorem (hLS, E_g, Ω_H)
AB ≍ X FIREWALL (new)                       PASS — exact
CASE-B CRITICAL EXPONENT (new)              PASS — exact, plus o(1) form
OMEGA_H NORMALISATION                       SOURCE PIN
B POLYNOMIAL MARGIN                         SOURCE PIN
G POLYNOMIAL MARGIN                         SOURCE PIN
SMALL-B, SMALL-G                            OPEN / SOURCE PIN
ERDOS287                                    OPEN
```

Nothing here closes Erdős #287, and no source pin was promoted.
