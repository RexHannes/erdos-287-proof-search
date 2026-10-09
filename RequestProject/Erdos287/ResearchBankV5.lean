import RequestProject.Erdos287.ResearchBankV5.Routes
import RequestProject.Erdos287.ResearchBankV5.GateLedger
import RequestProject.Erdos287.ResearchBankV5.AsymptoticInputs
import RequestProject.Erdos287.ResearchBankV5.KilledRoutes
import RequestProject.Erdos287.ResearchBankV5.ContactCore.PathTransfer
import RequestProject.Erdos287.ResearchBankV5.ContactCore.StrictHeight
import RequestProject.Erdos287.ResearchBankV5.ContactCore.ProperPowerRow
import RequestProject.Erdos287.ResearchBankV5.ContactCore.PadicSaturation
import RequestProject.Erdos287.ResearchBankV5.ContactCore.ExternalInterfaces
import RequestProject.Erdos287.ResearchBankV5.Regressions
import RequestProject.Erdos287.ResearchBankV5.RouteReconciliation
import RequestProject.Erdos287.ResearchBankV5.AxiomAudit

/-!
# Erdős #287 — route-aware master research bank V5 (aggregator)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Strictly **append-only** layer.  Anchored V2, Anchored V3 and Anchored V4 are untouched: no file
of those layers is edited, renamed, weakened, moved or replaced; this layer only *imports* and
*re-exports* them.

## Route firewall

Two research routes coexist and neither supersedes the other:

* `ResearchRoute.anchoredV4` — the Anchored V2/V3/V4 formal route;
* `ResearchRoute.contactCoreV5` — the CONTACT / strict-height / `p`-adic / exceptional-leaf route.

They may share lemmas and may eventually meet, but they currently have **different open-owner
sets** and **different closure DAGs**.  A status statement about one never changes the status of
the other (`Routes.lean`, `GateLedger.lean`), and a route closure reaches the original problem
only through that route's own proved bridge (`RouteReconciliation.lean`).

## New kernel bank (this layer)

* exact path transfer `D_j p_j = C_j p₀ - R_j`, the unrolled remainder and its normalized form,
  with the `53 — 317 — 79` depth-two counterfixture retiring the direct terminal splice
  (`ContactCore/PathTransfer.lean`);
* the complete proper-power row condition (PP-ROW) and the proof that it is strictly stronger than
  the naive unit-inverse congruence; exact interval counting for valuation layers
  (`D_v ≤ 2 n_v + 5`, the `6ℓ` sparse tail and the `4ℓ` raw forced-zero port cap); the exact
  valuation lift `q d = h d₀`, `⌊⌊M/q⌋/ℓ^v⌋ = ⌊M/h⌋` (`ContactCore/ProperPowerRow.lean`);
* the layer-local digit step of `p`-adic saturation: subset sums of any `ℓ-1` nonzero residues
  cover `𝔽_ℓ`, with the heavy/sparse obstruction dichotomy
  (`ContactCore/PadicSaturation.lean`);
* the STRICT-HEIGHT contact theorem, its height form, the impossibility of same-height first-power
  cycles and the mandatory no-monotone-descent firewall, with exhaustive finite regressions
  (`ContactCore/StrictHeight.lean`);
* the contact-core Gate D bridge back to the original reciprocal-gap formulation
  (`RouteReconciliation.lean`).

## External / conditional bank

`ContactCore/ExternalInterfaces.lean` names the Croot general-modulus input, its prime-power
corollary, (VAL-TRANS), (FP-INTERFACE-GEN) and (FP-INTERFACE) as **uninhabited `Prop`s**, and
kernel-proves only their logical consequences: full-cube removability/elimination and
(LINEAR-CHARGE).  `AsymptoticInputs.lean` is the visible ledger of this external mathematics.

## Status

```text
Erdős #287: OPEN
Anchored V2/V3: FROZEN      Anchored V4: BANKED / OPEN ROUTE
Gate A: local CLOSED, global OPEN
Gate B: OPEN (generic long families paid)
Gate C: OPEN (reduced excess core)
Gate D: CLOSED
Contact-core current owner: STRICT_HEIGHT_EXCEPTIONAL_LEAF_CAPACITY
```
-/
