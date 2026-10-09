# ERDŐS #287 — ROUTE-AWARE MASTER RESEARCH BANK V5

**INTERNAL RESEARCH PROGRAMME REPORT.  Erdős #287 is `OPEN`.  Nothing in this run claims a
solution, and no open owner is inhabited.**

This run is a **banking / reconciliation** run, strictly **append-only**.

---

## 1.  Project / file inventory (new layer only)

New aggregator:

```text
RequestProject/Erdos287/ResearchBankV5.lean
```

New modules:

```text
RequestProject/Erdos287/ResearchBankV5/Routes.lean                        (175 lines)
RequestProject/Erdos287/ResearchBankV5/GateLedger.lean                    (336 lines)
RequestProject/Erdos287/ResearchBankV5/AsymptoticInputs.lean              (113 lines)
RequestProject/Erdos287/ResearchBankV5/KilledRoutes.lean                  ( 69 lines)
RequestProject/Erdos287/ResearchBankV5/Regressions.lean                   (134 lines)
RequestProject/Erdos287/ResearchBankV5/RouteReconciliation.lean           (144 lines)
RequestProject/Erdos287/ResearchBankV5/AxiomAudit.lean                    (126 lines)
RequestProject/Erdos287/ResearchBankV5/ContactCore/PathTransfer.lean      (174 lines)
RequestProject/Erdos287/ResearchBankV5/ContactCore/StrictHeight.lean      (159 lines)
RequestProject/Erdos287/ResearchBankV5/ContactCore/ProperPowerRow.lean    (262 lines)
RequestProject/Erdos287/ResearchBankV5/ContactCore/PadicSaturation.lean   (178 lines)
RequestProject/Erdos287/ResearchBankV5/ContactCore/ExternalInterfaces.lean(170 lines)
```

New documents:

```text
ERDOS287_RESEARCH_BANK_V5_REPORT.md            (this file)
ERDOS287_RESEARCH_BANK_V5_NEXT_STATE.md
```

The library glob of the project (`RequestProject.+`) already covers the new modules, so no edit to
any older aggregator was required; the new aggregator imports the new modules and the frozen
Anchored V4 layer.

---

## 2.  Untouched frozen layers

```text
RequestProject/Erdos287/AnchoredV2/     untouched
RequestProject/Erdos287/AnchoredV2.lean untouched
RequestProject/Erdos287/AnchoredV3/     untouched
RequestProject/Erdos287/AnchoredV3.lean untouched
RequestProject/Erdos287/AnchoredV4/     untouched
RequestProject/Erdos287/AnchoredV4.lean untouched
```

No file outside `ResearchBankV5/` (and the two new Markdown documents) was created, edited,
renamed, moved or deleted in this run.  The V5 layer only *imports* and *re-exports* the earlier
layers.

---

## 3.  Anchored V4 snapshot (frozen, re-exported)

```text
ANCHORED V2: FROZEN
ANCHORED V3: FROZEN
ANCHORED V4: BUILT / BANKED
AnchoredV4 bridge to original Erdős #287: PROVED
AnchoredV4 route: OPEN
```

Open owners, unchanged and uninhabited:

```text
ENTRY_EXISTENCE
SAFE_DESCENT_SUPPLY
GUARDED_ABSORBER_ANALYTIC_SUPPLY
```

Exact V4 mathematics re-exported without modification (see `GateLedger.anchoredLedger` and
`Regressions.lean`):

* normalized prime-power height and `n ∣ 2·lcm(1,…,t) ↔ normHeight n ≤ t`, with the load-bearing
  factor-two regression `32 ∣ 2·L(16)`, `32 ∤ L(16)`
  (`Erdos287.AnchoredV4.two_factor_essential`, re-exported as
  `Regressions.regression_factor_two`).  `den(2Δ)` is never replaced by `den(Δ)`;
* the doubled denominator lattice `den(2q) ∣ P ↔ den(q) ∣ 2P` with the finite regression
  `1/1056 + 1/1080 = 89/47520`, `den(2Δ) ∣ L(30)`, `den(Δ) ∤ L(30)`
  (`Regressions.regression_doubled_lattice`);
* the exact no-`00` guard geometry (all-even omissions guarded, restoration never creates
  adjacency, fresh even centres preserve the guard, exact word-value bookkeeping);
* the exact `Entry` datum and its proved necessary conditions (omitted positions exceed `Q`, the
  guarded cardinality bound).  **ENTRY existence is not inhabited**;
* well-founded prime-power descent to any floor height, preserving interval, guard, mask,
  freshness and the doubled-denominator condition;
* the absorber reductions: exact absorption → integer subset-sum, no-wraparound congruence → exact
  equality, the exact finite Fourier counting identity, conditional exact absorption from Fourier
  dominance (dominance remains a hypothesis);
* the finite global transition system: exact congruence formulation, component splitting, the
  dual/divisor unsolvability certificate, `descentStep_of_congruence`;
* the V4 route firewalls: general global column surjectivity is false, Route B has only its exact
  coset/subgroup criterion, positive mass is not coverage, many targets do not imply a hit;
* exact compatibility with the frozen V3 bank (no V3 route previously killed is revived);
* the V4 bridge (final V4 configuration ⟹ original #287 counterexample) and its contrapositive,
  re-exported as `Reconciliation.anchoredV4_bridge` and
  `Reconciliation.anchoredV4_bridge_contrapositive`.

---

## 4.  Contact-core exact kernel bank (new, this run)

### 4.1  Exact path transfer (PATH)

`ContactCore/PathTransfer.lean`, over any commutative ring:

* `path_transfer` : from `pᵢcᵢ - p_{i+1}dᵢ = σᵢ` for all `i < j`, and
  `C₀ = D₀ = 1`, `R₀ = 0`, `C_{i+1} = cᵢCᵢ`, `D_{i+1} = dᵢDᵢ`, `R_{i+1} = cᵢRᵢ + σᵢDᵢ`:

  ```text
  D_j p_j = C_j p₀ - R_j
  ```

* `Rseq_eq_sum` : `R_j = ∑_{i<j} σᵢ Dᵢ ∏_{r ∈ [i+1, j)} c_r`;
* `Rseq_div_Cseq` : `R_j / C_j = ∑_{i<j} σᵢ Dᵢ / (Cᵢ cᵢ)` (over a field, all `cᵢ ≠ 0`);
* `Cseq_eq_prod`, `Dseq_eq_prod`.

### 4.2  Depth-one only: the `53 — 317 — 79` counterfixture

`direct_splice_not_unit`, `depthTwo_splice_counterfixture`, `fixture_accumulators`,
`fixture_path_transfer`, `depthOne_only`:

```text
6·53 - 317 = 1,   317 - 4·79 = 1,   but   6·53 - 4·79 = 2.
```

PATH reproduces the fixture exactly (`C₂ = 6`, `D₂ = 4`, `R₂ = 2`, `4·79 = 6·53 - 2`).

```text
positive-density root pins ⇒ positive-density direct root-to-terminal contacts:
    RETIRED as a global statement
direct incidence:  DEPTH-ONE ONLY
```

### 4.3  Complete proper-power row (PP-ROW)

`ContactCore/ProperPowerRow.lean`:

* `PPRow ℓ A N ε` : `∑_{c ∈ C} ε_c (J/c) ≡ 0 (mod ℓ^{t+1})` with `C = [A,N]`, `J = lcm C`,
  `t = v_ℓ(J)`;
* `ppRow_ne_naive` : the naive unit-inverse congruence modulo `ℓ` is **strictly weaker** — with
  `ℓ = 2`, `C = [1,2]`, `J = 2`, `t = 1`, the selection `ε₁ = 1, ε₂ = 0` satisfies the naive
  condition and violates PP-ROW.

### 4.4  Exact valuation-layer counting

* `mulCount_le`, `mulCount_ge` : two-sided interval counts of multiples;
* `layer_split` : `D_{v+1} + n_v = D_v`;
* `layerCount_le` : `D_v ≤ 2 n_v + 5` (master bound, base `ℓ ≥ 2`);
* `sparse_layer_bound` : `n_v < 2ℓ ⟹ D_v ≤ 6ℓ`  (sparse `p`-adic tail);
* `deficient_layer_bound` : `n_v ≤ ℓ - 1 ⟹ D_v ≤ 4ℓ`;
* `heavy_layer_majority` : `n_v ≥ 2ℓ` and `|P ∩ C_v| ≥ n_v - (ℓ-2)` imply `|P ∩ C_v| > n_v/2`;
* `rawPort_cap` (RAW-PP) : all cofactors of valuation at least the first deficient level `v✱` lie
  in `D_{v✱}`, hence **at most `4ℓ` raw forced-zero ports per base-`ℓ` proper-power row**;
* `no_deficient_layer_no_port` : if no layer is deficient, every layer carries `≥ ℓ` cofactors of
  exact valuation, so no raw forced-zero port is produced.

Recorded dichotomy:

```text
PP obstruction = charged heavy layer  ⊍  O(ℓ) sparse tail
```

### 4.5  Valuation lift

* `valuationLift_mul` : `ℓ^{e₀}·(ℓ^v d₀) = ℓ^{e₀+v}·d₀`, i.e. `q d = h d₀` with `h = ℓ^{e₀+v}`;
* `valuationLift_floor` : `⌊⌊M/q⌋ / ℓ^v⌋ = ⌊M/h⌋`;
* `valuationLift_unit_cofactor` : `d₀` is prime to `ℓ` and bounded by the lifted height.

### 4.6  `p`-adic layer saturation (local step)

`ContactCore/PadicSaturation.lean`:

* `subsetSums_card_ge` : the subset sums of `k` nonzero residues have size `≥ min(ℓ, k+1)`;
* `subsetSums_eq_univ` : **subset sums of any `ℓ-1` nonzero residues cover `𝔽_ℓ`** (proved
  directly; Cauchy–Davenport is not needed);
* `padicLayer_hits_target` : the digit step actually consumed at a valuation layer;
* `heavy_obstruction_charged`, `sparse_obstruction_small` : the two branches of the PP obstruction
  dichotomy.

The **global** (PADIC-SAT) statement — `|C_v \ P| ≥ ℓ-1` at every layer implies `P` extends to a
complete legal row state — is recorded as the uninhabited `Prop` `PadicSaturationStatement`
(`status = open`, `evidence = researchConjecture`).  Only its layer-local digit step is
kernel-proved.

### 4.7  STRICT-HEIGHT

`ContactCore/StrictHeight.lean`:

* `strictHeight_no_unit_contact` : for distinct odd owners `p < q` with
  `⌊M/p⌋ = ⌊M/q⌋ = N`, no `1 ≤ c, d ≤ N` satisfy `|pc - qd| = 1`;
* `strictHeight_no_unit_contact_symm` : unordered form;
* `strictHeight_floor_lt` : `p < q` in unit contact ⟹ `⌊M/q⌋ < ⌊M/p⌋`;
* `strictHeight_high_owners` : the specialization carrying the (unused) hypotheses
  `p, q > √M` — the proof does not need them, and the general theorem is stated without them;
* `sameHeight_cycle_impossible` : no same-height first-power cycle;
* regressions `strictHeight_regression_fixture`, `strictHeight_regression_sweep300`,
  `strictHeight_regression_sweep1000`.

### 4.8  Contact-core Gate D bridge

`RouteReconciliation.lean`:

* `contactCore_gateD_bridge` / `ContactFinalConfig.toCounterexample` : a final contact-core
  configuration (Boolean selection word on `[N,M]`, isolated holes, endpoints selected,
  reciprocal value exactly `1`) is an Erdős #287 counterexample;
* `contactCore_gateD_bridge_contrapositive`.

This is **not** the Anchored V4 bridge; both bridges coexist and neither implies the other
(`routes_not_claimed_equivalent`).

---

## 5.  External asymptotic bank (uninhabited)

`ContactCore/ExternalInterfaces.lean` + `AsymptoticInputs.lean`:

| input | Lean `Prop` | evidence |
|---|---|---|
| Croot general-modulus reciprocal coverage | `CrootGeneralModulus` | `externalAnalyticBank` |
| Croot prime-power corollary | `CrootPrimePowerModulus` | `externalAnalyticBank` |
| Croot/PNT multiscale incidence | (consumed by FP-INTERFACE-GEN) | `externalAnalyticBank` |
| FP-INTERFACE-GEN | `FPInterfaceGen κ` | `externalAnalyticBank` |
| FP-INTERFACE | `FPInterface κ` | `externalAnalyticBank` |
| positive-density multiscale burden | (Gate C input) | `researchConjecture` |

Kernel-proved **conditional** consequences (premises visible, never discharged):

* `valTrans_of_raw_terminal` (VAL-TRANS): under the one-demand interface, a raw terminal satisfies
  `U_ℓ(d) < C_η ((v+1) log ℓ)^{3+η}`;
* `fullCube_no_restriction`, `fullCube_elimination`: a full-cube projection makes the row exactly
  eliminable, so a clean Croot-long first-power row can be neither anchor, nor switch, nor
  forcing-message carrier, nor a nontrivial higher-order constraint;
* `linear_charge` (LINEAR-CHARGE): `κ ∑_{p ∈ K_long} N_p ≤ 2|E(K)| + F_K`;
* `linear_charge_supersedes_log_form`: the exact comparison recording that the older schematic
  `∑ N_p / log N_p ≲ |E| + F` is superseded by one logarithmic factor.

`externalInputs_not_formalized`, `externalInputs_not_kernelProof`, `externalInputs_not_refereed`
are machine-checked facts about this ledger.

---

## 6.  Killed routes (exact fixtures retained)

`KilledRoutes.lean`:

* `primorial_local_factor_cancellation` : `(1 - 1/λ)·λ/(λ-1) = 1`.

  ```text
  PRIMORIAL-SCALE PRE-SIEVING TERMINAL ROUTE: KILLED  (at this exact architecture scope)
  ```

  This does **not** kill sieve methods in general.

* `height_drop_20_19`, `no_universal_height_ratio`, `height_ratio_le` : the genuine `20 → 19`
  regression.

  ```text
  raw forced-zero + contact arithmetic  does NOT imply  N_child ≤ (1-η) N_parent
  for a universal η > 0.       FIXED-RATIO DESCENT ARCHITECTURE: KILLED
  ```

* `DEPTH_ONE_TERMINAL_SPLICE` : `retired` (see §4.2).

A kill is a statement about an *architecture*, never a falsification of a mathematical target
(`Routes.killed_not_false_target`).

Not reopened in this run (kept as previously established, or as previously closed/killed):
generic CUT/cactus gluing, TREE marginal integrality, 2TERM, abstract UNI-MARG classification,
the old WNU route, raw blocked-coordinate `f_p`, direct root-to-terminal incidence, generic
proper-power opacity.  The earlier structural bank (TREE branch polytope, two-terminal path
theorem, unicyclic bad-pattern classification, OR-anchor fractional gap classification, local
arithmetic bad traces, the embedded `53/59/71` bad triangle, and the firewall that a local bad
trace inside a `β ≫ 1` block is not an isolated `β = 1` counterexample) remains in its own frozen
layers and is untouched.

---

## 7.  Superseded owners

```text
LOG_FORM_CHARGE   (∑ N_p / log N_p ≲ |E| + F)   superseded by LINEAR-CHARGE
```

Superseding is not falsification (`Routes.superseded_not_false`).

---

## 8.  Two route-specific closure DAGs

`GateLedger.anchoredDAG`:

```text
ENTRY_EXISTENCE → SAFE_DESCENT_SUPPLY → GUARDED_ABSORBER_ANALYTIC_SUPPLY
  → EXACT_VALUE_1_CONFIGURATION → ANCHORED_BRIDGE → ORIGINAL_COUNTEREXAMPLE
```

`GateLedger.contactDAG`:

```text
STRICT_HEIGHT_EXCEPTIONAL_LEAF_CAPACITY → GATE_A_CLOSED → GATE_B_EXCEPTIONAL_CLEANUP
  → ALL_BETA_ONE_BAD_BLOCKS_EXCLUDED → GATE_C_REDUCED_EXCESS_CONTRADICTION
  → CONTACT_CONTRADICTION_INTEGRALITY → GATE_D_BRIDGE → ORIGINAL_287
```

`dags_disjoint` records that the two DAGs share no arrow.  Every analytic/unproved arrow is a
`Prop` parameter: `anchored_chain_composition` and `contact_chain_composition` compose *supplied*
implications and inhabit nothing.

---

## 9.  Current route-specific owners

```lean
currentOwner ResearchRoute.anchoredV4      = ENTRY_EXISTENCE
currentOwner ResearchRoute.contactCoreV5   = STRICT_HEIGHT_EXCEPTIONAL_LEAF_CAPACITY
```

with the downstream V4 owners `SAFE_DESCENT_SUPPLY` and `GUARDED_ABSORBER_ANALYTIC_SUPPLY`
retained, and the downstream contact-core owners `GATE_A_GLOBAL_FOREST_CAPACITY`,
`GATE_B_EXCEPTIONAL_FAMILIES`, `GATE_C_REDUCED_EXCESS_CONTRADICTION` retained.
`routeOwners_disjoint` is the machine-checked owner firewall.

**Current contact-core research target (open):** in a finite no-ear owner forest in which every
first-power edge strictly changes `N_p = ⌊M/p⌋`, every surviving Croot-long first-power internal
node consumes `κ_{δ,B} N_p` interface coordinates, generic long rows are removable and exceptional
leaves lie only in first-power short layers or sparse `p`-adic tails — prove that such a forest
cannot exist at the required positive-density scale, or construct a complete physical
counterfamily.

---

## 10.  Gate A/B/C/D ledger

```text
Gate A:
    local classification CLOSED                (gateStatus Gate.A_local  = closed)
    global exceptional-leaf capacity OPEN      (gateStatus Gate.A_global = open)

Gate B:
    generic long FP PAY                        (gateStatus Gate.B_generic_longFP = pay)
    generic PP PAY                             (gateStatus Gate.B_generic_PP     = pay)
    exceptional β=1 families OPEN              (gateStatus Gate.B_exceptional    = open)

Gate C:
    generic long rows PAY / REMOVED            (gateStatus Gate.C_generic_removed = pay)
    global reduced excess contradiction OPEN   (gateStatus Gate.C_global          = open)

Gate D:
    CLOSED                                     (gateStatus Gate.D = closed, kernelProof)

Erdős #287:
    OPEN                                       (erdos287Status = open)
```

Remaining Gate B families: short/transition first-power cycles, interface-heavy long first-power
cycles, heavy proper-power cycles, sparse-tail proper-power cycles.  Generic-family PAY is **not**
complete `β = 1` exclusion.

Reduced excess core (C-REDUCE): transition FP rows + linear-interface-heavy rows + sparse `p`-adic
interfaces.  Local taxonomy (A-CLASS): full-cube removable, positive-density interface-heavy,
first-power short/transition layer, sparse `p`-adic tail.

`gateD_closed_does_not_close_287` records that Gate D `CLOSED` does not close #287 without
Gates A–C; `no_closure_from_status` and `ledger_is_not_a_proof` record that no combination of
ledger statuses constructs a mathematical theorem.

---

## 11.  Exact regressions

`Regressions.lean` (finite statements only; a regression never certifies an asymptotic theorem):

1. factor-two denominator fixture — `regression_factor_two`;
2. doubled-denominator lattice `1/1056 + 1/1080 = 89/47520` — `regression_doubled_lattice`;
3. `53 — 317 — 79` depth-two splice — `regression_depth_two_splice`,
   `regression_path_transfer_fixture`;
4. proper-power forced-zero fixture `[34,100]`, `q = 16`, `d = 4` —
   `regression_cofactor_interval_34_100` (cofactor interval `[3,6]`),
   `regression_properPower_forced_zero` (`n₀ = 2`, `n₁ = 1`, `n₂ = 1`, first deficient layer
   `v✱ = 1`), `regression_forced_zero_valuation`, `regression_valuation_lift_34_100`;
5. `p`-adic saturation finite examples — `regression_padic_saturation` (four nonzero residues
   cover `𝔽₅`, three do not; `[2,1]` covers `𝔽₃`);
6. `4ℓ` raw-port bound finite example — `regression_raw_port_cap`;
7. strict-height exhaustive finite checks — `regression_strict_height`, plus
   `strictHeight_regression_sweep1000`;
8. `20 → 19` no-fixed-ratio-drop fixture — `regression_no_fixed_ratio`;
9. primorial local-factor cancellation — `regression_primorial_cancellation`.

---

## 12.  Axiom audit

`RequestProject/Erdos287/ResearchBankV5/AxiomAudit.lean` runs `#print axioms` on **every**
principal new kernel theorem of the V5 layer (86 declarations, grouped A–J).  Result: every
reported dependency is a subset of

```text
propext, Classical.choice, Quot.sound
```

and several theorems depend on no axioms at all (for example all meta-layer firewalls, and
`ppRow_ne_naive`/`valuationLift_*` use only `propext`).  **No** `sorryAx`, no custom axiom, and no
`_native` / compiler-trust axiom occurs.

---

## 13.  Placeholder audit

A textual search of the whole new layer for

```text
sorry   admit   axiom   native_decide   unsafe   opaque   implemented_by
```

returns **no syntactic occurrence**.  The only matches are prose/documentation:

* `StrictHeight.lean` lines 31 and 142 contain the English word "admit" ("admit no unit
  contact") inside docstrings;
* `Routes.lean` line 41 and `AxiomAudit.lean` lines 14–22 mention the words "axioms",
  "`sorry`", "`native_decide`" etc. inside documentation describing the audit itself.

No declaration in the layer is `unsafe`, `opaque`, `noncomputable`-by-axiom, `native_decide`-based
or `@[implemented_by]`-annotated.  (`rowExp`, `PPRow` are `noncomputable` merely because they use
`padicValNat`.)

---

## 14.  Build output

```text
lake build RequestProject.Erdos287.ResearchBankV5
  → Build completed successfully (8097 jobs), exit code 0
lake build                       (whole project, default target RequestProject)
  → Build completed successfully (8597 jobs), exit code 0
```

Warnings: the new layer compiles warning-free; the only warnings in the transitive build come from
the pre-existing frozen layers (`AnchoredV2/CapacityCertificate.lean` unused section variables,
`AnchoredV3/ConditionalClosure.lean` unused variables).  These files were **not** modified.

Commit of the banked layer: `03603a5155d5448649edeaf30038cedb85a82068` (further commits follow
with the two Markdown documents).

### 14.1  Whole-project build

The default target `RequestProject` builds the entire tree, including the new layer: **8597 jobs,
success, no errors**.  The build log contains 24 warnings, all from pre-existing layers (unused
variables / unused section variables in `AnchoredV2` and `AnchoredV3`, and Mathlib `Try this`
suggestions in older files).  No `sorryAx` occurs anywhere in the log.  No older layer was
modified to make any build succeed.

---

## 15.  Semantic / firewall caveats

```text
A route-aware research ledger is not a proof of route equivalence.

Anchored V4 and the Contact-core programme remain distinct.

A theorem proved in one route may be reused in the other only through an explicit proved bridge.

No OPEN external analytic statement is inhabited merely because it is recorded as BANKED research
state.
```

Further caveats:

* **STRICT-HEIGHT firewall (mandatory).**  STRICT-HEIGHT is an *edge* statement.  It gives

  ```text
  same-height edge:                     impossible
  same-height first-power cycle:        impossible
  global monotone descent:              NOT PROVED
  ```

  An undirected owner path may zigzag; `strict_change_not_monotone` is the explicit witness.
* **Gate A** is closed only in its *local row-language classification*; the global
  forest/capacity theorem is open.  **Gate B** generic-family PAY is not complete `β = 1`
  exclusion.  **Gate C** is reduced but open.  **Gate D** closed does not close #287.
* The deep-gate count (`STRICT_HEIGHT_EXCEPTIONAL_LEAF_CAPACITY`,
  `REDUCED_BETA_GE_2_EXCESS_CORE_CONTRADICTION`) is **descriptive metadata only**, not a claim
  that these are the only possible future lemmas.
* `PadicSaturationStatement` (global PADIC-SAT), `PPRow`-completeness at the programme scale, and
  every Croot/FP input remain uninhabited `Prop`s.

---

## VERDICT

```text
VERDICT:
ERDOS287_ROUTE_AWARE_MASTER_BANK_V5_CREATED

Anchored V2/V3/V4:
    untouched

Anchored V4 exact mathematics:
    preserved

Anchored V4 open owners:
    preserved

Contact-core path transfer:
    banked

Complete PP row:
    banked

P-adic saturation:
    banked where kernel-proved (layer-local digit step); global statement OPEN

Raw PP terminal cap ≤ 4ℓ:
    banked

Valuation lift:
    banked

Croot asymptotic interfaces:
    external / conditional only

FP full-interface saturation:
    external analytic bank

LINEAR-CHARGE:
    banked conditional consequence

STRICT-HEIGHT:
    kernel bank

Gate A local classification:
    closed

Gate A global forest theorem:
    open

Gate B:
    open, generic long families paid

Gate C:
    open, reduced

Gate D:
    closed

Current Contact-core owner:
    STRICT_HEIGHT_EXCEPTIONAL_LEAF_CAPACITY

Erdős #287:
    OPEN

No route equivalence asserted.
No open owner inhabited.
No fake closure.
```
