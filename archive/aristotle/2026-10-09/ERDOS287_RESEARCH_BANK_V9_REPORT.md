# Erdős #287 — Research Bank V9 report (direct exclusion / graph / ASRA bank)

**Erdős #287 remains OPEN. This research bank does not prove or disprove it.**

## 1. Files added

```
RequestProject/Erdos287/ResearchBankV9.lean                     (aggregator; imports V8)
RequestProject/Erdos287/ResearchBankV9/GcdClique.lean           (§3A)
RequestProject/Erdos287/ResearchBankV9/AffineContact.lean       (§3B)
RequestProject/Erdos287/ResearchBankV9/CircularGraph.lean       (§3C)
RequestProject/Erdos287/ResearchBankV9/Occupancy.lean           (§3D)
RequestProject/Erdos287/ResearchBankV9/Gates.lean               (§3E)
RequestProject/Erdos287/ResearchBankV9/GraphLocalization.lean   (§3F)
RequestProject/Erdos287/ResearchBankV9/ArchitectureLimit.lean   (§3G)
RequestProject/Erdos287/ResearchBankV9/AsraCRT.lean             (§4A–4C)
RequestProject/Erdos287/ResearchBankV9/AsraPrimeSlot.lean       (§4D–4E)
RequestProject/Erdos287/ResearchBankV9/AsraZeroMode.lean        (§4F)
RequestProject/Erdos287/ResearchBankV9/AsraClearing.lean        (§4G)
RequestProject/Erdos287/ResearchBankV9/AsraInterfaces.lean      (§4H–4I)
RequestProject/Erdos287/ResearchBankV9/Splice.lean              (§5)
RequestProject/Erdos287/ResearchBankV9/Ledger.lean              (§6, V9 part)
RequestProject/Erdos287/ResearchBankV9/AxiomAudit.lean          (#print axioms, all V9 theorems)
ERDOS287_RESEARCH_BANK_V9_REPORT.md
```

Namespaces: `Erdos287.ResearchBankV9.<FileName>`.

## 2. No prior layer modified

Only new files were added (checked with `git diff --name-status` against the initial commit).
V2–V7 and `ARISTOTLE_SUMMARY.md` are untouched. V9 uses, without modifying, the project's
existing `Erdos287Counterexample`, `Gap2CE`, `ExcludedPP`, `Gap2CE.excludedPP_blockerPair` and the
harmonic-tail lemma `exp_lower`.

## 3. Declarations proved internally

**§3A Gcd clique** (`GcdClique`): `gcd_eq_diff_iff`, `clique_translate_iff`,
`gcd_lcm_dvd_lcm_gcd`, `two_crt`, `crt_exists` (general CRT for pairwise-compatible systems),
`compatible_of_solution`, `crt_exists_ge`, `cliqueSystem_ne_zero`, **`gcdClique_of_compatible`**
(compatible congruence system ⟹ a translate `C ≥ C₀` with `gcd(C+b_i, C+b_j) = |b_i − b_j|`),
`compatible_of_clique` (converse), `clique_0124`, `shape_matters` ({0,1,2,3} admits no translate).

**§3B Affine contact** (`AffineContact`): `cofactors`, **`affine_contact_identity`**
((a_j/g)F_i(t) − (a_i/g)F_j(t) = 1 with F(t) = a t + 1, g = gcd = a_j − a_i),
`contact_locations`, `contact_in_window_iff`, `contact_example`.

**§3C Circular graph** (`CircularGraph`, G(n,r) on ℤ/n, edge iff circular distance ≥ r+1,
n > 3r): `near_iff`, `card_le_of_diam`, **`indep_card_le`** (α ≤ r+1), `arc_indep` (α ≥ r+1),
`fracColouring_value_ge`, `arcColouring_value`, **`fractional_chromatic_eq`** (explicit
fractional colouring of value n/(r+1), and every fractional colouring has value ≥ n/(r+1)).
Fractional colourings are the explicit finite certificate structure `FracColouring`.

**§3D Occupancy** (`Occupancy`): **`occupancy_forces_edge`** (each vertex ≤ m cells, α ≤ r+1,
≥ (r+1)m+1 occupied cells ⟹ an edge), **`occupancy_programme`** (a = (r+1)m, Q = ⌈A a⌉ + 1
placed cells, loss bound ⟹ edge among survivors), `circular_occupancy`.

**§3E Gates** (`Gates`): `gate_13_3` (α(G(13,3)) = 4, χ_f = 13/4), `gate_145_38` (α = 39,
χ_f = 145/39), `gate_ineq` (26/7 < 145/39), `gate_margin` (7/13 − 78/145 = 1/1885 > 0),
`gate_iff` (for θ > 0: 2/θ < 145/39 ⟺ θ > 78/145), `gate_eq_rho_add_one`,
`localization_constant` (106/39 < e and 1/e < 39/106, from Mathlib's proved bound on `exp 1`),
`gate_near_architecture_limit` (metadata-level arithmetic only).

**§3F Graph localization** (`GraphLocalization`): `contact_above_N`, `contact_contradiction`,
`Rigid.excluded`, **`no_gap2CE_of_usefulEdge`**, **`no_erdos287Counterexample_of_usefulEdge`**:
a `UsefulEdgeData M c` (edge a_i < a_j with gcd = a_j − a_i, both affine values prime with
bounded-cofactor rigidity, contact z, z+1 in [cM, M]) with c > 1/e rules out every #287
representation with maximum M. The pieces (contact arithmetic, rigidity ⟹ exclusion, gap ≤ 2 /
blocker pair, harmonic tail) are separate lemmas.

**§3G Architecture limit** (`ArchitectureLimit`): `periodic_indep`, `periodic_cover`,
**`architecture_upper_limit`** (periodic-interval fractional colouring of value (D+d)/d, i.e.
χ_f ≤ ρ+1 for useful distances in [d, ρd]), `limit_eq_rho_add_one`, `gate_is_limit_at_rho`.
The requirement ρ < e is not asserted.

**§4A–4C ASRA CRT** (`AsraCRT`): `root_iff_slot`, `slot_unique`, `dvd_Dmod_iff`, `Dmod_pos`,
`exists_root_mod`, **`crt_root_bijection`** (under non-exceptional hypotheses: roots b mod D of
Φ_i ↔ prime-to-spectator-slot allocations; each root determines a unique slot per prime,
roots are determined by their allocation, every allocation is realised),
`roots_distinguish_allocations`, **`collision_zero`**, `spectator_collision_zero`,
`joint_modulus_iff` (combined modulus is lcm), `lcm_ne_product_fixture`, `clean_main_modulus`
(with (B, Dd) = 1 and (D, d) = 1 the lcm is the product and φ is multiplicative).

**§4D–4E Prime slot / large overlap** (`AsraPrimeSlot`): **`primeSlot_truncation`**,
`primeSlot_truncation_sq` (on the prime-pair locus with both values > R the Maynard sum equals
the truncated `V_ij` with d_i = d_j = 1), `upper_sieve_majorization` (nonnegative physical
sequence ⟹ majorization step), `dvd_sum_eq_root_classes` (divisor decomposition into root
classes mod g).

**§4F Zero mode** (`AsraZeroMode`): `sol_unique`, `sol_exists`, `compat_of_sol`, `zeroMode_card`,
**`zeroMode_density`** (density = (1/L)·1[c₁n₂ ≡ c₂n₁ mod g], units guarded by `IsCoprime`
hypotheses), `compat_iff_ratio`, **`centred_kernel_eq`**, `ratio_indicator_average`,
`centred_kernel_sum_zero`.

**§4G Clearing** (`AsraClearing`): **`clearing_iff`** (q ∣ u m n − v ⟺ q ∣ (U m) n − (U/u) v for
u ∣ U, (U, q) = 1), `alphaT_support` (U ∣ m'), `alphaT_mul`, `alphaT_divisor_bound`,
`base_progression_iff` (m'n ≡ U p₀ mod U B), `fixed_denominator_does_not_delete_base`.

**§4H firewalls** (`AsraInterfaces`): `nonzeroFrequencyTransfer_not_automatic`,
`signedSieveMainTerm_not_automatic`, `asra_not_automatic` (explicit data for which each fails,
so none is a vacuous interface).

**§5 Splice** (`Splice`): **`splice`** (finite verification through U + M₀ ≤ U+1 + eventual
exclusion from M₀ ⟹ full exclusion), `current_M0_unavailable`, `M0_ge`,
`effectiveSplice_iff_no_counterexample` (hence the splice is not claimed),
`asymptotic_without_threshold_does_not_splice`, `finite_obstruction_not_asymptotic`,
`conditional_does_not_inhabit_premise`.

**§6 Ledger** (`Ledger`): `v9New_no_closed`, `v9_no_closed`, `v9_erdos287_open`,
`v9_record_external_not_proved`, `v9_proved_implies_kernel`, `asra_epochs`, `splice_blocked`,
`step_provedNodes`, `derivable_eq`, **`no_ledger_path_closes_erdos287`** (closure-DAG propagation
from the PROVED nodes never reaches "Erdős #287"), `every_edge_has_open_premise`.

## 4. Declarations conditional on parameters / interfaces

* `GraphLocalization.no_counterexample_above_of_edge_supply` — premise: every M ≥ M₀ carries
  `UsefulEdgeData M c` (edge supply = prime supply; never inhabited).
* `AsraPrimeSlot.primePair_bound_of_upperSieve` — premise `UpperSieveInput` (Iwaniec/Maynard).
* `AsraPrimeSlot.largeOverlap_tail_bound` — premise `ShiuAffineDivisorMomentInput`.
* `AsraZeroMode.smallOverlap_zeroFrequency_bound` — premise `ZhengRatioBVInput`.
* `AsraInterfaces.asra_of_components` — premises `DecompositionIdentity`,
  `ExternalLargeOverlapInput`, `ExternalRatioBVInput`, **`ASRA_NonzeroFrequencyTransfer`**,
  **`ASRA_SignedSieveMainTerm`** ⟹ `ASRA D`.
* `AsraInterfaces.pairCoefficient_below_gate_of_asra` — `ASRA D` + explicitly supplied
  `κ < 145/39` + positive scale ⟹ pair sum eventually below 145/39 · scale.
* `Splice.eventual_exclusion_conditional` — ASRA + a `PrimeSupply` proposition + chain
  hypothesis (occupancy/localization/prime supply ⟹ edge data for all M ≥ M_an) ⟹
  `EventualNoCounterexampleFrom M_an`. M_an is a parameter; none is constructed.
* `GcdClique.PrescribedShapeGCDClique` and `PrimeValuesOnClique` are separate propositions;
  the prime-values one is never assumed inside the clique theorems.

## 5. External analytic interfaces left uninhabited

`UpperSieveInput`, `ShiuAffineDivisorMomentInput`, `ZhengRatioBVInput`,
`ExternalLargeOverlapInput`, `ExternalRatioBVInput`, `ASRA_NonzeroFrequencyTransfer`,
`ASRA_SignedSieveMainTerm`, `ASRA`, `PrimeValuesOnClique`, the edge-supply hypothesis,
`EffectiveFiniteSplice`. They are `Prop`-valued structures/definitions with no instance, no
default constructor and no proof in the project; the two open ASRA interfaces and ASRA are
shown *not* automatically true.

## 6. Historical / status distinctions (V9 ledger rows, `Ledger.v9New`)

| row | status |
|---|---|
| gcd-clique CRT core | PROVED |
| prescribed-shape box placement (union bound) | OPEN (not formalized) |
| Maynard prime supply on the clique | CONDITIONAL / external |
| affine contact identity | PROVED |
| circular graph α, χ_f | PROVED |
| graph-selective occupancy | PROVED |
| 145/39 gate; 26/7 < 145/39 | PROVED |
| 7/13 − 78/145 = 1/1885 | PROVED |
| localization constant 39/106 > 1/e | PROVED |
| graph localization ⟹ no representation (given edge data) | PROVED |
| architecture limit χ_f ≤ ρ+1 | PROVED |
| three-group A<3 architecture | SUPERSEDED |
| arbitrary-F A≥3 moment route | KILLED METHOD |
| Chen parameter tuning below 3 | KILLED METHOD |
| ASRA = FULL WRITTEN CANDIDATE | SUPERSEDED (historical epoch, certification rollback) |
| CRT / collision / main modulus / prime-slot / divisor decomposition / zero mode / clearing | PROVED (algebra) |
| Iwaniec–Maynard upper sieve, Shiu, Zheng ratio-BV | CONDITIONAL / external |
| ASRA_NonzeroFrequencyTransfer | OPEN |
| ASRA_SignedSieveMainTerm | OPEN |
| ASRA assembly implication | CONDITIONAL |
| full ASRA | OPEN |
| eventual all-large exclusion | CONDITIONAL |
| M_an; finite verification through M₀−1 | OPEN |
| effective finite splice | BLOCKED |
| historical endpoint ≈ 6.125×10^120 | HISTORICAL METADATA (not reverified, not used) |
| Erdős #287 | OPEN |

The V8 ledger (itself containing the frozen V7 ledger) is prefixed: `v9Ledger = v8Ledger ++ v9New`.

## 7. Build result

```
lake build RequestProject.Erdos287.ResearchBankV9   → Build completed successfully (8158 jobs).
lake build RequestProject.Erdos287.ResearchBankV8   → Build completed successfully (8142 jobs).
lake build                                         → Build completed successfully (8653 jobs).
```
No errors; no warnings in V8/V9 files (the only warnings are pre-existing ones in older layers).

## 8. `#print axioms`

`ResearchBankV9/AxiomAudit.lean` prints axioms for all 114 V9 theorems: 83 × `[propext,
Classical.choice, Quot.sound]`, 14 × `[propext, Quot.sound]`, 8 × `[propext]`, 9 × none.
No `sorryAx`, no `Lean.ofReduceBool` / `Lean.trustCompiler`, no `_native` axiom, no custom axiom.

## 9. Forbidden-token scan

`rg -w "sorry|admit|axiom|unsafe|native_decide|bv_decide|opaque|implemented_by"` over all V8/V9
files: only the `#print axioms` lines and docstrings saying these constructs are not used. No
code use. Kernel `decide` is used only on closed finite data (gates, fixtures, ledger lists).

## 10. Current open owners

* `ASRA_NonzeroFrequencyTransfer` (full root-coloured nonzero-frequency Type-I/II transfer) — OPEN.
* `ASRA_SignedSieveMainTerm` (complete signed upper-sieve main-term evaluation) — OPEN.
* Prime supply on the prescribed-shape clique (Maynard-type) — external.
* Prescribed-shape box placement / union-bound argument — not formalized (OPEN in the ledger).
* Effective analytic threshold M_an — absent (`currentThresholds.M_an = none`); M₀ unavailable;
  effective finite splice BLOCKED.
* From V8: target-scale ENTRY, GOOD-M survivor supply.

## 11. Honest deviations / limits

* §3A: only the CRT core (compatible system ⟺ gcd clique after translation) is formalized; the
  existence of offsets inside prescribed scaled boxes via the union bound is **not**.
* §3C/3G: fractional chromatic number is expressed via explicit finite `FracColouring`
  certificates (lower bound for all certificates in §3C; upper-bound construction in §3G),
  not via a general Mathlib fractional-chromatic API.
* §4F: the zero-mode density and centred kernel are banked; the "mixed/principal" densities are
  represented by the `principal` term and `ratio_indicator_average`, not as separate density
  theorems for each mixed case.
* §4H/4I: ASRA and its interfaces are modelled over an abstract `ASRAData` record with real
  functions of X in an ε–X₀ little-o form; the concrete Maynard weights are not instantiated.
* §5: the finite thresholds `M_geom, M_int, M_rig` are recorded as `0` placeholders in
  `currentThresholds` (no values banked); `M_an = none`.

## Machine-readable ledger (V9 new rows)

```
GCD_CLIQUE_CRT_CORE=PROVED
PRESCRIBED_SHAPE_BOX_PLACEMENT=OPEN_NOT_FORMALIZED
PRIME_VALUES_ON_CLIQUE=EXTERNAL
AFFINE_CONTACT_IDENTITY=PROVED
CIRCULAR_GRAPH_ALPHA_CHIF=PROVED
GRAPH_SELECTIVE_OCCUPANCY=PROVED
GATE_145_39=PROVED
GATE_MARGIN_1_1885=PROVED
LOCALIZATION_CONSTANT_GT_INV_E=PROVED
GRAPH_LOCALIZATION_IMPLICATION=PROVED
ARCHITECTURE_LIMIT=PROVED
THREE_GROUP_A_LT_3=SUPERSEDED
ARBITRARY_F_A_GE_3=KILLED
CHEN_TUNING_BELOW_3=KILLED
ASRA_FULL_WRITTEN_CANDIDATE=SUPERSEDED
ASRA_CRT_COLLISION_MODULUS=PROVED
ASRA_PRIME_SLOT_TRUNCATION=PROVED
ASRA_LARGE_OVERLAP_ADAPTER=CONDITIONAL_ON_SHIU
ASRA_ZERO_MODE_ALGEBRA=PROVED
ASRA_ZERO_MODE_BOUND=CONDITIONAL_ON_ZHENG
ASRA_CLEARING=PROVED
ASRA_NONZERO_FREQUENCY_TRANSFER=OPEN
ASRA_SIGNED_SIEVE_MAIN_TERM=OPEN
ASRA=OPEN
EVENTUAL_ALL_LARGE_EXCLUSION=CONDITIONAL
M_ANALYTIC=NONE
EFFECTIVE_FINITE_SPLICE=BLOCKED
ERDOS_287=OPEN
```

Erdős #287 remains OPEN. This research bank does not prove or disprove it.
