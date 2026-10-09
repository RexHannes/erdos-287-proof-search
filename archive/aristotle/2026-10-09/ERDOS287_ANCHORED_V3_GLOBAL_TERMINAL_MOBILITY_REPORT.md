# ERDŐS #287 — ANCHORED V3 GLOBAL TERMINAL MOBILITY REPORT

**Mode.** Strict append-only. Anchored V2 frozen. Global-neutral terminal compiler. Target
mobility. Exact coefficient hit formulation. Resonance interfaces. No false asymptotic
inhabitation. No frontier extension. No counterexample claim. Axiom-audited.

**Verdict.** `BANKED_ANCHORED_V3_GLOBAL_TERMINAL_MOBILITY`.

Erdős #287 remains **OPEN**. Nothing in this layer proves, refutes, or claims a counterexample
to #287, and nothing extends the certified finite frontier `67108856338751594` (U2 still
pending, unchanged).

---

## 1. Files added

All new files are under `RequestProject/Erdos287/AnchoredV3/`, plus the aggregator
`RequestProject/Erdos287/AnchoredV3.lean`:

| File | Content |
|---|---|
| `GlobalNeutrality.lean` | rowwise vs. global multiplier neutrality; exact terminal completion; `D = D_core · U_mult` |
| `OldEmptyNewHit.lean` | the exact old-empty / new-global-hit finite certificate |
| `ColumnZeroPatterns.lean` | column zero patterns, exact integer weights, reciprocal identity |
| `GlobalColumnCompiler.lean` | the complete fixed-bank global column compiler |
| `ColumnPackets.lean` | zero-sum packet extraction and the packet-abundance firewall |
| `SupportMultiplicity.lean` | finite support-size / multiplicity skeleton; OPEN row-fibre owner |
| `ColumnLattice.lean` | Boolean column gcd theorem, telescoping certificate, sharpness witness |
| `TargetMobility.lean` | fixed-bank target mobility, denominator control, target movement |
| `MobilityStructure.lean` | distinctness, AP-freeness, `2^H` / `3^H` counts, cofactor gcd |
| `AlignmentPolynomial.lean` | exact combined terminal × mobility coefficient; mobility coset |
| `FourierHitInterface.lean` | exponential tilt, exact finite characteristic function, OPEN bridge |
| `BaselineCentrality.lean` | compatible / central baseline, bounded tilt, OPEN interface |
| `ResonanceInterfaces.lean` | conductor activity, zero phase, factorisation, OPEN budgets |
| `ConditionalClosure.lean` | the exact dependency theorem |
| `OpenOwners.lean` | the remaining open owners, incl. references to the V2 owners |
| `Reconciliation.lean` | the append-only V3 ledger |
| `AxiomAudit.lean` | `#print axioms` for every principal V3 theorem |

## 2. Exact imports added

* `RequestProject/Main.lean`: one line, `import RequestProject.Erdos287.AnchoredV3`
  (inserted directly after the existing `import RequestProject.Erdos287.AnchoredV2`).
* Inside V3: `ColumnLattice.lean` imports `RequestProject.Erdos287.AnchoredV2.UnitSubsetSum`
  (used, not modified); `OpenOwners.lean` imports `RequestProject.Erdos287.AnchoredV2.RouteBridge`
  and `RequestProject.Erdos287.AnchoredV2.CoupledBatchSupply` purely to *reference* the inherited
  open owners. All other V3 modules import `Mathlib` and earlier V3 modules only.

No V2 file was edited, renamed, weakened, deleted or re-proved.

## 3. Exact theorem list (all proved, no `sorry`)

### A. Global multiplier neutrality (`GlobalNeutrality.lean`)
* `globalNeutral_of_rowwiseNeutral` — rowwise ⇒ global (the converse is deliberately not proved).
* `witnessData_globalNeutral`, `witnessData_not_rowwiseNeutral`,
  `exists_globalNeutral_not_rowwiseNeutral` — explicit finite witness of
  `GlobalNeutral ∧ ¬ RowwiseNeutral`.
* `rowwise_sufficient_not_necessary` — the old compiler is a sound but **incomplete** subspace.
* `exact_rowwise_subset_global` — rowwise-neutral exact completions ⊆ globally neutral ones.
* `lcm_union`, `modulus_eq_core_mul_mult`, `dvd_modulusLcm` — `D = lcm_r m_r` and, under explicit
  coprimality, `D = D_core · U_mult`. (No asymptotics such as `log U_mult = O(R)`.)

### B. Old-empty / new-hit certificate (`OldEmptyNewHit.lean`)
* `coincidence` — `74 · 5407 = r₁ + r₂` with `r₁ = 199777`, `r₂ = 200341`.
* `newHit_reciprocal` — `1/n₁ + 1/n₂ = 1/(r₁ r₂)` for `n_i = 74 r_i · 5407`.
* `newHit_exact` — `S₀ + 1/n₁ + 1/n₂ = 1` for `S₀ = 1 − 1/(r₁ r₂)`.
* `n₁_le_siteBound`, `n₂_le_siteBound` — both new sites obey the bank bound `10^11`.
* `OldCompletion.four_le_card` — nonzero row targets + rowwise parity ⇒ at least four terms.
* `OldCompletion.four_div_siteBound_le_sum`, `gap_lt_four_div_siteBound`, `old_empty` — the exact
  rational lower bound exceeds `1 − S₀`, so the old model is empty on this bank.
* `same_bank_old_empty_new_global_hit` — the packaged certificate.

**Scope firewall.** This is a statement about rational sums only. It does not assert a full
background word, is not a #287 counterexample, and does not extend the finite frontier.

### C. Column zero patterns and the global compiler
* `sum_recip_zeroPattern` — `∑_{r∈E} 1/(m_r ℓ) = w_ℓ(E)/D` for a zero pattern `E`.
* `zpWeight_mul` — `ℓ · w_ℓ(E) = ∑_{r∈E} D/m_r`.
* `Bank.mem_weights_iff`, `Bank.delta_eq_of_neutral`.
* `Bank.globalColumnCompiler` — **the exact fixed-bank equivalence**
  `(∃ globally band-neutral selection with S + Δ = 1) ↔ T ∈ additive support of the column
  zero-pattern weights`, where `D(1 − S) = T`. `Bank.globalColumnCompiler_baseline` is the
  instance at the preparation baseline. The support is recorded as the exact support set
  (`Bank.InSupport`), which carries exactly the information of `∏_ℓ F_ℓ(X)`; no per-row
  multiplier neutrality appears anywhere.

### D. Column zero-sum packets (`ColumnPackets.lean`)
* `zeroSum_block_of_prefix_collision`, `exists_zeroSum_subset` — pigeonhole on `ℓ+1` prefix sums.
* `exists_zeroSum_subset_two_le` — no singleton packets when all coefficients are nonzero.
* `exists_disjoint_packets` — at least `⌊n/ℓ⌋` pairwise disjoint packets of size `2 … ℓ`;
  fewer than `ℓ` entries remain.
* `sum_biUnion_eq_zero` — any union of disjoint packets preserves column neutrality.
* `manyNeutralPackets_not_exactTarget` — **firewall**: packet abundance does not give a hit.

### E. Support size / multiplicity (`SupportMultiplicity.lean`)
* `RowFibreData.card_fiber_le_prod` — fixing the output fixes the residue in every row, so the
  multiplicity is at most `∏_r B_r`.
* `RowFibreData.card_image_ge` — number of distinct outputs ≥ (matrix count) `/ ∏_r B_r`.
* `RowFibreData.AsymptoticUniformRowFibres` — **OPEN** analytic owner (not inhabited);
  `uniformRowFibreBound_of_asymptotic` converts it into the finite hypothesis if ever supplied.
* The source-side conclusion `log |support| = (1+o(1))√M` is **not** stated as proved anywhere.

### F. Boolean column gcd theorem (`ColumnLattice.lean`)
* `exists_subset_sum_eq_finset` — `Finset` form of the V2 unit subset-sum theorem (V2 unchanged).
* `coeff_gcd_dvd_patternWeights_gcd` — easy inclusion.
* `gcd_patternWeights_dvd_coeff` — the constructive telescoping certificate:
  `a_i = ∑_{t ∈ ZMod q} ( w(E⁺_{i,t}) − w(E⁰_{i,t}) )` with
  `E⁰_{i,t} = S t ∪ T(−t)`, `E⁺_{i,t} = {i} ∪ S(t − a_i) ∪ T(−t)`.
* `boolean_column_gcd` — for `q ≥ 2`, positive `q`-units and `n ≥ 2q − 1`:
  `gcd { w(E) } = gcd { a_i }`.
* `sharpness_witness_two` — at `n = 2q − 2` (`q = 2`, coefficients `1, 3`) the raw gcd is `1`
  while the zero-pattern weight gcd is `2`.

**Firewall.** This is an integer span / gcd statement; patterns overlap and subtraction is used,
so it does **not** construct a Boolean selection hitting an arbitrary target.

### G. Target mobility (`TargetMobility.lean`)
* `MobilityData.S_eq_num_div`, `MobilityData.den_dvd_Dcore` — `den(S_y) ∣ D_core`.
* `MobilityData.prime_dvd_den_imp_dvd_Dcore` — inherited paid components stay paid.
* `MobilityData.mobility_support_disjoint` — reserved positions are disjoint from the terminal
  bank sites, the old repair sites and the fixed pins, so the *same* terminal support object is
  used for every `y`.
* `no00_preserved` — no-`00` preserved under the declared guard hypotheses.
* `MobilityData.target_movement` — `T_y = D(1 − S_y) = T_* − ∑_{i∈y} D/n_i` with `D = D_core·U`.
* `MobilityData.RealEntryWindow` — the real-mass qualification, defined and **never assumed**:
  the theorems preserve arithmetic/path preparation only.

### H. Distinctness and AP-free mobility (`MobilityStructure.lean`)
* `MobilityFamily.W_injective_of_lt`, `W_injective_boolean` — reduction modulo each private prime
  isolates one coefficient; all `2^H` Boolean sums are distinct.
* `MobilityFamily.no_three_term_ap` — `W y + W z = 2 W w` forces `y = z = w`.
* `MobilityFamily.card_targets` = `2 ^ H`, `card_targets_add_targets` = `3 ^ H`.
* `MobilityFamily.gcd_cofactors_eq_one` — the cofactors are globally coprime.
* Labelled **negative structure information**: many movable targets do not give a long AP or an
  interval. The additive-energy identity `6^H` was **not** formalised.

### I. Exact combined alignment coefficient (`AlignmentPolynomial.lean`)
* `AlignedBank.target_moved` — `D(1 − S_y) = T_y`.
* `AlignedBank.alignment_coefficient` — **central V3 theorem**: a mobility choice plus a globally
  band-neutral terminal choice with `S_y + Δ = 1` exists **iff** `T_*` decomposes as
  (terminal support weight) + (mobility weight), i.e. iff the coefficient of `X^{T_*}` in
  `F(X) M_Z(X)` is positive.
* `AlignedBank.alignment_sumset` — the same statement as `T_* ∈ F + M_Z` (pointwise Finset sum).
* `mobility_cofactor_gcd` — `gcd { D/n_i } = D/G`, `G = ∏ n_i`: mobility targets remain in one
  explicit congruence coset. No claim that mobility alone repairs a terminal lattice obstruction.

### J. Fourier / exponential-tilt interface (`FourierHitInterface.lean`)
* `FiniteCoeff.Z_pos`, `sum_prob`, `norm_char_le_one` — exact finite identities for the tilted
  distribution and its characteristic function.
* `FiniteCoeff.AntiHoleInput`, `FourierAntiHoleCriterion` — the target-specific criterion
  (mean `= T`, `σ ≥ 1` equal to the tilted standard deviation, arc bound `< 5/(3σ)`).
* `AntiHoleBridge` — **OPEN**; never inhabited, never axiomatised.
* `coeff_pos_of_antiHoleBridge` — the purely logical conditional bridge.
* The analytic Fourier-inversion proof (inversion, `cos x ≥ 1 − x²/2`, central interval) is
  **not** formalised; it is exactly what `AntiHoleBridge` owns.

### K. Bounded tilt / central baseline (`BaselineCentrality.lean`)
* `CompatibleBaseline`, `CentralBaseline`, `BoundedTilt` — the three distinct notions.
* `CentralityToBoundedTilt` — **OPEN** analytic interface, not inhabited.
* `mobility_cannot_repair_macroscopic_gap`, `mobility_capacity_fraction` — the exact finite
  scope facts: mobility capacity is a lower-order fraction of terminal capacity and cannot
  repair a baseline whose gap exceeds the total capacity.

### L. Resonance interfaces (`ResonanceInterfaces.lean`)
* `notMem_activeRows_iff` — which rows carry zero phase at a divisor frequency.
* `activeRows_private_prime` — a private core prime activates only its own row.
* `zero_phase_of_dvd` — exact triviality of the phase when the conductor divides the cofactor.
* `norm_columnProduct`, `norm_columnProduct_le_one` — factorisation over distinct columns.
* `norm_mobilityFactor_le_one` — mobility factors have modulus at most `1`.
* `SparseActive` — combinatorial predicate with a **generic cutoff** (no logarithmic arithmetic).
* `SparseResonanceArcBudget`, `CentralLobeBudget`, `RemainingSpectrumBudget` — **OPEN**, never
  inhabited; `arc_bound_of_budgets` is the exact finite combination lemma.

### M. Conditional closure (`ConditionalClosure.lean`)
* `CoefficientModel` — the interface saying a finite coefficient object models `F·M_Z`.
* `conditional_terminal_closure` — under a compatible baseline, a central baseline, legal
  mobility reservations, the instantiated global column compiler, the bounded-tilt interface and
  the three spectrum budgets with total constant `< 5/6`, together with the OPEN
  `AntiHoleBridge` and a coefficient model: the exact target coefficient is positive and an exact
  globally band-neutral terminal completion exists. **The chain stops there**; no bridge to a
  global #287 counterexample exists or is invented.

### N. Open owners (`OpenOwners.lean`)
`CompatibleActualBaseline`, `CentralCompatibleActualBaseline`, `CentralityToBoundedTiltOwner`,
`AntiHoleBridgeOwner`, `SparseResonanceArcBudgetOwner`, `CentralLobeBudgetOwner`,
`RemainingSpectrumBudgetOwner`, plus references (no re-proof, no weakening) to the inherited V2
owners `FixedPowerCoupledSupply`, `UniformNegativeCapacity`, `UniformLevel2Rejection`. None is
inhabited. There is no custom `axiom` and no theorem named `erdos287_closed`, `counterexample`
or `fullClosure`.

## 4. Old vs. new search-space comparison

| | old (rowwise) model | new (globally neutral) model |
|---|---|---|
| legality | every row increment individually kills every multiplier-prime component | only the **sum over rows** must kill them |
| formal relation | `RowwiseNeutral` | `GlobalNeutral`; `globalNeutral_of_rowwiseNeutral` gives ⊆ |
| strictness | — | strict: `exists_globalNeutral_not_rowwiseNeutral` |
| certificate on the fixed bank of §B | empty: every legal completion needs ≥ 4 terms and thus sum `> 1 − S₀` (`old_empty`) | hit: 2 terms, `S₀ + 1/n₁ + 1/n₂ = 1` (`newHit_exact`) |

## 5. Exact coefficient compiler statement

With `D = lcm_r m_r`, `cof r = D/m_r`, `Z_ℓ = { E ⊆ I_ℓ : ℓ ∣ ∑_{r∈E} cof r }`,
`w_ℓ(E) = (∑_{r∈E} cof r)/ℓ`, and `T` with `D(1 − S) = T`:

```
(∃ sel, (∀ ℓ ∈ bands, sel ℓ ∈ Z_ℓ) ∧ S + ∑_ℓ ∑_{r ∈ sel ℓ} 1/(m_r ℓ) = 1)
  ↔  ∃ f, (∀ ℓ ∈ bands, f ℓ ∈ w_ℓ(Z_ℓ)) ∧ ∑_ℓ f ℓ = T.
```

## 6. Exact mobility statements

```
den(S_y) ∣ D_core,        T_y = T_* − ∑_{i∈y} D/n_i,
#targets = 2^H,           #(targets + targets) = 3^H,
W y + W z = 2 W w  ⇒  y = z = w,
gcd { D/n_i } = D/G   (G = ∏ n_i),
(∃ y, ∃ neutral terminal choice, S_y + Δ = 1) ↔ T_* ∈ F + M_Z.
```

## 7. All OPEN analytic owners

`AsymptoticUniformRowFibres`, `AntiHoleBridge`, `CentralityToBoundedTilt`,
`SparseResonanceArcBudget`, `CentralLobeBudget`, `RemainingSpectrumBudget`,
`CompatibleActualBaseline`, `CentralCompatibleActualBaseline`, and the inherited V2 owners
`FixedPowerCoupledSupply`, `UniformNegativeCapacity`, `UniformLevel2Rejection`. All uninhabited.

## 8. Retractions / firewalls recorded

* per-row multiplier neutrality is **not** necessary (`exists_globalNeutral_not_rowwiseNeutral`);
* “many packets ⇒ target hit” retired (`manyNeutralPackets_not_exactTarget`);
* “gcd 1 ⇒ target hit” retired (the gcd theorem is about the integer span; patterns overlap and
  subtraction is used);
* “many movable targets ⇒ long AP” retired (`no_three_term_ap`);
* “support huge ⇒ target hit”, “mass bracket contains target ⇒ exact hit”, “global CLT ⇒ local
  exact positivity” are not banked in any form;
* the §B certificate is terminal arithmetic only: no background word, no counterexample, no
  frontier extension.

## 9. Dependency DAG

```
Anchored V2 (frozen)  ──UnitSubsetSum──►  ColumnLattice
        │
        ▼
GlobalNeutrality      ColumnZeroPatterns ──► GlobalColumnCompiler ──┐
        │                                                           │
OldEmptyNewHit        ColumnPackets      SupportMultiplicity        │
                                                                    ▼
TargetMobility     MobilityStructure ─────────────────────► AlignmentPolynomial
                                                                    │
FourierHitInterface ──► ResonanceInterfaces      BaselineCentrality │
        └───────────────────┴───────────────┬────────────────────────┘
                                            ▼
                                    ConditionalClosure
                                            ▼
                          OpenOwners ──► Reconciliation ──► AxiomAudit
                                            ▼
                                    AnchoredV3 (aggregator) ──► Main
```

## 10. Axiom audit output

`AxiomAudit.lean` runs `#print axioms` on all 52 principal V3 theorems. Every report is one of

```
[propext, Classical.choice, Quot.sound]
[propext, Quot.sound]                       (e.g. globalNeutral_of_rowwiseNeutral,
                                             no00_preserved, notMem_activeRows_iff,
                                             activeRows_private_prime)
```

No `sorryAx`, no custom axiom, no `Lean.ofReduceBool`/`Lean.trustCompiler`. The two `decide`
calls (in `sharpness_witness_two` and `manyNeutralPackets_not_exactTarget`) are kernel-reducible
and introduce no axiom dependency. A repository-wide search confirms no `sorry`, `admit`,
`native_decide`, `unsafe`, `opaque` or `@[implemented_by]` occurs anywhere in the V3 layer.

## 11. Build / validation

* `lake build RequestProject.Erdos287.AnchoredV3` — succeeds (all 17 V3 modules plus the
  aggregator), warnings only (three declared-but-unused hypotheses in
  `conditional_terminal_closure`, which are the compatibility / centrality / bounded-tilt inputs
  required by the specified statement shape).
* `lake build` (all default targets, including `RequestProject/Main.lean` with the new import) —
  **succeeds**: `Build completed successfully (8566 jobs)`, no errors.
* V2 build and V2 theorem names are unchanged; the only edit outside `AnchoredV3/` is the single
  new import line in `RequestProject/Main.lean`.
* Certified finite frontier `67108856338751594`: unchanged, U2 still pending; no V3 statement
  touches it.
* No external Python/JSON output is used as proof authority; every numeric certificate in §B is
  re-proved by Lean arithmetic.
* No independent external kernel checker beyond Lean's own kernel was available in this
  environment; this does not affect the results above.

## FINAL VERDICT

```
BANKED_ANCHORED_V3_GLOBAL_TERMINAL_MOBILITY
```

Erdős #287: **OPEN**. Not solved, no counterexample, no route closed, no frontier extension.
