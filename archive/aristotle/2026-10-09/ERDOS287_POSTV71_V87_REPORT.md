# Erdős #287 — post-V71 → V87 bank: kernel-checked firewall report

**Verdict: Erdős #287 is NOT solved. It remains OPEN.** Nothing in this subtree proves it, and
the closure DAG checks this formally (`DAG.dag_erdos287_open`, `DAG.dag_erdos287_open_support`).

Subtree: `RequestProject/Erdos287/PostV71V87/` · namespace `Erdos287.PostV71V87` ·
aggregator `RequestProject/Erdos287/PostV71V87.lean`.

**Source caveat.** No V83–V87 source documents are in the repository. Every statement below
was rebuilt from the mathematical descriptions in the task text (the Astra-repaired V87
reading). Where the text gave no complete proof, the claim is kept as an explicit provider or
marked OPEN. Nothing was reconstructed from a theorem's name alone.

---

## 1. Files added

| File | Content |
|---|---|
| `PostV71V87/Model.lean` | exact counterexample model: `Word`, `ExactWord`, `x`, `D = M - a`, `v`, `maxVal`, `P`, `Q`, `layer`, `carrier`, `Absent`, `row`, `selRow`, `Active`, `qstar`; equivalence with `Erdos287Counterexample`; `ValuationSurrogate` (kept separate from exact mass) |
| `PostV71V87/Positional.lean` | V84/V85 positional bank |
| `PostV71V87/EndpointCRT.lean` | V86 endpoint-anchored CRT bank |
| `PostV71V87/MinorRepair.lean` | V83 repair (RETIRED route) |
| `PostV71V87/AnalyticProviders.lean` | V84/V85 analytic providers and their conditional consequences |
| `PostV71V87/ReciprocalImage.lean` | `recipImage`, `Srec`, smooth/rough block decomposition |
| `PostV71V87/AnalyticToolkit.lean` | Chebyshev upper bound (imported from Mathlib), elementary lower bound for `π` |
| `PostV71V87/ReciprocalImageBound.lean` | `log S_rec(H) ≪ H log log H / log H` (proved) |
| `PostV71V87/ShellFingerprint.lean` | all-base shell fingerprint, entropy core |
| `PostV71V87/EntropyInversion.lean` | entropy inequality |
| `PostV71V87/RecurrenceGrowth.lean` | `gRec L = L log L / log log L` |
| `PostV71V87/RepairedRecurrence.lean` | entropy inversion and the repaired V87 recurrence theorem |
| `PostV71V87/Physical.lean` | internal `q_*`-multiples, guard triples, carrier reserve, overlap, carrier union |
| `PostV71V87/Firewalls.lean` | three-zone high-shell picture, terminal-window firewall, open frontier interfaces |
| `PostV71V87/RegressionFixtures.lean` | negative / hostile regressions |
| `PostV71V87/ClosureDAG.lean` | machine-checked dependency DAG with statuses |
| `PostV71V87/AxiomAudit.lean` | `#assert_std_axioms` on every principal theorem, `#print axioms`, `#audit_providers` |
| `PostV71V87/audit.sh` | source scan, historical-file check, narrow build, three negative controls |
| `PostV71V87.lean` | aggregator |
| `ERDOS287_POSTV71_V87_REPORT.md` | this report |

## 2. Files modified

**None.** `git diff --name-only <initial commit>` lists only the new files above. `PostV64V71/`,
`PostV64V71.lean` and `ARISTOTLE_SUMMARY.md` are unchanged; `audit.sh` §2 checks this. The
lakefile glob `RequestProject.+` picks up the new modules, so no build configuration had to
change.

## 3. Unconditional Lean theorems (status PROVED; axioms only `propext`, `Classical.choice`, `Quot.sound`)

Notation: `W : Word` or `W : ExactWord`, `D = W.M - W.a`, `Q p = p^(1+maxVal p)`,
`P p = p^maxVal p`, `q_* = W.qstar = min_p Q p`.

**Model (§2)**
* `ExactWord.toCounterexample (ha : 1 < W.a) : Erdos287Counterexample W.A`, with
  `ofCounterexample` and `ofCounterexample_one_lt_a` for the converse. So "an exact word with
  `a > 1`" means exactly "a #287 counterexample".
* `exact_implies_surrogate`: exact mass gives every valuation surrogate. The converse fails
  (`reg_surrogate_not_exact`).
* `Word.forced_omitted`, `Word.neighbours_of_omitted`, `Word.guard_pattern` (gap-two), and
  `Word.active_of_lt_qstar`: every prime `p < q_*` is active.

**V83 (RETIRED route; the algebra is proved)**
* `MinorData.actual_sub_target : m.actual S - m.target = m.B * (S - 1)`, i.e. `C_R − D_R = B_R(S−1)`.
* `MinorData.den_actual : (m.actual S).den = S.den / Nat.gcd S.den m.B.natAbs`.
* `MinorData.actual_integral_iff : (m.actual S).den = 1 ↔ (S.den : ℤ) ∣ m.B`, and
  `target_integral` (the target-one quantity is always an integer).
* `fixed_depth_compression`: a finite family of minor tests is equivalent to
  `(S.den : ℤ) ∣ F.gcd B`.
* `fixed_depth_not_exact_mass`: `{1,2,3,6}` passes every test at every depth but has mass 2.
* `integer_det_integral`: the determinant of an integer matrix, viewed in `ℚ`, is an integer.
  An actual principal minor is never "non-integral".

**V84/V85 positional**
* `ExactWord.two_le_layer_card`: an active top layer has at least 2 elements.
* `ExactWord.not_active_of_lt_two_mul (hℓ : ℓ.Prime) (h : W.M < 2ℓ) : ¬ W.Active ℓ` (singleton rejection).
* `ExactWord.conditioned_row_rejection`: if every selected element of valuation `k ≥ 1` lies in
  a set of size `≤ 1`, then `maxVal p ≠ k`.
* `ExactWord.positional_chain`: absent modulus `d`, `d ∣ y` in the window, and a neighbour of
  `y` that is a prime `ℓ` with `M < 2ℓ` together give `False` (absent modulus → forced
  omission → forced neighbours → singleton rejection).
* `ExactWord.Q_two_le_D (ha : 1 < W.a) : W.Q 2 ≤ W.D`.

**V86 endpoint-anchored CRT (high priority)**
* `Word.endpoint_anchored_crt (hcop : d.Coprime e) (hd : 2 ≤ d) (he : 2 ≤ e) (absent d, e) :
  W.M < d*e ∨ (W.M - W.a < d*e ∧ d*e < 2*W.a)`. All endpoint cases are covered: both
  oriented contacts come from `exists_contact` and `contact_reflect`.
* `Word.Q_mul_Q_gt_D : p ≠ r primes → W.D < W.Q p * W.Q r`.
* `Word.card_small_ceilings_le_one : #{p prime : Q_p² ≤ D} ≤ 1` (inside any finite set), i.e.
  `#{p : Q_p ≤ √(M−a)} ≤ 1`.
* `Word.low_start_chamber (3a ≤ M+1) : W.M < d*e`; `Word.Q_pair_annulus`;
  `ExactWord.dyadic_two_sided_saturation` (a `Q_2`-multiple exists inside the window, and every
  `Q_2`-multiple in the window carries the pattern `(1,0,1)`); `ExactWord.ceiling_annulus`
  (non-exceptional: `D < Q_p²` and `Q_p ≤ p·M`).
* Guard owner-disjointness: `Word.large_prime_unique_multiple` (for `ℓ > D` there is at most
  one multiple in the window), `Word.owner_disjoint` (`M < ℓℓ'` gives disjoint selected
  rows), `Word.guard_triple_owner_unique`.

**V87 reciprocal image / minimal grid**
* `Srec_block_bound : Srec H ≤ (H·H^{π(y)} + 1) · 2^{∑_{y<p≤H} ⌊H/p⌋}` (smooth / large-prime blocks).
* `log_Srec_le : ∃ C H0, 0 < C ∧ ∀ H ≥ H0, log S_rec(H) ≤ C·H·log log H / log H`. **Proved**;
  the only analytic input is Mathlib's Chebyshev bound (§5).
* `ExactWord.shell_fingerprint (hp : p.Prime) (hlt : p < q_*) : Active p ∧ 2 ≤ |layer p| ∧
  (p:ℤ) ∣ (sigma p).num`: the maximal layer is active, and its reciprocal cofactor sum has
  reduced numerator divisible by `p`.
* `ExactWord.entropy_core`, `entropy_inequality`, `entropy_inversion`.
* **`repaired_recurrence : ∃ c > 0, ∃ M0, ∀ W : ExactWord, 1 < W.a → M0 ≤ W.M →
  c · gRec(log D) ≤ D / q_*`**, where `gRec L = L·log L / log log L`. This is
  `(M−a)/q_* ≫ log(M−a)·log₂(M−a)/log₃(M−a)` with an absolute constant. It does not depend on
  V85's `δ₀` or on any provider.

**Physical consequences**
* `Word.card_internalMultiples_ge : D / d ≤ #(internal d-multiples) + 1`.
* `Word.guard_at_internal_qstar`: `(x_{y−1}, x_y, x_{y+1}) = (1,0,1)` at every internal `q_*`-multiple.
* `Word.exists_disjoint_guard_family`, `many_disjoint_guards`: pairwise-disjoint guard triples,
  `c · gRec(log D) ≤ #Y + 2`.
* `Word.carrier_reserve (p prime, p² ≤ D, p non-exceptional) : p ≤ P_p ∧ D < P_p⁴`. This is
  `P_p > D^{1/4}` with `P_p ≥ p`, not the strict inequality. It needs **no** largeness
  condition beyond `p² ≤ D`.
* `Word.carrier_overlap_le_four (M⁴ < (D+1)⁵)`: each element lies in at most 4 reserve carriers.
  `ExactWord.overlap_condition` gives `M⁴ < (D+1)⁵` for `a > 1`, `M ≥ 34`.
* `ExactWord.carrier_union_lower (a > 1, M ≥ 34) : #reservePrimes ≤ 2·|⋃ carriers|`.

**Firewalls / fixtures / DAG**
* `highShell_trivial : HighShellExtinction (fun M => M/2) 0` (shells above `⌊M/2⌋` are empty),
  `zone_one_below_qstar`, `polylog_window_not_excluded`, `realisation_of_exact`,
  `crossScale_iff_tail`, all `reg_*` fixtures, and all `DAG.dag_*` invariants.

## 4. Conditional theorems and their providers (status CONDITIONAL)

Each provider is a `def … : Prop` and appears only as a hypothesis. None is inhabited
(`#audit_providers` checks this).

| Theorem | Provider (hypothesis) | Conclusion |
|---|---|---|
| `fixed_modulus_saturation` | `FixedModulusDyadicSupply` | for each fixed `K`, large words have no absent modulus `2 ≤ d ≤ K` |
| `fixed_base_primary_growth` | same | `K < Q_p` for all primes `p`, large words |
| `qstar_tendsto_of_fixed` | same | `K < q_*` for large words |
| `uniform_modulus_saturation` | `UniformDyadicSupply f` | every absent modulus `d ≥ 2` has `f(M) < d` |
| `growing_base_primary_growth` | same | `f(M) < Q_p` for all `p` |
| `qstar_gt_of_uniform` | same | `f(M) < q_*` |
| `maximal_carrier_of_uniform` | same | `f(M) < p·P_p`, carriers divisible by `P_p`, and `≥ 2` carriers when active |
| `highShell_some_empty_row` | `HighShellExtinction X0 ε`, `ε < 1` | every shell above `X0(M)` has an empty prime row |
| `tail_closure_of_crossScale` | `CrossScaleSynchronization287 M0` | every counterexample has `max A < M0` |
| `erdos287_of_crossScale_and_finite` | `CrossScaleSynchronization287 M0` and `FiniteExclusionBelow M0` | `¬ Erdos287Counterexample A` |
| `nearbyTransition_implies_proximity` | `NearbyTransition287` (fictitious) | `Proximity287` |

Provider definitions:
* `FixedModulusDyadicSupply`: for every `q ≥ 1` there is `X0(q)` such that every `X ≥ X0(q)` has
  a prime `ℓ ≡ 1 (mod q)` with `X < 2ℓ`, `ℓ < X`. Pointwise in `q`; this follows from the PNT in
  arithmetic progressions.
* `UniformDyadicSupply f`: one threshold `X0` that works for all moduli `q ≤ f(X)`. The
  uniformity is stated explicitly and is **not** derivable from the fixed version
  (`reg_pointwise_not_uniform`).

## 5. Imported external formal theorems

All are from Mathlib (pinned commit) and match their use exactly:
* `Chebyshev.eventually_primeCounting_le` (wrapped as `chebyshev_upper`, `π(x) ≤ (log 4 + 1)·x/log x` eventually). This is the prime-counting upper bound behind `log_Srec_le`.
* `Nat.exists_prime_lt_and_le_two_mul` (Bertrand), used in `dyadic_supply_modulus_one` (the only
  exact formal instance of the dyadic supply, modulus 1) and in `shellPrimeCount_pos`.
* `Nat.four_pow_le_two_mul_self_mul_centralBinom` (for `primeCounting_lower`), `Real.log_le_rpow_div`,
  `RingHom.map_det`.

Project-internal (historical, imported unchanged): `Erdos287Counterexample`
(`ProblemStatement.lean`) and `topExp`, `topLayer`, `topLayer_congruence` (`TopLayer.lean`).

No formal PNT in arithmetic progressions with the required effective or uniform dyadic form is
available in Mathlib or in the project, so V84/V85 supply stays a provider.

## 6. Missing analytic formalisations

* Dyadic prime supply in residue classes `1 mod q`: fixed modulus (`FixedModulusDyadicSupply`)
  and uniform in `q ≤ f(X)` (`UniformDyadicSupply f`).
* The high-shell extinction estimate at non-trivial thresholds (`HighShellExtinction X0 ε`).
* The V86 aggregate rough-part estimate. No complete proof was supplied, so it has **no formal
  statement** and is the OPEN DAG node `roughPartAggregate` (`decl = none`).

## 7. RETIRED claims

* The V83 fixed-depth complement-minor hierarchy as a closure route (DAG node
  `minorRouteClosure`). Its algebra is proved (§3). Fixed-depth tests reduce to
  `den(S) ∣ gcd B_R`, which `S = 2` satisfies (`fixed_depth_tests_pass_at_two`), so they cannot
  force `S = 1`. `DAG.dag_no_retired_use` checks that no exact or conditional node depends on it.

## 8. OPEN claims

* `Proximity287`: for some `K ≥ 2`, in all large words at most half the primes in `(q_*, K q_*]`
  are active.
* `CrossScaleSynchronization287 M0`: no exact word with `M ≥ M0` realises `CrossScaleRealisation`
  (guard triples at `q_*`, all rows active below `q_*` with fingerprint, the carrier reserve,
  empty high shells, all carry digits, exact mass).
  **Exposure:** `realisation_of_exact` proves that every exact word realises the package. So
  `crossScale_iff_tail` shows the interface is *equivalent* to "no counterexample with `M ≥ M0`":
  as stated it is exactly the tail of #287, not a weaker intermediate statement.
* `IntermediateScaleControl287` (zone 3: scales between `q_*` and `X0(M)`).
* `FiniteExclusionBelow M0`.
* The providers in §4/§6 and `roughPartAggregate`.
* `NearbyTransition287` is a deliberately fictitious provider. It implies `Proximity287`, and
  nothing assumes it.
* **Erdős #287** itself.

**Three-zone picture** (`Firewalls.lean`):
1. Below `q_*`, every prime row is active and fingerprinted (PROVED, `zone_one_below_qstar`).
2. In high shells, total emptiness above `⌊M/2⌋` is PROVED (`highShell_trivial`). "Almost all
   rows empty" above `X0(M)` is CONDITIONAL on `HighShellExtinction`.
3. Intermediate scales are OPEN. Nothing claims emptiness just above `q_*` or a sharp transition
   at `q_*`. `reg_active_above_qstar` gives a gap-two word with `q_* = 3` and an active prime
   row at `5 ∈ (q_*, 2q_*]`.

**Terminal-window firewall:** `polylog_window_not_excluded` shows that for every `c > 0` and
`B ≥ 2`, the recurrence conclusion `c·gRec(log D) ≤ D/q` holds automatically whenever
`q ≤ D/(log D)^B` and `D` is large. So the recurrence theorem alone does **not** exclude
`M/(log M)^B < q_* ≪ M/T(M)`, and not every polylogarithmic terminal regime is closed.

## 9. Axiom audit

* `AxiomAudit.lean` runs `#assert_std_axioms` on 73 principal declarations. The build fails if
  any of them depends on an axiom other than `propext`, `Classical.choice`, `Quot.sound`.
  `sorryAx` and `Lean.ofReduceBool` (`native_decide`) are therefore rejected. All 73 pass.
* `#print axioms` for `repaired_recurrence`, `log_Srec_le`, `Word.endpoint_anchored_crt`,
  `ExactWord.shell_fingerprint`, `many_disjoint_guards`, `ExactWord.carrier_union_lower` and
  `tail_closure_of_crossScale` each prints `[propext, Classical.choice, Quot.sound]`.
* Provider-construction audit: `#audit_providers` scans every declaration in the namespace whose
  statement concludes a provider proposition. It fails if such a declaration has no `Prop`
  hypothesis, apart from the single whitelisted trivial instance `highShell_trivial`. Result:
  it passes. The only provider-concluding declarations are `highShell_trivial` (whitelisted),
  `nearbyTransition_implies_proximity` and `proximity_not_from_trivial_highShell`, which both
  take a hypothesis.
* Negative controls in `audit.sh`. Each one must be rejected, and each is: a `sorry` theorem
  (fails on `sorryAx`), a `native_decide` theorem (fails on `Lean.ofReduceBool`), and a
  provider built without hypotheses (`FiniteExclusionBelow 0`, rejected by `#audit_providers`).
  The source scanner also self-tests on a planted `sorry`.
* Source scan, with comments and docstrings stripped: no `sorry`, `admit`, `axiom`, `unsafe`,
  `native_decide`, `implemented_by`, `opaque`, `extern` or `Inhabited` anywhere in the subtree.
* DAG invariants are checked by `decide` (kernel evaluation), not `native_decide`.
* Note on vacuous instances: some provider families have trivially true degenerate parameter
  values (for example `FiniteExclusionBelow 0`, or `UniformDyadicSupply 0`). These are never
  stated or used as theorems, and the conditional results are only meaningful for
  non-degenerate parameters.

## 10. Build results

* Narrow build: `lake build RequestProject.Erdos287.PostV71V87` succeeded (8047 jobs).
* `bash RequestProject/Erdos287/PostV71V87/audit.sh` printed `AUDIT PASSED`.
* `lake env leanchecker RequestProject.Erdos287.PostV71V87 <all 17 subtree modules>` exited 0 (12 min 45 s).
* `lake env leanchecker --fresh RequestProject.Erdos287.PostV71V87` exited 0 (39 min 38 s;
  replays the whole import closure, including Mathlib, from scratch).
* Full `lake build` (default target, all `RequestProject.+` modules): **succeeded** — `Build completed successfully (8977 jobs)`, no errors.

## 11. First current mathematical theorem that is still open

`Proximity287` and `CrossScaleSynchronization287` are the two frontier interfaces.
`CrossScaleSynchronization287 M0` is provably equivalent to the tail of #287
(`crossScale_iff_tail`). So the first genuinely intermediate open statement is
**`Proximity287`**: substantial empty-row information in `(q_*, K q_*]`. On its own it does not
yet imply #287, and an exact cross-scale synchronization argument would still be needed.

## 12. Dependency graph to Erdős #287

`ClosureDAG.lean` records this graph and kernel-checks it. `support erdos287` contains exactly
the open nodes `erdos287, crossScaleSync, finiteExclusion, proximity, intermediateScales`.

```
erdos287 (OPEN, no Lean decl)
├── erdos287ConditionalOnSync (CONDITIONAL: erdos287_of_crossScale_and_finite)
│   ├── tailClosure (CONDITIONAL: tail_closure_of_crossScale)
│   │   ├── crossScaleSync (OPEN: CrossScaleSynchronization287)
│   │   ├── counterexampleEquiv (EXACT) ── exactWordModel
│   │   ├── disjointGuards (EXACT: many_disjoint_guards)
│   │   │   ├── guardPattern ── positionalChain ── singletonRejection ── topLayerTwo
│   │   │   ├── internalMultiples
│   │   │   └── repairedRecurrence (EXACT)
│   │   │       ├── logSrecBound ── srecBlockBound, chebyshevImported (Mathlib)
│   │   │       ├── entropyInequality ── shellFingerprint ── topLayerTwo
│   │   │       └── entropyInversion
│   │   ├── shellFingerprint (EXACT)
│   │   ├── carrierReserve (EXACT) ── qPairBound ── endpointCRT, ceilingAnnulus
│   │   └── highShellTrivial (EXACT)
│   └── finiteExclusion (OPEN: FiniteExclusionBelow)
├── proximity (OPEN: Proximity287)
└── intermediateScales (OPEN: IntermediateScaleControl287)

side branches (not on the #287 path):
  providerFixedSupply (OPEN) → fixedModulusSaturation → fixedBaseGrowth          (CONDITIONAL)
  providerUniformSupply (OPEN) → uniformModulusSaturation → growingBaseGrowth
                                 → maximalCarrierUniform                          (CONDITIONAL)
  providerHighShell (OPEN) → highShellEmptyRow                                    (CONDITIONAL)
  roughPartAggregate (OPEN, no formal statement) ← qPairBound, ownerDisjoint
  minorRouteClosure (RETIRED) ← fixedDepthCompression, fixedDepthNotExact
  nearbyTransition (OPEN, fictitious; only shown to imply proximity)
  polylogWindowFirewall (EXACT) ← repairedRecurrence
```

**Final verdict: Erdős #287 remains OPEN.** This branch gives a kernel-checked firewall for the
audited V83–V87 bank and a formal boundary around the Proximity / cross-scale synchronization
frontier. It does not prove #287.
