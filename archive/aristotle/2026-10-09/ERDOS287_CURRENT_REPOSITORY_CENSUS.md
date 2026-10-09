# Erdős #287 — current repository census (tail consolidation)

**Erdős #287 is still open. The asymptotic-tail theorem (TAIL-287) is NOT BANKED.**

Scope: the census lists what the repository contains *now*, which parts the new
`CurrentTail` subtree reuses, and which mathematics exists only in prose (reports or the
request) — that material is marked `UNFORMALISED_SOURCE`.

"Builds?" was checked in this session:

* `lake build RequestProject.Erdos287.W3Publication RequestProject.Erdos287.W2984Publication RequestProject.Erdos287.PostV87V90R`
  succeeded (8073 jobs).
* `lake build RequestProject.Erdos287.CurrentTail` succeeded.
* The full `lake build` succeeded (9020 jobs), so every module listed as existing builds.

Search method: the census is based on the files themselves (`rg` over `RequestProject/**.lean`
and Mathlib), not on file names or prose. A declaration is listed only if it compiles.

## A. Packages reused by `CurrentTail`

| Module | Exists? | Builds? | Exact theorems | External assumptions | Current role |
|---|---|---|---|---|---|
| `Erdos287/PostV71V87/Model.lean` (exact #287 model) | yes | yes | `ExactWord`, `ofCounterexample`, `ofCounterexample_one_lt_a`; `counterexample_iff_exactWord` (`PostV87V90R/ModelCompatibility.lean`), `ofCounterexample_M` | none | exact #287 model; used by `tail_of_remainder_littleO` |
| `Erdos287/PostV87V90R/MomentConsumer.lean` | yes | yes | `moment_cauchy`, `exists_occupancy_of_moment`, `sharp_mean_consumer`, `qbal_le_pairs` | none | moment consumer used by the seven-block consumer |
| `Erdos287/PostV87V90R/ContactCycle.lean` | yes | yes | `alpha_contactCycle` (`α(ContactCycle r m) = m` for `1 ≤ m`, `2m ≤ r`), `exists_useful_edge` | none | gives `α(Γ_{7,2}) = 2` (`alpha_Gamma72`) |
| `Erdos287/PostV87V90R/AffineCompiler.lean` | yes | yes | `affine_adjacency`, `AffineContactCompiler` (data structure) | none (no compiler instance is built for `r = 7`) | affine compiler / contact identity |
| `Erdos287/PostV87V90R/RowRigidity.lean` | yes | yes | `selRow_empty_of_bounded_cofactors`, `adjacent_empty_rows_contradiction`, `ContactWitness.false` | none | bounded-cofactor row rigidity |
| `Erdos287/PostV87V90R/OccupancyContact.lean` | yes | yes | `false_of_edge`, `occupancy_contact_false`, `moment_contact_false` | none | occupancy → adjacent omission → contradiction |
| `Erdos287/W3Publication` (+ `Checkpoint.lean`) | yes | yes | `W3_of_provider`, `counterexample_form` (aliases of `PostV87V90R`) | `WidthThreeMomentProvider` (never constructed) | W3 checkpoint; imported read-only through its public interface |
| `Erdos287/W2984Publication` (10 files) | yes | yes | `pairConstant_lt`, `W2984`, `W2984_counterexample_form`, `chen_pointwise`, `merikoski_pointwise_fails`, … | `W3FrameworkProvider`, `AffineChenS1/S2/S3Provider`, `AffineChenSquareTailProvider` | W2.984 package; **not imported or modified** by `CurrentTail` (its status does not depend on the tail) |
| Mathlib `NumberTheory/DirichletCharacter/Orthogonality.lean` | yes | yes | `DirichletCharacter.sum_characters_eq`, `sum_char_inv_mul_char_eq` | none | character orthogonality exists, but Ordering B deliberately does **not** expand characters before Cauchy; not needed |

## B. Earlier #287 packages (preserved, not modified)

| Module | Exists? | Builds? | Exact theorems | External assumptions | Current role |
|---|---|---|---|---|---|
| `Erdos287/{Defs,TopLayer,Cnum,Window,Counterexample,PrimeFree,Blocker,…}.lean` (224 top-level files) | yes | yes (full build) | e.g. `topLayer_congruence`, `topLayer_card_ne_one`, `primePower_window_exclusion`, `blockerPair_contradiction` | per file (documented in earlier reports) | elementary structural bank |
| `Erdos287/PostV64V71`, `PostV71V87`, `PostV87V90R` | yes | yes (PostV87V90R checked here) | see `ERDOS287_POSTV87_V90R_REPORT.md` | named providers | post-V64 … V90R consumers |
| `Erdos287/ResearchBankV5 … V30`, `QSigma`, `PostQSigma`, `Anchored*`, `Direct` | yes | yes (full build) | see their reports | named providers / inputs (`OrdinaryBVProvider`, `SiegelWalfiszSeedInput`, `BDHEnergyProvider`, …) | historical research banks; none contains a *proved* SW/BV/BDH theorem |
| `RequestProject/{CurrentProgramme,Status,TrustedBank,HostileAudit,Audit,Challenges,Validation}` | yes | yes (full build) | status ledgers and audits | as documented | historical status and audit layers |

## C. Analytic-number-theory material (what really exists)

| Module | Exists? | Builds? | Exact theorems | External assumptions | Current role |
|---|---|---|---|---|---|
| Siegel–Walfisz (formal theorem) | **no** (only as hypotheses: `SiegelWalfiszSeedInput`, `BalancedSevenLowConductorSiegelWalfiszInput`, `SiegelWalfiszLogModuli287`) | — | — | — | `CurrentTail` uses its own narrow `SWCondition` / `BaseSWProvider` |
| Bombieri–Vinogradov (formal theorem) | **no** (only `OrdinaryBVProvider`, `GeneralizedBVInput`, … as inputs) | — | — | — | not needed by Ordering B |
| Barban–Davenport–Halberstam (formal theorem) | **no** (`BDHEnergyProvider` input in ResearchBankV25 only) | — | — | — | `CurrentTail.BDHStatement` is the smallest ordinary-BDH interface |
| Additive large sieve | **no** formal theorem (only `…LargeSieve…Input` structures) | — | — | — | not used |
| Dirichlet-character orthogonality | yes (Mathlib) | yes | see §A | none | not used (Ordering A retired) |
| CRT | yes (Mathlib `Nat.chineseRemainder`, `Nat.modEq_and_modEq_iff_modEq_mul`) | yes | — | none | used by `rbdh_crt_identity`, `crt_phase_split` |
| Divisor-weighted summation | partly (Mathlib `Nat.divisors`, `Finset.sum_comp`) | yes | — | none | used by `divisor_weight_transport`, `card_fibre_le` |
| Fourier / Poisson summation for progressions | no usable formal statement | — | — | — | only the length bookkeeping `dualLength_enlarged` is formalised |
| "OpenAI Math" Lean corpus (prime gaps, additive sieve) | **not present** in this sandbox or the repository | — | — | — | nothing imported; no API inferred from names |

## D. V95–V100 programme material

| Module | Exists? | Builds? | Exact theorems | External assumptions | Current role |
|---|---|---|---|---|---|
| PHLS / seven-block consumer (formal) | was **absent** before this session | — | — | — | now `CurrentTail/SevenBlockConsumer.lean` (new) |
| V95–V98 reports / papers (coloured `E₁/E₂`, quantitative `T_H^{7/128}`) | **no** file in the repository | — | — | — | `UNFORMALISED_SOURCE` |
| V99 exact relative centering | only the formula in the request | — | — | — | identity now kernel-proved (`v99_relative_centering`) |
| V100 Relative-BDH (and the Opus V100 LOCAL-REPAIR verdict) | **no** file in the repository | — | — | — | algebra now kernel-proved (`rbdh_crt_identity`, `RBDH_of_BDH`); the verdict is recorded only as reported in the request |
| Ordering-B Maynard reduction (the `E₁`/`E₂` source dictionaries) | **no** source text in the repository | — | — | — | `UNFORMALISED_SOURCE`; represented as `OrderingBSourceDictionary` (status `Candidate`) |
| Pascadi spectral theorem; Maynard Type-II theorem | not formalised anywhere | — | — | — | narrow providers `PascadiE2Printed`, `QuantitativeTH`, `MaynardE1Estimate` |

## E. New subtree (this session)

`RequestProject/Erdos287/CurrentTail/` (16 Lean files + `audit.sh`) and the aggregator
`RequestProject/Erdos287/CurrentTail.lean`. See `ERDOS287_CURRENT_TAIL_FORMAL_REPORT.md`.
