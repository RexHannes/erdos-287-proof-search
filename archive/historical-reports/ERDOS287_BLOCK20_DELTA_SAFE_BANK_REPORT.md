# ERDŐS #287 — BLOCK20 Δ SAFE BANK — REPORT

Append-only addition to the frozen Balanced7 hostile-audit bank. No historical file was
modified; `RequestProject/Main.lean` received import lines only.

## Files added

| File | Sections |
|---|---|
| `RequestProject/CurrentProgramme/FixedCertificateBalancedSevenSourceSeal.lean` | §2, §2A–§2D |
| `RequestProject/CurrentProgramme/Block20PackingCompiler.lean` | §3, §4, §5 |
| `RequestProject/CurrentProgramme/Block20LargePrimePowerRouter.lean` | §6 |
| `RequestProject/CurrentProgramme/Block20GeneratedBilinearCompiler.lean` | §7–§11, §13, §14 |
| `RequestProject/CurrentProgramme/PerronConditionRemovalCompiler.lean` | §12, §12A |
| `RequestProject/CurrentProgramme/ExceptionalMainTermComparisonAdapter.lean` | §15 |
| `RequestProject/Status/CurrentStatusErdos287Block20.lean` | §16 |
| `RequestProject/Status/AxiomAuditErdos287Block20.lean` | §17 |

## §2 — Source-seal repair (attempted, partially successful)

Started at the *actual* repository fixed-certificate object
`Erdos287.SmoothParity.FixedCertificateSmoothParityPacket`, not at a model object.

Proved:

* `fixedCertificate_k0_Jempty_reduction`, `fixedCertificate_smoothCut_reduction` — the
  `k = 0`, `J = ∅`, `P⁺(n) ≤ n^σ_*` reduction to the truncated Möbius sum
  `∑_{e ∣ n, e ≤ n^(1/2 − ε_*)} μ(e)`;
* `fixedCertificate_sevenBox_eq_neg20` — the finite seven-box identity `H_*(P) = −20`,
  routed through the repository definitions rather than re-proved abstractly;
* `fixedCertificate_sevenBox_depth_metadata`;
* weight dictionary: `omegaBox_dictionary`, `omegaBox_dictionary_negative_twist`, together
  with the exclusion theorems `omegaBox_carries_no_vonMangoldt_factor`,
  `omegaBox_carries_no_log_factor`, `omegaBox_carries_no_inverse_log_factor`; the affine
  `log r` from `Λ = μ * log` is kept separate as `vonMangoldt_sum_divisors_eq_log`;
* `balancedSevenSeal_of_cellIdentity` — the seal `BalancedSevenSP2SourceSeal` follows from a
  *single* remaining hypothesis.

The seal is **not** inhabited. The exact residual is

    Erdos287.Block20.FixedCertificateSP2PacketMatchesCompilerPacket

(the `cell_identity` field: identification of the literal repository fixed-certificate SP-2
packet with the packet consumed by the Balanced7 compiler). Refutation of automaticity:
`sourceSeal_residual_not_automatic`; ledger honesty: `sourceSeal_status_is_open`.

## §3–§5 — Ledger, packing, source split

* `ν₀ = 16623/100000` exactly (`nu0Q_value`, and `nu0Q_ne_one_sixth`: ν₀ ≠ 1/6);
  `σ_* = ν₀ − 2ε_*`; `sigmaStar_ge : σ_* ≥ 0.1629054`; `nineteen_blocks_overflow :
  19·(σ_*/3) > 1`; `eps_one_over_600_not_admissible`.
* `nonfinal_block_count_le_18`, hence total block count ≤ 20.
* Procedural greedy packing: `bigAtoms` / `smallAtoms` / `groupSmall` / `packSide` /
  `packBoth`, with `packSide_perm` (every atom assigned exactly once — no loss, no
  duplication), deterministic singleton vs grouped provenance, no d/m straddling, every
  non-final block mass ≥ σ_*/3, every block mass ≤ σ_*, ≤ 2 leftovers globally.
  `Block20PackingValidity` is a separate contract and is inhabited **constructively** by
  `packBoth_validity`; `block20Validity_not_automatic` shows it is not vacuous.
* Smooth/rough split at `z₀ = X^(1/420)`: `block20_gcd_smooth_rough` (`gcd(d,m)=1`),
  `bigOmega_rough_le_420`.
* Truncated Möbius: `truncMobius_coprime_split` and `truncMobius_gamma_split`, the exact
  finite divisor factorisation `e = e_d·e_m`.

## §6 — Large prime-power router

Sector definition and finite routing partition proved; the analytic estimate is an
uninhabited input `LargePrimePowerRouterEstimateInput` with a proved conditional consumer to
`LargePrimePowerSectorNegligible` and a `*_not_automatic` refutation.

## §7–§11, §13, §14 — Templates, window, bilinear split, grammar, ledger

`Block20Template` carries only finite metadata (block IDs, d/m label, provenance, ordered
support cells, selected subset `E`, sign `s`, routing state, order). Proved:
`template_block_count_le_20`, `template_selection_not_recomputed` (E is template-fixed),
`typeII_window_from_first_crossing` (`ε_* ≤ selectedMass < ε_* + σ_* = ν₀ − ε_*`),
`typeII_size_window`, `template_product_split` (`∏ all = u·v`), `template_predicate_split`,
`template_mass_split`, `fixed_template_source_factorisation` (`ξ_π(u)·κ_π(v)` after the
external inputs are supplied), and the exposed joint residual
`joint_coprimality_predicate_not_factorisable`. Coefficients `generatedXi` / `generatedKappa`
are defined from the packed block grammar (`mobius_factor_occurs_once`,
`ordered_block_convolution`); the divisor-norm bounds are the uninhabited
`GeneratedCoefficientNormInput`, proved to attach to the generated class.
`Block20GeneratedTypeIIInput` is uninhabited; `k0_uniform_fragmentation_compiler` is the
conditional compiler to `K0UniformFragmentationConclusion` (not inhabited).
`CompilerLogBudget` with `total_eq_sum_of_fields`, `currentCrudeBudget_total = 22`, and
`crude_budget_is_not_an_optimality_theorem`.

## §12/§12A, §15 — Perron and effectivity sockets

`PerronConditionRemovalInput` is granular (source cutoff, truncated integral representation,
kernel `K(τ)`, vertical range, kernel L¹ budget, boundary-strip source and estimate,
truncation error, exact reconstruction) with conditional compiler to
`SeparatedPrefixCoefficientFamily`; `C_Perron = 1` is recorded as external audit metadata.
`PerronBoundaryRouterInput` plus the firewall theorems
`boundaryRouter_preserves_literal_source` and `smoothed_certificate_is_a_different_source`.
`ExceptionalMainTermComparisonAdapter` is uninhabited with all three routes left undecided
(`exceptionalRoute_not_decided`, `effective_route_is_not_chosen`) and a conditional compiler
to `EffectiveSmallQLowConductorConclusion`.

## Final block

    PREVIOUS BALANCED7 HOSTILE-AUDIT BANK:
        PRESERVED (no historical file modified; Main.lean imports only).

    BALANCED7 SOURCE SEAL:
        SOURCE_OPEN (seal derived from one residual; not inhabited).

    EXACT SOURCE-SEAL RESIDUAL IF OPEN:
        Erdos287.Block20.FixedCertificateSP2PacketMatchesCompilerPacket
        (the cell_identity field).

    BLOCK20 ARITHMETIC:
        PROVED — nu0 = 16623/100000 exact, sigma_* >= 0.1629054,
        19*(sigma_*/3) > 1, eps_* = 1/600 inadmissible.

    BLOCK20 GREEDY PACKING:
        PROVED FINITE / CONSTRUCTIVE (packBoth_validity).

    BLOCK COUNT:
        <= 20 (nonfinal <= 18 plus <= 2 leftovers).

    d/m ALIGNMENT:
        PROVED — no block straddles the d/m boundary; gcd(d,m) = 1.

    TRUNCATED-MOBIUS SPLIT:
        PROVED ALGEBRAIC (truncMobius_gamma_split).

    BLOCK20 SOURCE COMPILER:
        PROVED FINITE (bilinear split), with the joint coprimality
        predicate exposed as an explicit residual.

    BLOCK20 TYPE-II WINDOW:
        PROVED FINITE; log-mass -> X-power conversion is an explicit input.

    THREE-SMALL-PRIME:
        SUPERSESSION CANDIDATE / SOURCE COVERAGE OPEN; NOT FALSE.

    PERRON CONDITION REMOVAL:
        ANALYTIC INPUT / UNINHABITED.

    PERRON BOUNDARY ROUTER:
        ANALYTIC INPUT / UNINHABITED.

    GENERATED TYPE-II:
        OPEN_ANALYTIC / FIRST MAIN-LINE RESIDUAL.

    UNIFORM k=0:
        CONDITIONAL (compiler proved, conclusion not inhabited).

    EFFECTIVE PNT PROVIDER:
        CONDITIONAL.

    EXCEPTIONAL COMPARISON ADAPTER:
        SOURCE_OPEN / UNINHABITED.

    BALANCED7 EFFECTIVE:
        OPEN.

    FCL:
        OPEN.

    ERDOS287:
        OPEN.

    FULL BUILD:
        lake build — 8235 jobs, 0 errors.
        (One pre-existing linter warning in the historical file
        RequestProject/Erdos287/FixedCertificateSmoothParity.lean:60.)

    TRUST:
        New files: zero sorry, zero admit, zero axiom, zero opaque,
        zero unsafe, zero native_decide, zero @[implemented_by].
        #print axioms over every principal new declaration yields only
        subsets of {propext, Classical.choice, Quot.sound}.

## FINAL FIREWALL

This formal layer certifies finite source algebra, deterministic Block20 packing, source
dependency graphs and conditional compilers only. It does **NOT** prove
`287-K0-SP2-BLOCK20-GENERATED-TYPEII45`, Perron analytic error estimates, the exceptional
comparison adapter, FCL, or Erdős #287.
