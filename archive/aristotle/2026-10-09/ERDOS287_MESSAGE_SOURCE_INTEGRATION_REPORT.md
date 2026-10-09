# Erdős #287 — message-level source integration report (V99–V100R4)

**Erdős #287 is still open. TAIL-287 is NOT BANKED.**
Labels: `V100R4_AuthorCandidate`, `IndependentTailAuditPending`,
`TAIL287_AUTHOR_CHAIN_COMPLETE` (author package claim), `TAIL287_INDEPENDENT_BANK_PENDING`.
These are metadata only. No Opus `PASS — PRE-EFFECTIVITY TAIL BANK` verdict has been supplied.

Provenance: `MESSAGE_LEVEL_SOURCE`, the formulas supplied in the conversation. Two items were
inferred from consistency with AB.2/AA.1 and are not quoted from the source: the Cauchy factor
`𝓑 = ML`, and the ledger split `1 + 2 + 7/128` behind `391/256`. The numeric constants of the
three Pascadi range inequalities were not supplied. They are carried as an explicit hypothesis
bundle (`PascadiRangeExport`).

Status labels used: `BANK_EXACT` (kernel-proved, no open input), `PAPER_VERIFIED_PARTIAL`
(source statement whose finite steps are proved), `EXTERNAL_ANALYTIC` (named analytic
provider), `REFEREE_PENDING` (inherited input awaiting independent audit), `TAIL_CONDITIONAL`.

All Lean files are under `RequestProject/Erdos287/SourceChain/`.

| Object | Source level | Lean status | Remaining provider |
|---|---|---|---|
| V99 exact relative centering | V99 text (CurrentTail) | `BANK_EXACT`: `v99_relative_centering`, `RSigmaP_eq_Rrel_add_Rpaid` (CurrentTail, unchanged) | `BaseSWProvider` (`REFEREE_PENDING` #1) |
| RBDH algebra | V100 | `BANK_EXACT`: `rbdh_crt_identity`, `rbdh_variance_contraction`, `crt_injOn`, `divisor_weight_transport` (CurrentTail) | divisor-weighted BDH bound |
| Ordering-B Type-II split | OB.1 | `BANK_EXACT`: `typeII_split`, `typeII_split_sum` (`TypeIISplit.lean`) | — |
| Family relative centering (second term → `Δ^{f,c m̄}_{α^{(r)}}(l, B·(Am)⁻¹)`) | OB.2 | `BANK_EXACT`: `secondTerm_eq_DeltaRel`; every inverse carries `a*a⁻¹ ≡ 1` (`affine_modEq_iff_of_inv`, `coprime_of_inv`) | — |
| Residue-fibre `1/f` density | OB.3 | `BANK_EXACT`: `residueFibre_card_le`, `residueFibre_density` | — |
| Ordering-B square `n₁ ≡ n₂ (fl)` | OB.5 | `BANK_EXACT`: `physical_pair_congr`, `orderingB_physical_square` (no characters used) | — |
| Zero mode covariance | OB.8 | `BANK_EXACT`: `zeroMode_covariance` (`1/(fl[r₁,r₂]) (1_{n₁≡n₂ (r₁,r₂)} − 1/φ((r₁,r₂)))`), `zeroMode_covariance_full`, `totient_lcm_mul_totient_gcd` | — |
| Model–model / Poisson remainder `𝒫_T(q,a)` | OB.6 | `BANK_EXACT`: `poissonP_scale`, `PF_scale`, `PF_rho_scale`, `lattice_discrepancy` (`|𝒫| ≤ Var Ψ`, sum side) | Fourier-side `|𝒫_T| ≤ V`, `Ψ̂` decay (`EXTERNAL_ANALYTIC`) |
| `F_AB` | OB.7, AB.1, AB.2 | `BANK_EXACT`: `rho_factor` (`ρ_k ≡ k ρ̃_k`), `rho_crt`, `poissonP_rho` (`𝒫_M(kq₀,ρ_k) = 𝒫_{M/k}(q₀,ρ̃_k)`), `FAB_eq_sum_PF`, `FAB_split`, `FAB_kgt1_count`, `AB2_cauchy`, `k1_modulus_exponent`; per cell `fabKgt1_cell_bound` | `τ/φ` moment, harmonic count, `|𝒫| ≤ V` |
| `F_AA` cleanup | OB.9, OB.10, AA.1 | `BANK_EXACT`: `FAAData`, `FAA_eq_sectors` (exact partition into commonR/commonN/diagonal/nearDiag/clean), `AA1_cauchy`, `nearDiag_cauchy`, `aaShape_cell_bound`, `nearDiag_cell_bound`; `(n₁,n₂)=1` **not** added: `commonN_empty_of_not_rough` | rough-support counts (`EXTERNAL_ANALYTIC`) |
| Clean `F_AA^♯` | OB.10, REC.1 | `BANK_EXACT`: `FAAsharp` (keeps `f, A, B, l, r₁, r₂, n₁, n₂`, CRT residue, coefficients, masks, Fourier variable, dyadic ranges), `clean_conditions`, `rec1_recombination` (`|∑Γ_ξ S_ξ| ≤ R_paid + ∑|Γ_ξ|√(𝓑_ξ|F^♯_ξ|)`, where `R_paid` is the explicit sum of the paid cells) | `SharpMembership` (`REFEREE_PENDING` #3/#4) |
| Full scalar weight | FW.1–FW.4, R1, R2 | `BANK_EXACT`: `scalarWeight_eq_sectors` (equality), `labelled_eq_canonical`, `canonical_gamma_one` (`γ(𝐃)=1`, disjoint grid only), `parity_sign_routing` (even → upper FL weight, odd → lower FL weight, then outer sign) | — |
| Low/high convolution | FW.5, FW.6 | `BANK_EXACT`: `coprime_low_high`, `lowHigh_unique`, `abs_Gamma1_le_one`, `sectors_Gamma1_bounded` | — |
| Range exporter | RG.1, R3 | `PAPER_VERIFIED_PARTIAL`: `Q1_absorb` (`Q₁ = bq₁`), `PascadiRangeExport.ineq2_holds` (inequality 2 **only** from `θN ≤ 1/3+δ`) | numeric constants of the three inequalities (not supplied) |
| Affine phase | PH.1 | `BANK_EXACT`: `ph1_phase`, `ph1_ePhase` (PH.1 verbatim, conditions `n₁ρ ≡ c (f)`, `An₁ρ ≡ An₂ρ ≡ B` kept; `A` not cancelled mod `f`; `(A,f)=1` not assumed), `affine_phase_decomposition`, `fixedLocal_split_phase` (`f = f₀f₁`) | — |
| `T_H` exponent | TH.1–TH.3 | `BANK_EXACT`: `exc_exponent_chain`, `th_exponent_propagation` (`7/32 → 7/64 → 7/128`), `QuantitativeTH_of_spectralY`, `TH_le_f1_power` | `PascadiSpectralY` with `θexc ≤ 7/32` |
| Final ledger `391/256` | TH.3 | `BANK_EXACT`: `messageLedger_coefficient`, `ledger_391_iff`, `TH3_of_sigma_lt`, `TH3_margin` (`391/256·σ < ε_k/2` from explicit positive assumptions; no `o(1)`) | — |
| h-separation | message pack (`QR < x^{2/3}`, `QR² < Mx^{1−2ε}`, cost `exp((log log x)^5)`) | `BANK_EXACT`: `hsep_cost_subpower`, `hsep_membership`, `subpower_absorbed_by_power`, `log_saving_not_absorbing` | — |
| Cross-coprime partition | inherited (Maynard) | inside `SharpMembership` | `REFEREE_PENDING` #4 |
| Spectral kernel | Pascadi Prop. 3.4/3.8 | narrow provider `PascadiSpectralY` (mentions only Kloosterman forms of bounded sequences) | `EXTERNAL_ANALYTIC` |
| One/two-large (V97) | inherited | not used separately in the message-level chain | `REFEREE_PENDING` #2 |
| `e`-errors | aux error 6 | `BANK_EXACT`: `eErrors_absent_at_one` (reduction at `e = 1`; the errors are proved absent) | — |
| Final remainder | REC.1 | `TAIL_CONDITIONAL`: `RrelMain_eq_sum_Sxi`, `cell_bound`, `RrelMain_bound`, `RSigmaP_littleO_of_minimal`, `sharpPaid_of_spectralY` | see the minimal interface |
| Tail | — | `TAIL_CONDITIONAL`: `Tail287_of_MinimalAnalyticProviders`, `Tail287_of_NarrowProviders`; **no unconditional tail** | `SevenBlockTailFramework` + minimal set |

## Old providers → remaining analytic providers

Old (`Tail287_of_AnalyticProviders`), 9 inputs: `MaynardE1Estimate`, `PascadiE2Printed`,
`QuantitativeTH`, `BDHFamily`, `SpectatorMomentFamily`, `BaseSWProvider`, `AuxPieceProviders`,
`OrderingBSourceDictionary`, `SevenBlockTailFramework`.

New (`Tail287_of_NarrowProviders`):

* **Genuinely analytic estimates (6):** `BaseSWProvider`, `PascadiSpectralY`,
  `SpectatorReciprocalNorm`, the RBDH bound behind `CenteringPaid`, `CoprimalityPaid`
  (divisor/rough count), and the numeric per-cell counts behind the 7 non-critical
  `PiecePaid` cells.
* **Source-level, not reducible with the supplied text (2):** `OrderingBPoissonReduction` and
  `SharpMembership`.
* **Structural (1):** `SevenBlockTailFramework`.

Eliminated or derived: `QuantitativeTH` (now derived), `PascadiE2Printed` and
`MaynardE1Estimate` (not needed), `OrderingBSourceDictionary` (split up), `AuxPieceProviders`
(split up), `BDHFamily` / `SpectatorMomentFamily` (narrowed).
