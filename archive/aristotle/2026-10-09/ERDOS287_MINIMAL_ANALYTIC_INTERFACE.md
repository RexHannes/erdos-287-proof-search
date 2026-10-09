# Erdős #287 — minimal analytic interface after the V99–V100R4 source-chain consolidation

**Erdős #287 is still open. TAIL-287 is NOT BANKED.** Status labels recorded:
`V100R4_AuthorCandidate`, `IndependentTailAuditPending`, `TAIL287_AUTHOR_CHAIN_COMPLETE`,
`TAIL287_INDEPENDENT_BANK_PENDING`. These labels are documentation only. No Lean declaration
uses them, and they instantiate nothing.

Source provenance: the V99–V100R4 formulas were supplied as a **message-level source pack**
(`MESSAGE_LEVEL_SOURCE`: OB.1–OB.10, AB.1/AB.2, AA.1, REC.1, FW.1–FW.6, RG.1, PH.1, TH.1–TH.3 and
the h-separation data). The full V100R/V100R2/V100R4 papers, `COMPLETE_KERNEL_MEMBERSHIP.md` and
the Opus referee report were **not** in the repository. Every Lean object below is stated against
those message-level formulas.

## 1. Conditional tail theorems (Lean)

* `Erdos287.CurrentTail.Tail287_of_AnalyticProviders` (old, preserved unchanged).
* `Erdos287.SourceChain.Tail287_of_MinimalAnalyticProviders`
  (`RequestProject/Erdos287/SourceChain/MinimalTail.lean`).
* `Erdos287.SourceChain.Tail287_of_NarrowProviders`
  (`RequestProject/Erdos287/SourceChain/NarrowTail.lean`). In this version the critical
  `F_AA^♯` payment is derived from the narrow spectral provider and is no longer an input.

There is **no** unconditional tail theorem, no alias, no default instance, and no
classical-choice construction of a provider. `audit.sh` §2 checks this, and the build-time
firewalls in `SourceChain/AxiomAudit.lean` check it too.

## 2. Minimal provider set of `Tail287_of_NarrowProviders`

The inputs are listed in the order of the theorem's signature. "Shape" names the kernel-proved
theorem that turns a numeric per-cell estimate into the named payment. Every provider was
build-checked (`#ct_assert_avoids`) **not** to mention `R_Σ^P`, `Tail287Statement`,
counterexamples or exact words.

| Provider | Exact statement | Source theorem | Why not formalized | Downstream use |
|---|---|---|---|---|
| `SevenBlockTailFramework S` (CurrentTail) | for every `X0` there is `M0` such that every exact word with `M ≥ M0` has a scale `X ≥ X0`, a 7-block affine compiler, finite weights with the main-term dictionary for `R_Σ^P`, and window control | V96/V97 seven-block CRT prescription + main-term evaluation | the prescription and the main-term evaluation are not in the supplied source pack | `tail_of_remainder_littleO` |
| `BaseSWProvider S` (CurrentTail) | tiny-modulus Siegel–Walfisz: `|progErr| ≤ η_X` for all `j, ξ`, `|∑_d ℓ_X(d)/φ(d)| ≤ L_X`, and `ℓ · ∑|Γ| · η · L = o(𝒩_X I)` | V99 base-only BV + large-smooth deletion (`REFEREE_PENDING` #1) | Siegel–Walfisz is not in Mathlib; Mathlib has only qualitative Dirichlet (`Nat.forall_exists_prime_gt_and_eq_mod`) | `Rpaid_littleO` |
| `CoprimalityPaid S` | `R_rel^coprime = o(𝒩_X I)` | coprimality insertion/removal, V100R (aux error 4) | the exact identity is proved (`Rrel_eq_main_sub_coprimality`); the size bound needs a divisor-sum estimate over common factors that the source pack does not supply | `RSigmaP_littleO_of_minimal` |
| `OrderingBPoissonReduction S C` | per packet: `|S_ξ| ≤ cent_ξ + √(𝓑_ξ (‖F_AB‖ + ‖F_commonR‖ + ‖F_commonN‖ + ‖F_diag‖ + ‖F_nearDiag‖ + zm_ξ + ‖F_AA^♯‖))` with the **literal** `F_AB` (OB.7), the literal `F_AA` sectors (OB.9/OB.10) and the literal `S_ξ` | V100R/V100R2: Type-II split → first Cauchy → square → Poisson (`PAPER_VERIFIED_PARTIAL`) | every finite step is kernel-proved (`typeII_split`, `secondTerm_eq_DeltaRel`, `orderingB_physical_square`, `zeroMode_covariance_full`, `FAB_eq_sum_PF`, `FAA_eq_sectors`). The remaining link is Poisson summation with the smooth weight `Ψ`. Mathlib's `Real.tsum_eq_tsum_fourier_of_rpow_decay` exists, but the source pack does not fix `Ψ`, its support or its decay class, so the link cannot be stated literally | `RrelMain_bound`, `cell_bound` |
| `CenteringPaid S C` | `∑_ξ |Γ_ξ| cent_ξ = o(𝒩_X I)` | relative `E₃` centering with reciprocal density `1/φ(f)` (aux error 1) | derived by `centeringPaid_of_RBDH` from a `CenteringSource` + an RBDH bound `∑_F τ(F)^C R_X(F) ≤ C_A N_X² log^{-A}` + the `φ`-weighted spectator norm. The **RBDH/BDH bound** is the analytic core (ordinary divisor-weighted BDH is not in Mathlib) | `RSigmaP_littleO_of_minimal` |
| `SpectatorReciprocalNorm S Fs CD` | `∑_ξ |Γ_ξ|/f_ξ ≤ (log x)^{CD}` | OB.4 spectator reciprocal norm | needs the moment `∑ τ(F)^E/φ(F) ≪ (log)^C`. The finite combinatorics are proved (`spectator_norm_finite`); the moment is analytic | `piecePaid_of_powerSaving`, `piecePaid_of_logSaving` |
| `PascadiSpectralY θQ θR θH δ θexc` with `θexc ≤ 7/32` | for every bilinear Kloosterman form satisfying `E2Hypotheses`: `K² ≤ Y·Z`, `Y ≤ T_H^{θexc/2} Y0`, `Y0·Z ≤ (C x^{-δ} · trivial)²` | Pascadi Prop. 3.4 + Prop. 3.8 (exceptional exponent `≤ 7/32`) | spectral theory of automorphic forms is not in Mathlib. The statement mentions only bounded sequences and the `E₂` shape | `QuantitativeTH_of_spectralY` → `sharp_powerSaving` |
| `SharpMembership` (eventually, every packet) | `F^♯_ξ ≤ P · |𝒦|` for a Kloosterman form `𝒦` satisfying `E2Hypotheses`, with `T_H ≤ x^σ` and `𝓑_ξ · trivial ≤ (x/f)² x^{3σ}` | clean-AA kernel membership = box-stable clean-AA factorisation export (Pascadi Prop. 5.2, `REFEREE_PENDING` #3) + Maynard cross-coprime partition (`REFEREE_PENDING` #4) | the finite parts are proved: scalar weight, low/high split, `|Γ₁| ≤ 1`, affine phase PH.1, `Q₁ = bq₁`, h-separation cost, range interpolation with `θN ≤ 1/3+δ`. The cross-coprime partition and the export depend on inherited items without supplied text | `sharp_powerSaving` |
| partition count `P X ≤ C_P x^η` + ledger `391/256·σ + η/2 < δ/2` | explicit numeric hypotheses | h-separation (`exp((log log x)^5)` cost) | the sub-power cost is proved (`hsep_cost_subpower`, `subpower_absorbed_by_power`); `η` is a free positive parameter | `sharp_powerSaving` |
| `PiecePaid S C p` for the 7 non-critical pieces `fabK1, fabKgt1, commonR, commonN, diagonal, nearDiag, zeroMode` | `∑_ξ |Γ_ξ| √(𝓑_ξ · piece_ξ) = o(𝒩_X I)` | AB.1/AB.2, AA.1, near-diagonal, zero mode | each is reduced by a kernel-proved **per-cell** theorem to explicit numeric inputs; see §3 | `RSigmaP_littleO_of_minimal` |

### Providers that no longer appear in the new chain

* `QuantitativeTH`: derived from the narrow `PascadiSpectralY` with `θexc ≤ 7/32`
  (`QuantitativeTH_of_spectralY`, using `th_exponent_propagation`: `T_H^{7/32} → T_H^{7/64}`
  inside `Y`, and the outer square root gives `T_H^{7/128}`).
* `PascadiE2Printed`: superseded by `PascadiSpectralY` (the printed form without the
  quantitative `T_H` loss is not used).
* `MaynardE1Estimate`: the message-level Ordering-B route has no separate `E₁` Type-II
  estimate. The first-Cauchy square is paid by `F_AB` and `F_AA` (`orderingB_physical_square`,
  `cell_bound`).
* `OrderingBSourceDictionary`: split into kernel-proved algebra plus the single per-packet
  source inequality `OrderingBPoissonReduction`. See the diff in
  `ERDOS287_CURRENT_TAIL_FORMAL_REPORT.md`.
* `AuxPieceProviders`: split into individually named pieces (`CoprimalityPaid`,
  `CenteringPaid`, 8 `PiecePaid` cells), and `eErrors_absent_at_one` for the `e`-errors.
* `BDHFamily`, `SpectatorMomentFamily`: replaced by the narrower RBDH bound in
  `centeringPaid_of_RBDH` and by `SpectatorReciprocalNorm`.

## 3. Per-cell reductions of the non-critical pieces (kernel-proved)

| Piece | Kernel theorem | Remaining numeric / analytic input |
|---|---|---|
| `fabK1` | `PF_decay_bound`, `k1_modulus_exponent` (`59/100 − 5/8 = −7/200`), `k1_power_saving` | `Ψ̂` decay of order `A` (analytic property of the smooth weight) |
| `fabKgt1` | `FAB_kgt1_count` (AB.1), `AB2_cauchy` (AB.2), `fabKgt1_cell_bound` | scale-free `|𝒫_T(q,a)| ≤ V` (sum-side `lattice_discrepancy` is proved for the integer lattice; the Fourier-side `PF` bound is analytic); `∑ τ(r₂)/φ(r₂) ≤ T`; harmonic `∑_l (N/(fl)+1) ≤ NH/f + L`; exponents `fLR/M ≤ x^{σ−7/200}`, `f²L²R/x ≤ x^{σ−7/200−ε}` |
| `commonR`, `commonN`, `diagonal` | `AA1_cauchy`, `aaShape_cell_bound` | physical count `W(MN²/(f²Lz₀) + MN/f)` with `z₀ ≥ x^{η₀}`, `fL/N ≤ x^{−κ₁}` (rough-support counting). `commonN` is **empty** unless the rough-support theorem is supplied (`commonN_empty_of_not_rough`) |
| `nearDiag` | `nearDiag_cauchy`, `nearDiag_cell_bound` | count `W MN²/(f²LK)` (proved style: `pairs_congr_window_real`) |
| `zeroMode` | `zeroMode_covariance_full`, `zeroMode_vanishes_g1`, `zeroMode_full_vanishes` | none when `(r₁,r₂) = 1`; for `g > 1` the AA.1-shape count |

## 4. Smallest remaining analytic provider set

Each item below is an estimate about arithmetic functions or bounded sequences. None of them
mentions #287:

1. **Siegel–Walfisz for tiny moduli** (`BaseSWProvider`), `REFEREE_PENDING` #1.
2. **Divisor-weighted BDH over moduli coprime to `f`** (`hRBDH` in `centeringPaid_of_RBDH`).
3. **Reciprocal divisor moment** `∑ τ(F)^E/φ(F) ≪ (log)^C` (spectator norms).
4. **Pascadi spectral `Y`-bound with `θexc ≤ 7/32`** (`PascadiSpectralY`).
5. **Fourier-side lattice discrepancy and `Ψ̂` decay** for the fixed smooth weight (`F_AB`).
6. **Divisor-in-progressions / rough-support counts** for the cleanup sectors and the
   coprimality error (`CoprimalityPaid`, AA.1-shape counts).
7. **V97 noncritical Type-I / one-large / two-large estimates**, `REFEREE_PENDING` #2. In the
   message-level chain these enter only through `BaseSWProvider` and the non-critical
   `PiecePaid` cells.

Two **source-level** hypotheses also remain. They are not estimates; they are source statements
whose full text was not supplied:

* `OrderingBPoissonReduction`: the Poisson-summation link, `PAPER_VERIFIED_PARTIAL`;
* `SharpMembership` + `PascadiRangeExport` constants: clean-AA kernel membership,
  `REFEREE_PENDING` #3/#4. The three Pascadi range inequalities were given without numeric
  constants, so they are carried as an explicit bundle. The second one is derived only from
  `θN ≤ 1/3 + δ` (`PascadiRangeExport.ineq2_holds`, repair R3).

Finally, `SevenBlockTailFramework` is the structural seven-block input of the tail theorem.

## 5. Existing Lean infrastructure that was searched (§13)

* Mathlib (pinned): no Bombieri–Vinogradov, BDH, Siegel–Walfisz, Kloosterman or spectral
  theorems. Present: Poisson summation (`Real.tsum_eq_tsum_fourier_of_rpow_decay`,
  `SchwartzMap.tsum_eq_tsum_fourier`), qualitative Dirichlet
  (`Nat.forall_exists_prime_gt_and_eq_mod`), and the Selberg sieve framework
  (`Mathlib/NumberTheory/SelbergSieve.lean`). None matches a provider's hypotheses.
* Installed packages: `mathlib`, `batteries`, `aesop`, `Qq`, `plausible`, `proofwidgets`,
  `importGraph`, `LeanSearchClient`, `Cli`. No OpenAI Math, PrimeGaps, PNT+ or PrimeGapsLib
  module is installed, so nothing from them is reused.
* Effectivity (§16): no zero-free-region theorem is available. If one becomes available later,
  it would count as effectivity infrastructure only.
