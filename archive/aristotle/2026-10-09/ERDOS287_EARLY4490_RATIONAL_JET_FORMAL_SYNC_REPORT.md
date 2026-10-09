# Erdős #287 — EARLY_4490 rational-jet formal sync report

**Erdős #287 is OPEN and is not claimed anywhere in this layer.**  No computer-assisted
real/analytic certificate was turned into a kernel-proved theorem; every such input is a typed
certificate object whose inhabitation is proved to carry no analytic content.

## 0. Scope and preservation

This run is **append-only**.  No existing module was rewritten and no existing theorem
statement was altered.  In particular the original/effectivity modules, the long-fibre layer
and the whole proper-γ multiplicity layer

```
ProperGammaQFibre.lean            ProperGammaLaneRecombination.lean
ProperGammaSource.lean            ProperGammaMultiplicityGeometry.lean
ProperGammaShellSix.lean          ProperGammaCurrentSurvivor.lean
ProperGammaProductResummation.lean ProperGammaOddConvolution.lean
ProperGammaTruncatedDivisor.lean  ProperGammaMultiplicityLedger.lean
CurrentStatusEffectivityMultiplicity.lean
```

are preserved verbatim and are reused (`B`, `B0`, `beta`, `hz`, `gz`, `rhoOdd`,
`parentAvailable`, `properGammaTarget`, the §41 `Evidence` taxonomy).  Only the newest
aggregator import in `RequestProject/Main.lean` was added.

### Files added (all under `RequestProject/Erdos287/`)

| module | content |
|---|---|
| `ProperGammaAdmission.lean` | exact γ parameters; high-prime admission set; `|H(z)| ≤ 3`; admission inclusion–exclusion; `C3` source typing |
| `Early4490FiniteACompiler.lean` | `w(a)`, `P_d`, `F_M`, `M_N`; the finite-`a` compiler; Abel summation; compiler ⇏ annihilation firewall |
| `Early4490BernoulliJet.lean` | exact `B₂`, `B₃`, strict `ψ`; derivative ladder; the three-term jet `Φ₃`; the Euler/Bernoulli identity interface |
| `Early4490RationalJetSource.lean` | `ω(z)`; the combined joint source `J = R[1] − R[C2]`; `J3`, `Jψ`; chart difference |
| `Early4490FiniteDFT.lean` | exact finite `q`-DFT and inversion; the three Bernoulli zero modes; coprimality-mask firewall |
| `Early4490NearResonance.lean` | the exact near-resonant odd divisor identity |
| `Early4490RationalJetLedger.lean` | `C3` ownership arithmetic; slab partition; range data; budget arithmetic; alternative-chart firewall; certificate objects |
| `CurrentStatusEffectivityEarly4490.lean` | status evolution, retired-method firewalls, open frontier, axiom audit |

### File modified

`RequestProject/Main.lean` — one added import of the new aggregator.

## 1. Fixed parameters (§2)

Exact rationals, no floating-point semantics anywhere in a statement:

```
epsPar   = 1/(2·10^21)
nuPar    = 16623/100000 − 2·epsPar
gammaPar = 1/2 − epsPar
a0Par    = 83377/200000
```

* `gammaPar_eq_a0_add_half_nu : gammaPar = a0Par + nuPar/2` — KERNEL-PROVED.
* `four_nuPar_gt_gammaPar : gammaPar < 4·nuPar` — KERNEL-PROVED.

## 2. High-prime admission (§3)

`N_z = z^{1/γ}` is the real `rpow`; the qualifying set is carried by `HighPrimeData`, which
separates the **arithmetic** finite prime set `H` (odd primes dividing `z`) from the
**threshold order** hypotheses (`T ≤ p` and `z < T⁴`).

* `admission_threshold_pow : 1 < z → z < (N_z^ν)⁴` — KERNEL-PROVED, and this is exactly where
  `4ν > γ` is used.  `ν` is **not** replaced by `ν/2`.
* `highPrimeCount_le_three : D.H.card ≤ 3` — KERNEL-PROVED (four qualifying primes would have
  product `≥ T⁴ > z` while dividing `z`).

## 3. Admission inclusion–exclusion (§4)

`C2` counts the qualifying **unordered** pairs (2-element subsets of `H` passing the source's
pair condition); `C3` is the indicator of the exact three-high-prime exceptional case.

* `gammaAdmission_inclusion_exclusion` — KERNEL-PROVED, with all four admissible cases
  `j = 0,1,2,3` resolved: `e = 1` for `j ≤ 1`; `e = 1 − C2`, `C3 = 0` for `j = 2`;
  `e = 1 − C2 + 2C3`, `C2 ≤ 3` for `j = 3`.
* `admissionE_exceptional_case` : `1 − 3 + 2 = 0`.
* `admissionE_coeff_two_forced` : the coefficient `+2` is the unique annihilating one.
* `admission_no_four_case` : no `j ≥ 4` case is source-admissible.
* `admC3_endpoint_firewall` : endpoint firewalls for `C3`.

## 4. `C3` source status (§5)

* `c3_source_typing` — KERNEL-PROVED: the auxiliary `C3` inclusion–exclusion correction,
  the historical physical "three-high" owner and the pair correction `C2` are three
  **pairwise distinct** named owners.
* `|2 R[C3]|/B_X < 1.1e-10` is **CERTIFICATE-BACKED** (`C3Certificate`,
  `c3Certificate_not_proved`), never a theorem.
* `c3_ownership_arithmetic : parentAvailable − 1.1e-10 = 8.03976032e-9` — KERNEL-PROVED
  exact rational arithmetic, with the banked proper-γ ledger values unchanged
  (`properGamma_ledger_unchanged_by_early4490`).

## 5. Early-slab status (§6)

Rational endpoints `429/10`, `503/10`, `125/2`; `slab_partition` proves every
`L ∈ [42.9, 62.5]` lies in exactly one of EARLY `[42.9, 50.3)` and LATE `[50.3, 62.5]`.
The late-subslab bound `|R_{≥6}|/B_X < 7.8e-9` is a typed certificate
(`lateSubslab_certificate_not_proved`); the analytic inequality is **not** proved.

## 6. EARLY_4490 range data (§7)

`oddACeiling = 4489`, `c2LaneCeiling = 2245`, `z < 7.94e10`, `p < 291200`, `q < 3.913e9`
are recorded as declared range data.  Kernel-proved finite consequences
(`early4490_range_arithmetic`, `range_integer_consequence`): both ceilings are odd,
`2·2245 = 4489 + 1` so `2245` is exactly the largest `a` with `2a ≤ 4490`, the real bounds are
strictly ordered `p < q < z`, and a strict rational bound on a natural number gives the
expected integer consequence.  No decimal enclosure became a hidden axiom.

## 7. Finite-`a` compiler (§8) — high-priority kernel algebra

With `w(a) = μ(a)B(a)/B₁ = μ(a)B₀(a)` (`wCoef_eq_mu_B_div_B1`), the finite odd window
`A(N,t) = {1 ≤ a ≤ min(t,N), a odd}` and `M_N = ∏ {p odd prime, p ∣ M, p ≤ N}`:

* `largePrime_mask_irrelevant` — KERNEL-PROVED: for odd `a ≤ N`, `(a,M) = 1 ↔ (a,M_N) = 1`;
  primes `p > N` dividing `M` cannot alter the mask (nor can the even part of `M`).
* `finiteA_compiler : F_M(t) = Σ_{d ∣ M_N, d ≤ N} μ(d) P_d(t)` — KERNEL-PROVED
  (with `finiteA_compiler_untruncated` and `Pcompiler_eq_zero_of_gt` justifying the `d ≤ N`
  truncation).

## 8. Discrete partial summation (§9)

* `abel_summation_general` — KERNEL-PROVED for an arbitrary finite sequence.
* `Fcompiler_succ_sub` — `F_M` is the summatory function of the masked term.
* `finiteA_partial_summation` — KERNEL-PROVED:
  `Σ_{a=l}^{u} w(a)1_{(a,M)=1}K_a = F_M(u)K_u − F_M(l−1)K_l − Σ_{a=l}^{u−1} F_M(a)(K_{a+1}−K_a)`.
  No analytic smallness conclusion is drawn.
* `compiler_not_fibre_annihilation` — KERNEL-PROVED firewall with an explicit finite witness
  (`N = M = t = 1`, `K ≡ 1`): the compiler identity holds while the compiled sum is `1 ≠ 0`.

## 9. Exact early joint source (§10)

`ω(z) = μ(z)B(z)(1 − C2(z))` (`omegaEarly`), and the early joint source is the **single
combined object** `J(X) = R[1](X) − R[C2](X)` (`Jjoint`).  Only its linear decomposition is
kernel content (`Jjoint_linear_decomposition`), and `joint_split_charging_firewall` exhibits
data with `J = 0` while both constituents are arbitrarily large — so the two pieces must not
be stored as independently chargeable errors.  The required bound `|J|/B_X < 8.03976032e-9`
is defined (`EarlyJointTarget`) and left **OPEN**; `earlyJoint_target_open` shows it is a
genuine, non-tautological proposition that nothing here inhabits.

## 10. Bernoulli polynomials and the three-term jet (§11–§12)

Exact rational `B₂(r) = r² − r + 1/6`, `B₃(r) = r³ − (3/2)r² + (1/2)r`, strict sawtooth
`ψ(r) = r − 1/2` with the repository's endpoint convention (`ψ(0) = −1/2`).  Kernel-proved:
values at `0, 1/2, 1`, the reflections `B₂(1−r) = B₂(r)`, `B₃(1−r) = −B₃(r)`, `ψ(1−r) = −ψ(r)`,
and the derivative ladder `B₃' = 3B₂`, `B₂' = 2ψ` in `Polynomial ℚ`
(`bernoulli_derivative_ladder`).

With `y = z²/X`, `t = zq/X`, `r = frac(z/q)`:

```
Φ₃(z,q;X) = ψ(r)W(y) − (t/2)B₂(r)W'(y) + (t²/6)B₃(r)W''(y)
```

is a KERNEL-PROVED definition (`Phi3`, `Phi3_eq`), together with `Phi3_sub_PhiPsi`,
`Phi3_additive_in_jet`, `Phi3_zero_jet`.

## 11. Euler/Bernoulli identity interface (§13)

Option **B** was taken: `I_X = Φ₃ + E₃ + Δ` is carried by the hypothesis object
`BernoulliJetIdentity` (a structure parameterised by the weight jet), **not** by a custom
axiom.  Only downstream algebra is kernel-proved (`bernoulliJet_downstream_algebra`), and
`bernoulliJetIdentity_not_proved` shows the interface is inhabited by content-free data.

Status: **CONDITIONAL_ANALYTIC_INTERFACE.**

## 12. Rational-jet sources and budgets (§14–§16)

* `J3src` and `Jpsisrc` — KERNEL-PROVED definitions
  (`J3(X) = −4 Σ_z ω(z) Σ_{q∈Q_z} β(q) Φ₃(z,q;X)`, and the sawtooth-only alternative).
* `rationalJet_charts_are_alternatives` — the exact chart difference;
  `J3src_eq_Jpsisrc_of_flat_jet` — the charts coincide when the higher jet vanishes.
* Budget arithmetic (KERNEL-PROVED, exact rationals):
  `8.03976032e-9 − 1.7e-9 = 6.33976032e-9` (`target3_budget_arithmetic`),
  `8.03976032e-9 − 4e-9 = 4.03976032e-9` (`targetPsi_budget_arithmetic`).
* `rationalJet_alternative_chart_no_double_charge` — KERNEL-PROVED: each chart closes the
  allocation exactly, while charging both replacement errors strictly overspends it.
* The replacement errors `|J−J3|/B_X < 1.7e-9` and `|J−Jψ|/B_X < 4e-9` are
  **CERTIFICATE-BACKED**, never proved (`replacement_certificates_not_proved`).

## 13. Finite `q`-DFT and zero modes (§17–§18)

* `finite_dft_inversion` — KERNEL-PROVED exact finite Fourier inversion for the
  coprimality-masked functions `f₁, f₂, f₃`, with respect to `ZMod.stdAddChar`; all sums are
  finite, no asymptotic Fourier series appears.  `dftCoef_zero_eq_zeroMode` identifies the
  `h = 0` coefficient with the zero mode.
* `f1_zero_mode`, `f3_zero_mode` — KERNEL-PROVED `= 0`.  **Deviation recorded honestly:** the
  proof needs only `q > 1`, not oddness, so the theorems are stated in that (more general)
  form; the odd squarefree source moduli are a special case.  `q = 1` genuinely fails
  (`f1_zeroMode_needs_q_gt_one : mean(f₁,₁) = −1/2`), because of the strict endpoint
  convention.
* `f2_zero_mode` — KERNEL-PROVED `mean(f₂,q) = μ(q)φ(q)/(6q²)` for squarefree `q`, from the
  exact period sum `Σ_{r<m} B₂(r/m) = 1/(6m)` (`sum_range_bern2`), Möbius expansion of the
  mask (`coprime_sum_mobius`) and `Σ_{d∣q} μ(d)d = μ(q)φ(q)`
  (`mobius_id_divisors_squarefree`).
* `maskedCorrection_zero_mean` and `f2_zeroMode_mask_firewall` — subtracting the zero mode
  must preserve the coprimality mask: at `q = 3` the masked correction has mean `0` while the
  same constant subtracted without the mask leaves mean `1/54 ≠ 0`.

## 14. Near-resonant odd identity (§19)

`nearResonance_identity` — KERNEL-PROVED, reusing the banked `h_z`, `g_z`, `ρ_odd`:

```
Σ_{d ∣ M} h_z(d) ρ_odd((M+δ)/d) = sgn⁺(δ)/2 · g_z(M) − (δ/2) Σ_{d ∣ M} h_z(d)/d
```

for odd `M ≥ 1` and `−1 < δ < 1`, with the strict `sgn⁺` convention.  It is an exact algebraic
identity only: `nearResonance_no_smallness` records that the global near-resonant aggregate
remains OPEN.

## 15. Retired-method firewalls (§20) and frontier (§22)

`retiredStatus` records: reciprocal-integral control SUPERSEDED; pointwise-small Fourier
remainder shortcut REJECTED_FALSE; coefficient-only `R[1]`/`C2` merge RENAMED_WALL; positive
whole-early-slab wrapper METHOD_NONCLOSING; signed near-resonant aggregate OPEN; selected
Perron OPEN.  No universal impossibility theorem is encoded.

`early4490RationalJet_open_frontier` proves that none of

```
EARLY_4490 reduction, J3, Jψ, signed near-resonant aggregate, selected Perron,
proper-γ over the full slab, S_live, R_012, signed floor, Maynard, final splice,
Erdős #287, Euler/Bernoulli identity
```

is tagged `kernelProved` or `certificateBacked`, and records Erdős #287 as `OPEN`, Maynard as
`NOT ENTERED`.  The late subslab, `q ≤ 200`, `N = 1`, `N = 2..5` and shell `N = 6` remain
CLOSED **at their declared certificate scope** only.

## 16. Build and axiom audit (§24)

* Dedicated builds of all eight new modules: **PASS**.
* Full `lake build`: **PASS**.
* `#print axioms` is run in `CurrentStatusEffectivityEarly4490.lean` for every principal new
  theorem: each depends only on `propext, Classical.choice, Quot.sound`, and several on no
  axioms at all.
* No `sorry`, `sorryAx`, `admit`, custom `axiom`, `native_decide`, `Lean.trustCompiler`,
  `unsafe`, `@[implemented_by]` or `opaque` proof escape occurs in any new module.

## 17. Strict final output

```
MULTIPLICITY BANK:                       PRESERVED
HIGH-PRIME COUNT <= 3:                   KERNEL-PROVED
ADMISSION e = 1 - C2 + 2 C3:             KERNEL-PROVED
FINITE-a COMPILER:                       KERNEL-PROVED
FINITE-a PARTIAL SUMMATION:              KERNEL-PROVED
BERNOULLI B2/B3 ALGEBRA:                 KERNEL-PROVED
THREE-TERM Phi3:                         KERNEL-PROVED DEFINITION
I_X = Phi3 + E3 + Delta:                 CONDITIONAL ANALYTIC INTERFACE
J3 SOURCE:                               KERNEL-PROVED DEFINITION
Jpsi SOURCE:                             KERNEL-PROVED DEFINITION
J3 REPLACEMENT < 1.7e-9:                 CERTIFICATE-BACKED
Jpsi REPLACEMENT < 4e-9:                 CERTIFICATE-BACKED
J3 TARGET 6.33976032e-9:                 KERNEL-PROVED BUDGET ARITHMETIC
Jpsi TARGET 4.03976032e-9:               KERNEL-PROVED BUDGET ARITHMETIC
RATIONAL-JET ALTERNATIVE-CHART FIREWALL: KERNEL-PROVED
FINITE q-DFT:                            KERNEL-PROVED
f1 ZERO MODE:                            KERNEL-PROVED
f2 ZERO MODE:                            KERNEL-PROVED
f3 ZERO MODE:                            KERNEL-PROVED
NEAR-RESONANT DIVISOR IDENTITY:          KERNEL-PROVED
J3 ANALYTIC BOUND:                       OPEN
Jpsi ANALYTIC BOUND:                     OPEN
EARLY_4490:                              STRICTLY REDUCED / OPEN
PROPER-GAMMA:                            OPEN
S_live:                                  OPEN
R_012:                                   OPEN
SIGNED FLOOR:                            OPEN
MAYNARD:                                 NOT ENTERED
FINAL SPLICE:                            OPEN
ERDŐS #287:                              OPEN
FULL LAKE BUILD:                         PASS
DEDICATED BUILD:                         PASS
AXIOM AUDIT:                             PASS
```
