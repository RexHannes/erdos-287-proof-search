# Erdős #287 — Research Bank V27 report: decorated Maynard / DI reduction, finite-label colour energy, clean nonzero theorem

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős Problem #287 remains OPEN.**  Nothing in this bank is
a proof of #287; no explicit `M₀` is produced and no finite splice is performed.

Mode: APPEND-ONLY / POST-ASTRA / SOURCE-LITERAL / PROVIDER-MINIMIZATION / NO EFFECTIVITY YET.
Research Banks V2–V24, every historical report and `ARISTOTLE_SUMMARY.md` are untouched
(verified by `git diff --name-status a08308e HEAD`, see §Git audit).

Status classes used (only): LEAN BANK, LEAN CONDITIONAL, EXTERNAL PROVIDER, FINITE REGRESSION,
REPAIRED / RETIRED, OPEN (Lean: `ResearchBankV25.Ledger.StatusClass`).

This is the key bank: everything BEFORE the invocation of the deep spectral estimate is Lean-proved,
and the single public analytic input is `DISpectralProvider`.  The clean nonzero bound is a THEOREM
(`clean_nonzero_derived`), not an assumption; the former monolithic V16 clean-source provider is not
used.

## Files and contents

### `RequestProject/Erdos287/ResearchBankV27/DecoratedMaynardSetup.lean`

## §5.1  Exact clean domain

`q = D q₀ ~ Q`, `B = q d`, `U ~ Q d`, `r_i = u_i v_i` with `u_i ~ R`, `v_i ~ S`, and the EXACT
assignment `R = R₃`, `S = R₂`.  The clean conditions are the fields of `CleanDomain`.

## §5.2  Range quantities

    Δ₁ = N² R² S / x,   Δ₂ = N² R³ S⁴ Q / x²,   Δ₃ = N R² S⁵ Q / x².

Required: `Δ₁ ≤ x^{−7η}`, `Δ₂ ≤ x^{−14η}`, `Δ₃ ≤ x^{−14η}` (`RangeConditions`).

**LEAN BANK.**
* `clean_substitution` — `n₁ ≡ n₂ (mod qd)` gives the exact substitution `n₁ − n₂ = f d q`;
* `delta1_rpow`, `delta2_rpow`, `delta3_rpow` — with `N = x^n`, `R = x^r`, `S = x^s`, `Q = x^κ`:
  `Δ₁ = x^{2n+2r+s−1}`, `Δ₂ = x^{2n+3r+4s+κ−2}`, `Δ₃ = x^{n+2r+5s+κ−2}`;
* `rangeConditions_iff_exponents` — for `x > 1` the three range conditions are EQUIVALENT to the
  three linear exponent inequalities (the arithmetic implication of the exponent ledger).

The analytic interpretation of the ranges remains conditional (it enters only through the
providers of `DISpectralProvider.lean`).

Theorems (6): `clean_substitution`, `rpow_pow_nat`, `delta1_rpow`, `delta2_rpow`, `delta3_rpow`, `rangeConditions_iff_exponents`

Definitions / structures: `structure SizeAssignment`, `def SizeAssignment.ofR`, `structure CleanDomain`, `def CleanDomain.q`, `def Delta1`, `def Delta2`, `def Delta3`, `def RangeConditions`

### `RequestProject/Erdos287/ResearchBankV27/OuterInnerSeparation.lean`

After `n₁ − n₂ = f d q` the OUTER variables are `o = (f, n₁, n₂, u₁, u₂, v₂)` and the INNER
variables are `(v₁, h)`.  Admissible decorations are `A(o)` (`|A| ≤ 1`) and `Ψ(v₁, h)`
(`|Ψ| ≤ 1`).

**LEAN BANK.**
* `InnerCoeff` — the type of inner decorations: functions of `(v₁, h)` ONLY;
* `decoration_firewall` — a decoration that depends on a final Kloosterman variable is NOT an
  inner decoration: there is `Φ(i, b)` with `Φ(i, b) ≠ Ψ(i)` for every candidate `Ψ`;
* `joint_dependence_allowed` — `Ψ` may depend JOINTLY on `(v₁, h)` (non-product example);
* **`product_cutoff_separation`** — exact discrete separation on a finite `v₁`-box:
  `1_{u₁ v₁ ≤ T₁} = Σ_{j ∈ V} 1_{u₁ j ≤ T₁} · 1_{v₁ = j}`;  the new phase `1_{v₁ = j}` is an
  INNER `v₁`-coefficient, the factor `1_{u₁ j ≤ T₁}` is OUTER;  `L¹` cost `#V`;
* `separated_inner_coeff_bounded` — `Ψ(v₁,h) · 1_{v₁ = j}` is again a one-bounded inner
  decoration.

**EXTERNAL PROVIDER.**
* `ProductCutoffFourierProvider` — the smooth (Fourier/Mellin) separation with `L¹` cost
  `≤ log^C x` (only needed if the `#V` cost of the exact discrete separation is too large).

Theorems (4): `decoration_firewall`, `joint_dependence_allowed`, `product_cutoff_separation`, `separated_inner_coeff_bounded`

Definitions / structures: `def OneBoundedInner`, `def separatedInner`, `structure ProductCutoffFourierProvider`

### `RequestProject/Erdos287/ResearchBankV27/CommonCauchy.lean`

The decorated sum is `W(A, Ψ) = Σ_o A(o) Σ_i Ψ(i) K(o; i)` with outer coefficients `A` and inner
coefficients `Ψ` (depending on inner variables only), and its energy is
`V(Ψ) = Σ_o |Σ_i Ψ(i) K(o; i)|²`.

**LEAN BANK.**
* `common_cauchy` — `|Σ_o A(o) X(o)|² ≤ (Σ_o w(o)) · Σ_o |X(o)|²` whenever `|A(o)|² ≤ w(o)`;
* **`decorated_cauchy`** — `|W(A,Ψ)|² ≤ mass · V(Ψ)`, `mass = Σ_o w(o)`;
* `decorated_cauchy_normalized` — with the Maynard mass bound
  `mass ≤ log^C x · N²/(Q² R² S³)`:  `|W|² ≤ log^C x · N²/(Q²R²S³) · V(Ψ)`;
* `cauchy_direction_audit` (regression) — the REVERSED inequality `mass · V ≤ |W|²` is FALSE
  (`A = (1, −1)`, `X = (1, 1)`: `|W|² = 0 < 4 = mass · V`).

Theorems (4): `common_cauchy`, `decorated_cauchy`, `decorated_cauchy_normalized`, `cauchy_direction_audit`

Definitions / structures: `def innerSum`, `def decoratedSum`, `def energy`

### `RequestProject/Erdos287/ResearchBankV27/GroupedCoefficient.lean`

After the common Cauchy step the energy `V(Ψ) = Σ_o |Σ_i Ψ(i) K(o;i)|²` is opened.  The
regrouped outer (Kloosterman) variables are `β = n₂ u₁`, `γ = n₁ u₂ v₂`; the pair of inner
variables `((s,h),(t,k))` enters only through the grouped frequency

    ℓ = h t − k s,   z = s t,   y = a f (h t − k s).

**LEAN BANK.**
* `bPsi` — `b_Ψ(z) = Σ_{grp(i,i') = z} Ψ(i) conj Ψ(i')`: its type has NO outer argument;
* **`grouped_expansion`** — if the outer correlation `Σ_o K(o;i) conj K(o;i')` depends on the
  inner pair only through `grp(i,i')` (i.e. equals `Σ_b Kl(b; grp(i,i'))` over the regrouped
  outer variables `b = (β,γ)`), then EXACTLY
  `V(Ψ) = Σ_b Σ_z b_Ψ(z) Kl(b; z)`;  the grouped coefficient `b_Ψ(z)` is the same for every
  `b = (β, γ)`;
* `grpConcrete`, `bPsiConcrete` — the literal grouping `(s,h),(t,k) ↦ (st, af(ht − ks))` and
  `b_Ψ(z,y) = Σ_{st = z, af(ht−ks) = y} Ψ(s,h) conj Ψ(t,k)`;
* `concrete_grouping_ell` — `y = a f ℓ` with `ℓ = ht − ks`.

Theorems (3): `energy_eq_sum_pairs`, `grouped_expansion`, `concrete_grouping_ell`

Definitions / structures: `def bPsi`, `def betaVar`, `def gammaVar`, `def grpConcrete`, `def ellVar`, `def bPsiConcrete`

### `RequestProject/Erdos287/ResearchBankV27/RepresentationMoment.lean`

`A_z = #{(i,i') : grp(i,i') = z}` is the representation count with coefficient `1`.

**LEAN BANK.**
* `bPsi_norm_le` — `|b_Ψ(z)| ≤ A_z` for one-bounded `Ψ`;
* `bPsi_L2_le` — `Σ_z |b_Ψ(z)|² ≤ Σ_z A_z²`;
* `same_rep_relation` — two representations with the same `(z, y)` and the same `(s, t)` satisfy
  `(h − h') t = (k − k') s` (when `a f ≠ 0`);
* `antidiagonal_card` — `#{(k,s) : k s = n} = τ(n)`;
* **`diagonal_count_le`** — for a box of positive `(h,t)` and ANY finite boxes of `k`, `s`:
  `#{(h,t,k,s) : h t = k s} ≤ Σ_{(h,t)} τ(h t)`.  This is the precise arithmetic content of the
  diagonal `ht = ks`; the analytic divisor-moment estimate of `Σ τ(ht)` is NOT claimed here (it
  is the `RepresentationMomentProvider`, `DecoratedLemma.lean`).

Theorems (6): `repCount_nonneg`, `bPsi_norm_le`, `bPsi_L2_le`, `same_rep_relation`, `antidiagonal_card`, `diagonal_count_le`

Definitions / structures: `def repCount`

### `RequestProject/Erdos287/ResearchBankV27/DISpectralProvider.lean`

`DISpectralProvider` is the single public Deshouillers–Iwaniec / Maynard spectral input used
AFTER the grouped coefficient has been constructed.  It is an EXTERNAL PROVIDER (never
constructed).  Its contract exposes exactly:

* the modulus variables `Q, R, S, N, d` and the scale `x`;
* the smooth Kloostermann-type kernel `Kl(b; z)` on regrouped outer variables `b` and grouped
  frequencies `z`;
* the coefficient vector `c(z)`, required to be supported on the off-diagonal range `offDiag`;
* the coefficient `L²` norm `‖c‖₂ = (Σ_z |c(z)|²)^{1/2}`;
* the loss `ε_DI`;
* the output bound `|Σ_b Σ_z c(z) Kl(b; z)| ≤ x^{ε_DI} Ξ ‖c‖₂`, together with its Maynard
  normalisation `mass · Ξ · √Rep ≤ N_q² T (Δ₂ + Δ₃)^{1/2}`.

Admissibility (`MaynardAdmissible`) is the literal range condition of §5.2 with `ε_DI = η/4`.
The provider replaces the former monolithic V16 source-class provider; nothing else analytic
about the clean sum is assumed.

Theorems (5): `degenerateForm_admissible`, `degenerateForm_not_DI`, `DI_not_automatic`, `unrestricted_provider_false`, `admissible_delta_bounds`

Definitions / structures: `structure KloostermanData`, `def bilinear`, `def l2`, `def DIConclusion`, `def MaynardAdmissible`, `structure DISpectralProvider`, `def degenerateForm`

### `RequestProject/Erdos287/ResearchBankV27/DecoratedLemma.lean`

A `DecoratedData` bundles one decorated sum: outer set `O`, inner set `I`, outer coefficient `A`
with Cauchy weights `w` (total `mass`), kernel `K(o; i)`, grouping `grp`, and the Kloosterman
form `KD` of the regrouped outer variables, with the exact regrouping hypothesis `hgrp`.

**EXTERNAL PROVIDER.**
* `RepresentationMomentProvider` — the divisor-type representation bounds
  `Σ_{z off-diag} A_z² ≤ Rep` and the diagonal (`ht = ks`) contribution
  `mass · Σ_{z diag} A_z Σ_b |Kl(b;z)| ≤ x^ε N_q² T Δ₁`.

**LEAN CONDITIONAL** (on `DIConclusion`, i.e. on `DISpectralProvider`, and on
`RepresentationMomentProvider`):
* **`decorated_energy_bound`** — for EVERY one-bounded inner decoration `Ψ`:
  `mass · V(Ψ) ≤ x^ε N_q² T Δ₁ + x^{ε_DI} N_q² T (Δ₂+Δ₃)^{1/2}`;
* **`decorated_master_bound`** — `|W(A,Ψ)| ≤ N_q √T [x^{ε/2} √Δ₁ + x^{ε_DI/2} (Δ₂+Δ₃)^{1/4}]`.

**LEAN BANK** (exponent arithmetic, `T ≤ x^{η/4+ε}`, `ε_DI = η/4`, `0 ≤ ε ≤ η`):
* `first_part_saving` — `√T · x^{ε/2} √Δ₁ ≤ x^{ε − 27η/8}`;
* `second_part_saving` — `√T · x^{η/8} (Δ₂+Δ₃)^{1/4} ≤ 2^{1/4} x^{ε/2 − 13η/4}`;
* `energy_instantiation` — `T (x^ε Δ₁ + x^{η/4} (Δ₂+Δ₃)^{1/2}) ≤ 3 x^{−2η}`;
* **`decorated_conservative`** (LEAN CONDITIONAL) — `mass · V(Ψ) ≤ 3 N_q² x^{−2η}` and
  `|W(A,Ψ)| ≤ √3 N_q x^{−η}`.

Theorems (11): `sqrt_add_le_sqrt_add`, `sqrt_rpow_half`, `mass_nonneg`, `decorated_energy_bound`, `decorated_master_bound`, `rpow_mono_exp`, `first_part_saving`, `second_part_saving`, `energy_instantiation`, `decorated_conservative`, `decorated_conservative_linear`

Definitions / structures: `structure DecoratedData`, `structure RepresentationMomentProvider`

### `RequestProject/Erdos287/ResearchBankV27/FiniteLabelEnergy.lean`

Inner coefficients may carry a label `κ(o) ∈ J` depending on the OUTER variable only:
`X_κ(o) = Σ_i Ψ_{κ(o)}(i) K(o; i)`.  Each `Ψ_j` is an arbitrary inner coefficient (it is a
function of the inner variable only, hence cannot see the final Kloosterman variables).

**LEAN BANK.**
* `label_energy_le` — `Σ_o |X_{κ(o)}(o)|² ≤ Σ_j Σ_o |X_j(o)|²` (positivity / range enlargement;
  NO orthogonality is assumed — the `Ψ_j` are completely arbitrary);
* `labelled_cauchy` — `|W_κ|² ≤ mass · Σ_j V(Ψ_j)`;
* `labelled_sqrt_cost` — if every single label satisfies `mass · V(Ψ_j) ≤ B²`, then
  `|W_κ| ≤ √L · B`: the labels cost `√L` on the linear sum (`L` at energy level only).

**FINITE REGRESSION.**
* `label_energy_not_le_max` — the labelled energy can exceed `max_j V(Ψ_j)`: the factor `L` at
  energy level is genuinely needed (so the linear cost is `√L`, not `1`).

Theorems (4): `label_energy_le`, `labelled_cauchy`, `labelled_sqrt_cost`, `label_energy_not_le_max`

Definitions / structures: `def labelInner`, `def labelEnergy`, `def labelSum`

### `RequestProject/Erdos287/ResearchBankV27/CRTColourOrbit.lean`

The colour phase is
`Ω_D(o; v₁, h) = 1_{(v₁, D) = 1} · e_D(h · c(o) · v̄₁)`, with
`c(o) = (b − a₀) · (n₁ q₀ d u₁ u₂ v₂)⁻¹ mod D`.
Write `g_D = gcd(D, b − a₀)` and `E_D = D / g_D`.

**LEAN BANK** (no character theory anywhere):
* `dvd_mul_iff_div_gcd` — `D ∣ c t ↔ D / gcd(D, c) ∣ t`;
* **`orbit_card`** — `#{ (b − a₀) v mod D : v ∈ (ℤ/D)ˣ } = φ(E_D)`;
* `orbit_card_le` — `φ(E_D) ≤ D`;
* `colour_mem_orbit` — every colour value `c(o)` lies in the orbit (inverse of a unit is a unit);
* `colourPhase_norm_le` — `|Ω| ≤ 1`, so every label coefficient `Ψ_j = Ψ₀ · Ω(j; ·)` is
  one-bounded and depends only on the inner variables `(v₁, h)`;
* `coloured_eq_labelled` — the coloured sum is literally the finite-label sum with one label per
  orbit element (`κ(o) = c(o)`, an OUTER function);
* **`colour_sqrt_phi_bound`** — a single-label decorated estimate `mass · V(Ψ) ≤ B²`, valid for
  every one-bounded inner `Ψ`, yields `|P| ≤ √φ(E_D) · B ≤ √D · B`.

Theorems (9): `dvd_mul_iff_div_gcd`, `orbit_card`, `orbit_card_le`, `eD_norm`, `colourPhase_norm_le`, `colour_mem_orbit`, `labelCoeff_norm_le`, `coloured_eq_labelled`, `colour_sqrt_phi_bound`

Definitions / structures: `def orbit`, `def ED`, `def eD`, `def colourPhase`, `def colourValue`, `def colouredSum`, `def labelCoeff`, `def labelOf`

### `RequestProject/Erdos287/ResearchBankV27/SmoothFrequencyRecovery.lean`

**LEAN BANK** (exact algebra, all inverse-existence hypotheses explicit):
* `reciprocity_dvd` — if `a ā ≡ 1 (mod b)`, `b b̄ ≡ 1 (mod a)` and `(a, b) = 1`, then
  `ab ∣ a ā + b b̄ − 1`;
* `reciprocity_frac` — hence `c ā / b + c b̄ / a − c / (ab) ∈ ℤ` for every integer `c`; with
  `c = a₀ f`, `a = n₁ r₂`, `b = n₂ r₁`, this is the reciprocity step
  `m_{a₀}/L ≡ a₀ f \overline{n₂ r₁}/(n₁ r₂) + a₀/(L n₁) (mod 1)` once the (explicit) relation
  between `m_{a₀}`, `L` and the inverses is substituted (`reciprocity_instance`).
* `fixed_J_exists` / `frequency_tail_absorbed` — a FIXED `J` (chosen before `x → ∞`) makes the
  Schwartz tail beyond `H_cap` absorb any fixed polynomial outer count `x^P` and still save `x^{-A}`.
* `colour_partial_summation` — Abel summation in which the colour coefficients stay INSIDE the
  partial sums and only the smooth physical weight is differenced.
* `real_correction_exponent_facts` — the supplied real-correction exponent `−1079/1900` is
  negative, beats `−1/2` and beats `−η` for `η = 1/1100` (rational arithmetic).

**EXTERNAL PROVIDER** (never constructed):
* `SchwartzFrequencyProvider` — `Σ_{0<|h|≤H} |h| |ψ̂(h/t)| ≤ C_ψ t²`;
* `FrequencyCapProvider` — for a fixed `J > 2`, the tail `Σ_{H_cap<|h|≤H} |ψ̂(hM/L)| ≤
  C_{ψ,J} (L/M) x^{−(J−1)η/4}`, with `H_cap = C Q d R² S² / M · x^{η/4}` (no exponential decay
  is claimed for compactly supported smooth weights);
* `SmoothRecoveryProvider` — the variation bound `Σ_n |b_{n+1} − b_n| ≤ V` for the physical
  smooth cutoff.

The derivation of the literal exponent `1079/1900` from the analytic real-correction estimate is
NOT reconstructed here: it is recorded as the supplied value, and only its rational arithmetic is
kernel-checked.

Theorems (10): `reciprocity_dvd`, `reciprocity_frac`, `reciprocity_instance`, `real_correction_conditional`, `real_correction_exponent_facts`, `fixed_J_exists`, `frequency_tail_absorbed`, `frequency_cap_conditional`, `colour_partial_summation`, `smooth_recovery_conditional`

Definitions / structures: `structure SchwartzFrequencyProvider`, `def realCorrectionExponent`, `def Hcap`, `structure FrequencyCapProvider`, `structure SmoothRecoveryProvider`

### `RequestProject/Erdos287/ResearchBankV27/CleanNonzero.lean`

The clean nonzero bound is here a THEOREM, derived from:
* the decorated master lemma (`DecoratedLemma`, itself LEAN CONDITIONAL on `DISpectralProvider`
  and `RepresentationMomentProvider`);
* the finite-label colour energy and the CRT orbit count (`FiniteLabelEnergy`, `CRTColourOrbit`,
  LEAN BANK);
* the exact `1/d` factor and the global conductor aggregation (`GlobalConductorSum`,
  LEAN CONDITIONAL on `DivisorSumProvider`);
* the named operator/pruning contract `NonzeroPruningContract` (the identity
  `R_nonzero = Σ_{D,b} Γ(D,b) P_clean(D,b) + E` with an acceptable error `E`).

Smooth-cutoff recovery (`SmoothFrequencyRecovery`) enters through the kernel `K` of each clean
state; its providers are recorded in the V28 analytic bundle.

**LEAN CONDITIONAL.**
* **`clean_state_bound`** — `|P_clean(D,b,d)| ≤ √φ(E_D) · √3 N_q x^{−η} / d` and
  `≤ √D · √3 N_q x^{−η} / d`;
* **`clean_global_bound`** — `Σ_{D,b} |Γ(D,b)| |P_clean(D,b)| ≤ √3 (N²/U) x^{−347/418000 + ε}`;
* **`clean_nonzero_derived`** (`CleanNonzeroDerivedProvider`, a theorem) — for every fixed `A`
  there is `X₀` such that for `x ≥ X₀`: `[Re R_nonzero]_+ ≤ (N²/U) / log^A x`.

**LEAN BANK.**
* `log_power_absorbed` — `K · log^A x ≤ x^c` eventually, for fixed `c > 0`.

Theorems (4): `clean_state_bound`, `clean_global_bound`, `log_power_absorbed`, `clean_nonzero_derived`

Definitions / structures: `structure CleanState`, `def CleanState.P`, `def CleanAdmissible`, `structure NonzeroPruningContract`

### `RequestProject/Erdos287/ResearchBankV27/GlobalConductorSum.lean`

**LEAN BANK.**
* `denominator_split` / `exact_one_over_d` — the actual denominator `q d u₁ v₁ u₂ v₂` equals
  `d · (q u₁ v₁ u₂ v₂)`, so the decorated sum carries the exact outside factor `1/d`;
* `fixed_lifted_scale_factor` — at FIXED lifted scale `Q = D Q₀` the common `1/Q` factors out;
* `global_aggregation` — (root-mass contract) + (per-state bound `√D · B`) + (divisor-sum bound)
  give `Σ_D Σ_b |Γ(D,b)| |P(D,b)| ≤ x^{3σ/2+ε} B`;
* `clean_energy_saving` — `η − 3σ/2 = 347/418000 > 0` for `η = 1/1100`, `σ = 1/19000`;
* `clean_discrepancy_saving` — after the final Cauchy: `(η − 3σ/2)/2 = 347/836000 > 0`.

**FINITE REGRESSION.**
* `fixing_Q0_alone_invalid` — with `Q₀` fixed but `D` varying, the lifted scales differ and no
  single denominator `D·Q₀` factors out of the sum.

**EXTERNAL PROVIDER** (never constructed):
* `DivisorSumProvider` — `Σ_{D ≤ x^σ} τ(D)^C √D ≤ x^{3σ/2 + ε}`.

Theorems (8): `denominator_split`, `exact_one_over_d`, `fixed_lifted_scale_factor`, `fixing_Q0_alone_invalid`, `global_aggregation`, `clean_energy_saving`, `clean_discrepancy_saving`, `global_saving_rpow`

Definitions / structures: `structure DivisorSumProvider`, `def eta`, `def sigma`

### `RequestProject/Erdos287/ResearchBankV27/Ledger.lean`

Status classes are those of `ResearchBankV25.Ledger.StatusClass`.

Theorems (2): `v27_final_status`, `v27_bank_certificate`

Definitions / structures: `inductive V27Item`, `def status`

### `RequestProject/Erdos287/ResearchBankV27/AxiomAudit.lean`

`#print axioms` for every theorem of the bank (76 theorems).

Aggregator: `RequestProject/Erdos287/ResearchBankV27.lean` (imports every file above).

## Notes, deviations and honest caveats

* Files use ordinary (non-`module`) Lean headers, exactly like the frozen banks V2–V24, so that they
  import the frozen banks unchanged.
* **DI class restriction (important).**  A provider quantified over ALL admissible Kloosterman data
  is provably FALSE (`unrestricted_provider_false`, via an explicit degenerate admissible form with
  `Ξ = 0`).  `DISpectralProvider η DIClass` therefore quantifies over a class `DIClass` of genuine DI
  forms, and each realized clean form must be certified to lie in `DIClass`
  (`CleanAdmissible`).  This keeps the provider satisfiable in principle and makes the certification
  obligation explicit.
* The master bound is stated with `N_q` in place of `N²/Q` and with the representation/diagonal loss
  written as `x^ε`; the conservative bound carries the explicit constant `√3`
  (`|W| ≤ √3 N_q x^{−η}`).
* Representation moment: the finite combinatorics (`bPsi_norm_le`, `bPsi_L2_le`,
  `same_rep_relation`, `diagonal_count_le`) are LEAN BANK; the divisor-type moment bound itself is
  `RepresentationMomentProvider` (LEAN CONDITIONAL row).
* The real-correction exponent `−1079/1900` is recorded as the supplied value; its derivation from
  the analytic estimate was not reconstructed (only its rational arithmetic is checked).
* The pruning/operator identity `R_nonzero = P_clean + acceptable errors` was not found in the
  frozen banks as a Lean theorem; it is carried as the NAMED contract `NonzeroPruningContract`.
* The smooth-recovery providers (`SchwartzFrequencyProvider`, `FrequencyCapProvider`,
  `SmoothRecoveryProvider`) are used in the LEAN CONDITIONAL theorems of `SmoothFrequencyRecovery`;
  the construction of each clean state's kernel from the physical smooth cutoff is part of the clean
  realization (V28) and is not itself formalized.

## Trust / validation

* Build commands (all succeed):
  * `lake build RequestProject.Erdos287.ResearchBankV27` — includes `RequestProject.Erdos287.ResearchBankV27.AxiomAudit`;
  * full project `lake build` — `Build completed successfully (8883 jobs)`; no warnings reported in any V25–V28 file.
* `#print axioms` on all 76 theorems of the bank (`AxiomAudit.lean`): every theorem depends
  only on a subset of `propext`, `Classical.choice`, `Quot.sound`.  Across V25–V28 (220 theorems):
  201 use all three, 9 use `propext, Quot.sound`, 2 use `propext` only, 8 use no axioms.
  No `sorryAx`, no `Lean.ofReduceBool`, no `Lean.trustCompiler`, no custom axiom.
* Forbidden-token scan (`rg` for `sorry`, `admit`, `axiom` declarations, `native_decide`,
  `bv_decide`, `unsafe`, `implemented_by`, `opaque`, `skipKernelTC`, `trustCompiler`,
  `ofReduceBool`) over `RequestProject/Erdos287/ResearchBankV25*` … `V28*`: no occurrences (the only
  hits are the words "axiom audit" in the `AxiomAudit.lean` headers and the `#print axioms`
  commands).  Only ordinary kernel `decide` is used.
* External checker: the installed checker is `leanchecker` (bundled with the toolchain);
  `lean4checker` is NOT installed.  Command:
  `lake env leanchecker --fresh RequestProject.Erdos287.ResearchBankV27` — result: exit code 0, no errors reported (wall time 46m08s; `--fresh` re-checks the module together with all of its imports, including Mathlib and the frozen banks).
* Comparator: not installed (`comparator` not found); no comparator run and no emulation.

## Git audit

* Base commit: `a08308e` (Initial commit of this run).
* `git diff --name-status a08308e HEAD`: 48 entries, ALL of status `A` (added); modified/deleted
  entries: none.
* Modified files: none.  V2–V24, every historical report and `ARISTOTLE_SUMMARY.md` are untouched.
* Full list of added paths (all four banks):

```
A	ERDOS287_RESEARCH_BANK_V25_REPORT.md
A	ERDOS287_RESEARCH_BANK_V26_REPORT.md
A	ERDOS287_RESEARCH_BANK_V27_REPORT.md
A	ERDOS287_RESEARCH_BANK_V28_REPORT.md
A	RequestProject/Erdos287/ResearchBankV25.lean
A	RequestProject/Erdos287/ResearchBankV25/AxiomAudit.lean
A	RequestProject/Erdos287/ResearchBankV25/CorrectionAggregation.lean
A	RequestProject/Erdos287/ResearchBankV25/Counterfixtures.lean
A	RequestProject/Erdos287/ResearchBankV25/ExceptionalStateLocalization.lean
A	RequestProject/Erdos287/ResearchBankV25/FixedModulusCentering.lean
A	RequestProject/Erdos287/ResearchBankV25/FixedResidueEnergy.lean
A	RequestProject/Erdos287/ResearchBankV25/GoodModulusClearing.lean
A	RequestProject/Erdos287/ResearchBankV25/Ledger.lean
A	RequestProject/Erdos287/ResearchBankV25/LocalizationContract.lean
A	RequestProject/Erdos287/ResearchBankV26.lean
A	RequestProject/Erdos287/ResearchBankV26/AxiomAudit.lean
A	RequestProject/Erdos287/ResearchBankV26/BoundaryBudget.lean
A	RequestProject/Erdos287/ResearchBankV26/DyadicSourceMap.lean
A	RequestProject/Erdos287/ResearchBankV26/HBBranchCoverage.lean
A	RequestProject/Erdos287/ResearchBankV26/HeathBrownIdentity.lean
A	RequestProject/Erdos287/ResearchBankV26/Ledger.lean
A	RequestProject/Erdos287/ResearchBankV26/ProductIntervalBoxes.lean
A	RequestProject/Erdos287/ResearchBankV26/RoughConvolution.lean
A	RequestProject/Erdos287/ResearchBankV26/RoughSWAdapter.lean
A	RequestProject/Erdos287/ResearchBankV26/SingletonBins.lean
A	RequestProject/Erdos287/ResearchBankV27.lean
A	RequestProject/Erdos287/ResearchBankV27/AxiomAudit.lean
A	RequestProject/Erdos287/ResearchBankV27/CRTColourOrbit.lean
A	RequestProject/Erdos287/ResearchBankV27/CleanNonzero.lean
A	RequestProject/Erdos287/ResearchBankV27/CommonCauchy.lean
A	RequestProject/Erdos287/ResearchBankV27/DISpectralProvider.lean
A	RequestProject/Erdos287/ResearchBankV27/DecoratedLemma.lean
A	RequestProject/Erdos287/ResearchBankV27/DecoratedMaynardSetup.lean
A	RequestProject/Erdos287/ResearchBankV27/FiniteLabelEnergy.lean
A	RequestProject/Erdos287/ResearchBankV27/GlobalConductorSum.lean
A	RequestProject/Erdos287/ResearchBankV27/GroupedCoefficient.lean
A	RequestProject/Erdos287/ResearchBankV27/Ledger.lean
A	RequestProject/Erdos287/ResearchBankV27/OuterInnerSeparation.lean
A	RequestProject/Erdos287/ResearchBankV27/RepresentationMoment.lean
A	RequestProject/Erdos287/ResearchBankV27/SmoothFrequencyRecovery.lean
A	RequestProject/Erdos287/ResearchBankV28.lean
A	RequestProject/Erdos287/ResearchBankV28/AxiomAudit.lean
A	RequestProject/Erdos287/ResearchBankV28/EffectivityFirewall.lean
A	RequestProject/Erdos287/ResearchBankV28/ExactParameterInstantiation.lean
A	RequestProject/Erdos287/ResearchBankV28/FinalPairComposition.lean
A	RequestProject/Erdos287/ResearchBankV28/FinalStatus.lean
A	RequestProject/Erdos287/ResearchBankV28/PreEffectivityTheorem.lean
A	RequestProject/Erdos287/ResearchBankV28/RepairedAnalyticBundle.lean
```

Files added by this bank:

* `RequestProject/Erdos287/ResearchBankV27.lean`
* `RequestProject/Erdos287/ResearchBankV27/DecoratedMaynardSetup.lean`
* `RequestProject/Erdos287/ResearchBankV27/OuterInnerSeparation.lean`
* `RequestProject/Erdos287/ResearchBankV27/CommonCauchy.lean`
* `RequestProject/Erdos287/ResearchBankV27/GroupedCoefficient.lean`
* `RequestProject/Erdos287/ResearchBankV27/RepresentationMoment.lean`
* `RequestProject/Erdos287/ResearchBankV27/DISpectralProvider.lean`
* `RequestProject/Erdos287/ResearchBankV27/DecoratedLemma.lean`
* `RequestProject/Erdos287/ResearchBankV27/FiniteLabelEnergy.lean`
* `RequestProject/Erdos287/ResearchBankV27/CRTColourOrbit.lean`
* `RequestProject/Erdos287/ResearchBankV27/SmoothFrequencyRecovery.lean`
* `RequestProject/Erdos287/ResearchBankV27/CleanNonzero.lean`
* `RequestProject/Erdos287/ResearchBankV27/GlobalConductorSum.lean`
* `RequestProject/Erdos287/ResearchBankV27/Ledger.lean`
* `RequestProject/Erdos287/ResearchBankV27/AxiomAudit.lean`
* `ERDOS287_RESEARCH_BANK_V27_REPORT.md`
