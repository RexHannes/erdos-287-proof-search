# ERDŐS #287 — SHARED-`g₀` ROUTER / REDUCED DENOMINATOR / CAUCHY-REPAIR FRONTIER

## APPEND-ONLY FORMAL DELTA — SAFE BANK REPORT

**Mode: append-only.** No historical file was rebuilt, modified, or superseded. The only
edit to an existing file is the addition of `import` lines at the end of the import block of
`RequestProject/Main.lean`. `CurrentStatusErdos287PrimitiveLocalProfile.lean` was not edited.
`ARISTOTLE_SUMMARY.md` was not edited.

---

## 1. WHAT WAS ALREADY BANKED (UNTOUCHED)

The pre-existing safe bank is retained verbatim:

| module | content |
| --- | --- |
| `RequestProject/CurrentProgramme/PrimitiveRamanujanAlgebra.lean` | primitive-`t` Ramanujan sum, unit shift, divisor normal form |
| `RequestProject/CurrentProgramme/PrimitiveRamanujanReassembly.lean` | the reassembly representation loop |
| `RequestProject/CurrentProgramme/ShortLiftLocalProfile.lean` | `mProfile`, `mProfileDivisor`, the finite Euler-product avatar |
| `RequestProject/CurrentProgramme/PrimitiveDMultiplicity.lean` | fixed-`D` fibre multiplicity `≤ g₀ + 1` |
| `RequestProject/CurrentProgramme/PrimitiveFareyNearCollision.lean` | the exact near-collision Farey count |
| `RequestProject/CurrentProgramme/PrimitiveLocalProfileGramSocket.lean` | `PrimitiveLocalProfileGramInput` — **UNINHABITED**, kept |

Both research interfaces remain **UNINHABITED** and were not inhabited by this delta:

* `ShortLiftEulerAnalyticInput` — UNINHABITED;
* `PrimitiveLocalProfileGramInput` — UNINHABITED.

---

## 2. NEW FORMAL EXACT RESULTS

All statements below are kernel-checked, `sorry`-free Lean theorems in this repository.

### §1 — `DET1-LOCALPROFILE-HARMONIC-TWISTS45` (ALGEBRAIC CORE FORMALLY PROVED)

File: `RequestProject/CurrentProgramme/LocalProfileHarmonicTwists.lean`
(namespace `Erdos287.LocalProfileHarmonic`)

* `rad`, `rad_ne_zero`, `rad_squarefree`, `gcd_rad_eq_one_iff`, `squarefree_of_dvd_rad`
* `moebius_coprime_twist_sum` — resolution of `1_{gcd(d,H)=1}` by `∑_{ℓ | gcd(d,H)} μ(ℓ)` on the
  squarefree support of `μ`
* `twistInner`, `twistInner_reindex`
* **`mProfile_harmonic_twist_expansion`** — the exact finite identity

  ```
  m_{g,b}(Δ) = ∑_{ℓ | rad(2bg)} (1/ℓ) · twistInner ℓ Δ T Ψ
  ```

  stated over the repository's own `Erdos287.ShortLift.mProfile`, with the `ℓ`-inner sum
  supported on `d` with `ℓ ∣ d` and `gcd(d/ℓ, ℓ) = 1`.

The asymptotic claim `total L¹ cost = log^{o(1)} X` is **NOT** formalised (its divisor
estimates are not present). Analytic L¹ cost: **RESEARCH PASS only.**

### §2 — `DET1-SHAREDG0-PRIMITIVE-U-PARAM45` (FORMALLY PROVED)

File: `RequestProject/CurrentProgramme/SharedG0PrimitiveUParam.lean`
(namespace `Erdos287.SharedG0Param`)

* **`sharedG0_u_param_iff`** — the exact solution parametrisation: for fixed `(t₁⁰,t₂⁰)` with
  `r₂t₁⁰ − r₁t₂⁰ = D` and `gcd(r₁,r₂) = 1`, `r₂t₁ − r₁t₂ = D ↔ ∃ u, t₁ = t₁⁰ + r₁u ∧ t₂ = t₂⁰ + r₂u`
* **`sharedG0_u_period`** — the `u mod g₀` residue system: shifting `u` by `g₀k` moves `t₁` by
  `g₁k = g₀r₁k` and `t₂` by `g₂k = g₀r₂k`
* `primitive_not_dvd_t1`, `primitive_not_dvd_t2` — the primitive exclusions `t₁ ≢ 0 (mod p)`,
  `t₂ ≢ 0 (mod p)` for every `p ∣ g₀`
* `excludedU`, `excludedU_mem_iff`
* **`excludedU_eq_iff_dvd_D`** — the two forbidden residues coincide **iff** `p ∣ D`, under the
  clean coprimality hypotheses `p ∤ r₁`, `p ∤ r₂`
* `nuP p D = if p ∣ D then 1 else 2`, and **`card_excludedU`**: the excluded set has cardinality
  exactly `ν_p(D)`.

### §3 — `DET1-SHAREDG0-PRIMITIVE-U-ROUTER45` (FORMALLY PROVED ALGEBRAIC/FINITE CORE)

File: `RequestProject/CurrentProgramme/SharedG0PrimitiveURouter.lean`
(namespace `Erdos287.SharedG0Router`), over the repository's own phase
`Erdos287.NormalForm3221.phase`.

* `admissible` (+ `Decidable` instance), `primitiveUSum`, `excludedResidues`, `norm_phase`
* **`primitiveUSum_eq_complete_sub_excluded`** — the exact local factor: the primitive sum is the
  complete sum minus the sum over the excluded residue set
* **`norm_primitiveUSum_le_modulus`** — `|U_{g₀}(C)| ≤ g₀`; in particular `|U_p(C)| ≤ p`,
  the bound used when `p ∣ C`
* `card_excludedResidues_le_two`, **`norm_primitiveUSum_le_two`** — `|U_p(C)| ≤ 2` when `p ∤ C`
* `prod_primeFactors_dvd_gcd`, **`abs_prod_local_le`** — the deduction

  ```
  |∏_{p | g₀} U_p| ≤ 2^{ω(g₀)} · gcd(g₀, C)
  ```

* `phase_add`, `admissible_mul_iff`, `phase_crt_split`, **`primitiveUSum_crt_split`** — the CRT
  factorisation, in exact two-factor form: for coprime `m, n` with `an + bm = 1`,

  ```
  U_{mn}(C) = U_m(C·a) · U_n(C·b).
  ```

  Iterating this over the primes of a squarefree `g₀` is `U_{g₀,D}(C) = ∏_{p | g₀} U_p`; the
  product bound is stated in the iterated (product) form `abs_prod_local_le`.

### §4 — `sharedGcd_reciprocalDiff_eq_originalDiff` (FORMALLY PROVED)

File: `RequestProject/CurrentProgramme/SharedG0UnitSectorGcd.lean`
(namespace `Erdos287.SharedG0UnitSector`)

* `gcd_congr_of_dvd_sub`, `gcd_unit_cancel`, `gcd_sub_comm`, `isCoprime_of_inverse`,
  `unitSector_coprime_of_inverses`
* **`sharedGcd_reciprocalDiff_eq_originalDiff`** — the exact unit-sector gcd identity: if
  `g₀ ∣ 2b₁x − 1` and `g₀ ∣ 2b₂y − 1` (so `x ≡ (2b₁)^{-1}`, `y ≡ (2b₂)^{-1}` mod `g₀`), then

  ```
  gcd(g₀, x − y) = gcd(g₀, b₁ − b₂).
  ```

  The hypotheses encode `gcd(2b₁b₂, g₀) = 1` intrinsically (it is *derived*, as
  `unitSector_coprime_of_inverses`).
* **`sharedGcd_unitTwisted_reciprocalDiff`** — the same identity after multiplication by a unit
  `s`, i.e. for `C = s((2b₁)^{-1} − (2b₂)^{-1})`.

### §5 — `DET1-SHAREDG0-BPAIR-AVERAGED45` (FORMAL FINITE CORE PASS)

File: `RequestProject/CurrentProgramme/SharedG0BPairAveraged.lean`
(namespace `Erdos287.SharedG0BPair`)

* **`gcd_eq_sum_totient_divisors`** — `gcd(g₀, n) = ∑_{d | g₀, d | n} φ(d)`, and its integer
  version `int_gcd_eq_sum_totient_divisors`
* `pairCountCongruentModulo`, **`pairCountCongruentModulo_le`** — the elementary interval count
  with exact integer floors: `pairCount(d, B) ≤ B · (⌊B/d⌋ + 1)`
* **`bpair_gcd_sum_le_divisorCount`** — the finite precursor

  ```
  ∑_{b₁,b₂ ∈ [0,B)} gcd(g₀, b₁ − b₂) ≤ B²·τ(g₀) + B·g₀,
  ```

  obtained through `∑_{d | g₀} φ(d) = g₀`.

No asymptotic big-O is formalised, and **no downstream analytic large-`g₀` closure is marked.**

### §6 — `DET1-PRIMITIVE-REDUCED-DENOMINATOR45` (FORMALLY PROVED)

File: `RequestProject/CurrentProgramme/PrimitiveReducedDenominator.lean`
(namespace `Erdos287.ReducedDenominator`)

* **`lcm_sharedG0_eq`** — `lcm(g₀r₁, g₀r₂) = g₀r₁r₂` under `gcd(r₁,r₂) = 1`
* `gcd_D_lambda_coprime_left`, `gcd_D_lambda_coprime_right`, **`gcd_D_lambda_dvd_g0`** — with
  `D = t₁r₂ − t₂r₁`, `Λ = lcm(g₁,g₂)` and the primitivity hypotheses `gcd(t₁,g₁) = 1`,
  `gcd(t₂,g₂) = 1`:

  ```
  gcd(D, Λ) ∣ g₀.
  ```

  The argument is by coprimality with `r₁` and with `r₂` separately, hence valuation-safe: the
  hypotheses are the general primitivity conditions and **no squarefree assumption is used.**
* **`reducedDenominator_eq`** — `den(D/Λ) = Λ / gcd(D,Λ)` for `Λ > 0`
* **`reducedDenominator_ge`** — hence

  ```
  den(D/Λ) ≥ r₁r₂ = g₁g₂/g₀².
  ```

### §7 — `DET1-PRIMITIVE-NEARFREQ-COUNT45` (FORMALLY PROVED COUNT PRECURSOR)

File: `RequestProject/CurrentProgramme/PrimitiveNearFreqCount.lean`
(namespace `Erdos287.NearFreqCount`)

The existing `PrimitiveFareyNearCollision` machinery is kept and reused, not replaced.

* `g0_mul_lambda_eq`, `nearFreqSet`, **`nearFreqSet_eq`** — the `‖D/Λ‖ ≤ H/A` parameterisation is
  *exactly* the banked near-collision set at threshold `A/H`
* **`nearFreq_D_mem_Icc`** — the exact finite range of the `D`-residues
* **`nearFreqSet_card_le`** — the exact finite inequality

  ```
  N_near ≤ g₀ + 2·g₀·⌊g₀r₁r₂·H/A⌋,
  ```

  combining the banked fixed-`D` fibre multiplicity `≤ g₀` with the `D`-range count. Its research
  asymptotic form is `N_near ≪ g₀ + g₁g₂H/A`; **the fixed-power analytic saving is not claimed.**

### §9 — the new repair socket (UNINHABITED)

File: `RequestProject/CurrentProgramme/SharedG0CauchyConfigurationSocket.lean`
(namespace `Erdos287.SharedG0Cauchy`)

* `CauchyLedger` — the exact missing analytic/norm ledger, carrying
  * `thetaU` : the **averaged** `b`-pair `U` bound exponent (audit item **A**);
  * `unoscillatedScale` : the natural unoscillated shared-`g₀` scale;
  * `nearDensityGain` : the `Q`-level near-density gain;
  * `cauchyRoots` : the number of Cauchy square roots;
  * `amplitudeExponent` : the final amplitude exponent.
* `CauchyLedger.rootExponent`, `CauchyLedger.RootConsistent`, `CauchyLedger.Valid` — the
  well-formedness conditions, including `thetaU < 1` (audit item **A**: the averaged router,
  not the pointwise `g₀^{1+o(1)}`) and root consistency (audit item **B**).
* `rootExponent_one` (`= 1/2`), `rootExponent_two` (`= 1/4`), `amplitude_dichotomy_nontrivial`
  (`1/4 ≠ 1/2`) — the `density^{1/4}` vs `density^{1/2}` dichotomy, formalised as open.
* `exists_valid_ledger` — the configuration class is non-empty (the socket is not vacuous).
* **`SharedG0CauchyConfigurationInput`** — the analytic interface, **stated and never
  inhabited**.
* `sharedG0CauchyConfiguration_compiler` — the only, trivial, conditional consumer.
* **`sharedG0CauchyConfiguration_not_automatic`** — explicit data refuting the socket, so it is
  a genuine hypothesis and not automatically satisfied.

Research name: `287-K0-SP2-DET1-SHAREDG0-CAUCHY-CONFIGURATION45`.
Status: **ANALYTIC REPAIR OPEN / UNINHABITED.**

### §11–§12 — the new status ledger

File: `RequestProject/Status/CurrentStatusErdos287SharedG0Repair.lean`
(namespace `Erdos287.SharedG0RepairStatus`)

Kernel-checked (`decide +kernel`) integrity theorems over the new ledger:

* `no_closed_rows`, `erdos287_open`, `uniform_k0_open_fcl_not_reached`
* `two_analytic_children_repair_pending`
* `localProfileGram_strictly_reduced_not_promoted`
* `hardDen_child_conditional_not_promoted`
* `cauchyConfiguration_is_first_exact_research_residual`
* `exact_algebraic_rows_are_theorems` — every exact row is backed by the *actual* statement of
  §§1–7, quoted in full
* `router_crt_and_product_bound`
* `analytic_rows_are_uninhabited`
* `cauchy_amplitude_dichotomy_is_open`
* `historical_localProfile_status_preserved` — the imported PRIMITIVE-LOCALPROFILE and BLOCK20
  ledgers are unmodified.

---

## 3. NANC-VERIFIED ANALYTIC STATUS (METADATA ONLY)

Recorded in the new ledger as the label `nancVerifiedPassUninhabited` on the row
`shortLiftEulerAnalytic45`:

```
DET1-SHORTLIFT-EULER-COLLAPSE45 : NANC_VERIFIED_PASS
```

with metadata

| item | status |
| --- | --- |
| old `H/φ(H)` off-axis wording | SUPERSEDED |
| old `1/log H` contour repair | SUPERSEDED |
| valid research contour | `η = c₀/√(log D)` |
| valid threshold | `D_♯ = exp(C_♯ (loglog X)²)` |
| finite Euler product on the retained contour | `H_H(w) ≤ (log X)^{o(1)}`, uniformly for `H ≤ X^C` |
| previous one-full-log budget charge | WITHDRAWN |

**This is research-status metadata only.** No zero-free-region or Euler-product statement is
proved in Lean, and `ShortLiftEulerAnalyticInput` remains **UNINHABITED**. What *is* proved in
Lean is the finite avatar, `mProfileDivisor_euler_product`, which was already banked; the new
status file re-checks it (`analytic_rows_are_uninhabited`).

---

## 4. ANALYTIC REPAIR PENDING

Per the hostile NANC audit, **neither** analytic child is promoted:

```
DET1-LARGESHAREDG0-CELLS45   : REPAIR_PENDING
DET1-PRIMITIVE-NEARFREQ45    : REPAIR_PENDING
```

Neither carries the label `closed` — `two_analytic_children_repair_pending` proves this.

Reasons, both carried explicitly by the §9 ledger:

* **A.** the proof must use the **averaged** `b₁,b₂` gcd router of §5, not the pointwise
  `|U(C)| ≤ g₀^{1+o(1)}`; formalised as `Valid.thetaU_beats_pointwise : thetaU < 1`;
* **B.** the exact Cauchy configuration deciding `density^{1/4}` vs `density^{1/2}`; formalised
  as `RootConsistent` together with `cauchy_amplitude_dichotomy_is_open`.

Current controlling repair: `287-K0-SP2-DET1-SHAREDG0-CAUCHY-CONFIGURATION45`.

---

## 5. CONDITIONAL HARD-DENOMINATOR CHILD

```
287-K0-SP2-DET1-PRIMITIVE-SMALLGCD-FAR-HARDDEN-GRAM45 : PENDING CHILD
```

Conditional on **both** `DET1-LARGESHAREDG0-CELLS45` and `DET1-PRIMITIVE-NEARFREQ45` closing.
It is **not** marked current, **not** closed, **not** inhabited, and has residual rank `0`
(`hardDen_child_conditional_not_promoted`).

`PrimitiveLocalProfileGramInput` was **not** deleted or altered. Historical hierarchy:
`PRIMITIVE-LOCALPROFILE-GRAM45` is `strictlyReducedBlocked` — strictly reduced in research, its
promotion blocked by the repair child (`localProfileGram_strictly_reduced_not_promoted`).

---

## 6. AXIOM AUDIT

File: `RequestProject/Status/AxiomAuditErdos287SharedG0Repair.lean`

`#print axioms` is run for **all 64** new principal declarations of §§1–7, §9 and §12. Every
one reports a subset of

```
[propext, Classical.choice, Quot.sound]
```

(several report strictly fewer; `erdos287_open`, `uniform_k0_open_fcl_not_reached` and
`two_analytic_children_repair_pending` report *no* axioms at all).

Placeholder scan over all ten new files: **no** `sorry`, `admit`, `axiom`, `opaque`, `unsafe`,
`native_decide`, or `implemented_by` occurs anywhere (the only textual match in the repository
is the prose of this audit's own docstring).

---

## 7. BUILD

Targeted module builds, all clean (no errors, no warnings):

```
lake build RequestProject.CurrentProgramme.LocalProfileHarmonicTwists
lake build RequestProject.CurrentProgramme.SharedG0PrimitiveUParam
lake build RequestProject.CurrentProgramme.SharedG0PrimitiveURouter
lake build RequestProject.CurrentProgramme.SharedG0UnitSectorGcd
lake build RequestProject.CurrentProgramme.SharedG0BPairAveraged
lake build RequestProject.CurrentProgramme.PrimitiveReducedDenominator
lake build RequestProject.CurrentProgramme.PrimitiveNearFreqCount
lake build RequestProject.CurrentProgramme.SharedG0CauchyConfigurationSocket
lake build RequestProject.Status.CurrentStatusErdos287SharedG0Repair
lake build RequestProject.Status.AxiomAuditErdos287SharedG0Repair
```

Then the whole project:

```
lake build
Build completed successfully (8253 jobs).
```

No unrelated historical blocker was touched; none was encountered.

### Exact files changed

**New:**

```
RequestProject/CurrentProgramme/LocalProfileHarmonicTwists.lean
RequestProject/CurrentProgramme/SharedG0PrimitiveUParam.lean
RequestProject/CurrentProgramme/SharedG0PrimitiveURouter.lean
RequestProject/CurrentProgramme/SharedG0UnitSectorGcd.lean
RequestProject/CurrentProgramme/SharedG0BPairAveraged.lean
RequestProject/CurrentProgramme/PrimitiveReducedDenominator.lean
RequestProject/CurrentProgramme/PrimitiveNearFreqCount.lean
RequestProject/CurrentProgramme/SharedG0CauchyConfigurationSocket.lean
RequestProject/Status/CurrentStatusErdos287SharedG0Repair.lean
RequestProject/Status/AxiomAuditErdos287SharedG0Repair.lean
ERDOS287_SHAREDG0_CAUCHY_REPAIR_SAFE_BANK_REPORT.md
```

**Modified (imports only):**

```
RequestProject/Main.lean
```

---

## 8. COMMITS / PUSH

The delta was committed and pushed incrementally:

```
SharedG0 repair delta: reduced denominator algebra (Sec 6)
SharedG0 repair delta: unit-sector gcd reduction (Sec 4), averaged b-pair finite core (Sec 5)
SharedG0 repair delta: fixed-D u-parametrisation (Sec 2), near-frequency count precursor (Sec 7)
SharedG0 repair delta: harmonic twist expansion (Sec 1), U router local factor and bounds (Sec 3 stage A)
SharedG0 U router: CRT two-factor split (Sec 3.5)
SharedG0 Cauchy configuration repair socket (Sec 9), uninhabited
SharedG0 repair delta: status ledger (Sec 12), axiom audit (Sec 13), Main.lean imports
```

All pushed to `origin`.

---

## FINAL

```
ERDOS287 OPEN.

UNIFORM k = 0 : OPEN.
FCL           : NOT REACHED.

CURRENT FIRST EXACT RESEARCH RESIDUAL:

    287-K0-SP2-DET1-
    SHAREDG0-CAUCHY-CONFIGURATION45
```
