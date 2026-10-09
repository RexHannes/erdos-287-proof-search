# Erdős #287 — Research Bank V23 report: exact principal CRT measure and same-weight principal

**Erdős #287 remains OPEN.** V23 reconnects the positive square to the original full-lcm principal
term. The finite CRT algebra, the signed expansion, the same-weight bound, the Euler-factor algebra,
the singular cancellation and the rational budget are kernel-proved; the Euler/Mellin asymptotic
and the hat-reference approximation are EXTERNAL PROVIDER interfaces.

Namespace `Erdos287.ResearchBankV23`. Aggregator `RequestProject/Erdos287/ResearchBankV23.lean`.

## Files

| File | Content |
|---|---|
| `PrincipalCRTMeasure.lean` | compatible residues, `principalProb`, **`principal_prob`**, `principal_Li_identity` |
| `FullLCMPrincipal.lean` | `fullLCM W0 s qs = lcm(W0, s, q₁, …, q_r)`, `principal_prob_fullLCM`, `principal_sum_fullLCM` |
| `SingularFactors.lean` | `SingularData` (with nonvanishing hypotheses), `singular_cancellation` |
| `GoodPrimeEulerFactor.lean` | `eulerFactor p r s t`, local signed-square average, zero-parameter avoidance |
| `SameWeightPrincipal.lean` | `signed_expansion`, `Mnew`, `principalSifted`, **`same_weight_principal_bound`** |
| `PrincipalEulerProvider.lean` | `PrincipalModel`, `pref`, `gConst = e^{-γ}/b_z`, `PrincipalEulerProvider`, same-normalization theorem |
| `HatApproximationProvider.lean` | `HatReferenceApproximationProvider`, hat firewall |
| `PrincipalBudget.lean` | exact rational slack, cost algebra of `Λ_new^+`, **conditional principal budget** |
| `Ledger.lean` | `v23Ledger = v22Ledger ++ v23New` |
| `AxiomAudit.lean` | `#print axioms` for all 53 V23 theorems |

## Principal theorems

### LEAN BANK
- `PrincipalCRTMeasure.principal_prob` — for an actual compatible CRT residue `t0`,
  `Prob_i(t ≡ t0 mod L0) = φ(A_i W0)/φ(A_i L0) · 1(gcd(A_i t0 + 1, A_i L0) = 1)`;
  `principal_Li_identity` — `Li/φ(A_i W0) · Prob = Li/φ(A_i L0) · (unit indicator)`.
  `FullLCMPrincipal.principal_prob_fullLCM` / `principal_sum_fullLCM` at the complete modulus
  `L0 = lcm(W0, s, q₁, …, q_r)`. The finite auxiliary set used for CRT probabilities is a model
  device; it is never passed to the prime-distribution theorem as a new modulus.
- `SameWeightPrincipal.signed_expansion` — `E[|B|² S_λ(L_j)]` with `B = Σ_e c_e φ_e` equals the
  original signed expression `Σ_d λ(d) Σ_{e,e'} c_e c̄_{e'} E[φ_e φ̄_{e'} 1_{d|L_j}]` (tensor signs,
  all root-collision states, the same `λ`).
- `SameWeightPrincipal.same_weight_principal_bound` (+ `_LambdaNewPlus`) — after the signs have
  recombined inside `|B|²`: `M_new ≤ C_Λ(h) · principalSifted`, for the SAME weight (V21 quadratic
  domination; uses only nonnegative divisor sums of `Λ_new^+`).
- `GoodPrimeEulerFactor.eulerFactor_eq_local_average` — `E_p(s,t) = 1 + 1/(p-2) Σ_k
  (p^{-s_k-t_k} - p^{-s_k} - p^{-t_k})` is the local average of the signed square;
  `signed_square_zero_is_avoidance` — at zero parameters the signed square is the indicator that
  all spectator forms avoid `p`; `eulerFactor_zero`.
- `SingularFactors.singular_cancellation` — `S_i · (S_ij/S_i) · (S_all/S_ij) = S_all` under explicit
  `S_i ≠ 0`, `S_ij ≠ 0`; `cancellation_needs_nonzero` shows the hypotheses are load-bearing.
- `PrincipalBudget.two_div_diff` — `2/vartheta0 - 2/vartheta = 1000/149057727`;
  `principal_slack` — `A_C - 2/vartheta0 - 1/5000 = 147807727/186322158750 > 0`
  (`A_C = 1000273/273000`, the frozen V16 value); `costU_muE` (the exceptional presieve costs
  exactly `1`), `cost_LambdaNewPlus_eq` (`C_{Λ_new^+}(h) = C_{β_sm^+ ⋆ ℓ_rd}(h)`), `F0_mul_g`
  (`F(s0) · e^{-γ}/b_z = 2/vartheta0`), `gConst_pos_le_two`.
- `HatApproximationProvider.hat_not_differentiableAt_zero`, `hat_ne_differentiable` — the hat
  interpolant `max 0 (1-|x|)` is not differentiable at `0`; no differentiable (smooth) cutoff equals
  it.
- `PrincipalEulerProvider.zeta_simple_pole_available` — the provider's zeta-pole field is provable
  from Mathlib (`riemannZeta_residue_one`).

### EXTERNAL PROVIDER (interfaces; never constructed)
- `PrincipalEulerProvider` — exact good-prime Euler product (with `eulerFactor`, exceptional
  factor kept exact), zeta simple pole, Fourier/Mellin truncation, mixed-derivative integral,
  normalization agreement (`S0Contract S0 N` for the frozen `S0`), sifted main term.
- `HatReferenceApproximationProvider` — `E_ij|A-B|² ≤ C (log x)^{-(K+26)}` eventually.

### LEAN CONDITIONAL
- `PrincipalEulerProvider.principal_euler_asymptotic` —
  `|E_ij|A_{e,x}|² (log x)^r - S_all/S_ij · L_ij(F)| ≤ ε` eventually.
- `PrincipalEulerProvider.same_normalization_sifted_main` — with `N` the SAME frozen normalization
  (the conclusion includes `S0Contract (S0 τ W) N` for the frozen Route-C `S0`):
  `Li/(φ(A_i W0) N) · E[|B|² 1(L_j sifted to z)] = e^{-γ}/b_z · L_ij(F)/I + o(1)`
  (ε/eventual form); the singular chain cancels via `singular_cancellation`. No new denominator.
- `HatApproximationProvider.hat_approximation_eventually_small` — the tensor error is `o(1)`.
- `PrincipalBudget.principal_budget_conditional` — for every `ε > 0` there exist `S`, then `τ`,
  then `M₀` with `M_new ≤ (2/vartheta0 + 1/5000) W_F + ε` for `M ≥ M₀` (`W_F = L_ij(F)/I`), from
  `RosserScalarProvider` + `PrimeHarmonicTupleProvider` + `PrincipalEulerProvider`;
  `principal_budget_conditional_mul` (multiplicative form `(2/vartheta0 + 1/5000 + ε) W_F` for
  `W_F > 0`); `principal_budget_le_A_C` (`M_new ≤ A_C W_F + ε` eventually).

## Trust
See the common trust section in `ERDOS287_RESEARCH_BANK_V24_REPORT.md`. V23: 53 theorems, all
depending only on `propext`, `Classical.choice`, `Quot.sound` (or a subset).
