# Erdős #287 — physical source completion (Tasks A, B, C)

**Erdős #287 is still open. `Tail287` is not banked and is not claimed anywhere.**

## Verdict

* **SCALAR SOURCE COMPLETE.** The actual parity-sensitive coefficient `ℓ_X` is defined from the
  actual low-prime weights `λ_low^±` and the actual high-prime box grid. Its support, level
  `≤ D_tot = X^{59/100}`, `J = 0` sector, parity decomposition, total-variation bound, and the
  pointwise upper-majorant property are all proved.
* **Type-II: BLOCKED at one precise formula** (the rest of Task B is done). The Heath–Brown
  identity, its dyadic cells, the coefficients `α_n` and `β_m`, their bounds, the literal
  Ordering-B square `V_ξ`, its expansion, the first Cauchy–Schwarz step and the
  source = Ordering-B bridge are all proved. The first missing formula is the **factorization
  rule `d = l·r`** used to turn `ℓ_X(d)` into the two-variable coefficient `c_{ξ,l,r}`.
  Pascadi Prop. 5.2 only says such a well-factorable split *exists* (it depends on the prime
  anatomy of `d`); none of the supplied sources gives an explicit formula. So `c_{ξ,l,r}` is
  built from the actual `ℓ_X` with the split rule left as an explicit parameter `σ`
  (`TypeII/Instance.lean`).
* **Task C:** the bridge from the independently defined Maynard weight `w_X(t)` is proved. The
  ℓ-deleted majorised moment equals the designated-pair packet sum **exactly**, for the actual
  `ℓ_X`. The literal two-prime moment is **bounded above** by that packet sum (`≤`, not `=`,
  because primality is replaced by the majorant `U_X ≥ 1`). For Type-II, the independently
  defined source equals `T_ξ` exactly, and `|T_ξ|² ≤ (∑|β|²)·V_ξ`.

So the overall status is **not** PHYSICAL SOURCE COMPLETE.

## Files (all under `RequestProject/Erdos287/SourceChain/Physical/`; nothing that was already there was weakened)

| File | Contents |
|---|---|
| `Scalar/RosserCore.lean` | Generic Rosser upper/lower inequalities (odd/even position witnesses) |
| `Scalar/Weights.lean` | `ScalarParams`; `eps0 = 1/T`, `tau = eps0^9`, `Dtot = X^{59/100}`, `Dint = Dtot^{1/(1+eps0+tau)}`, `u0`, `Dlow`; Pascadi's `DplusSet`/`DminusSet`; `lamLowPlus`, `lamLowMinus`, `kappa J` (even `J` gives upper, odd `J` gives lower); box grid `boxEnd`, `boxTop`, `H`, `InBox`, `IsHigh`, `boxOf` (ownership rule: the least box); `threshold`; `BoxAdm`; `tuples`, `Tcount`, `gammaP` (repeated-box multiplicity), `Bcoef`; **`ellX`**; `UX`; `ztop`; `Good` |
| `Scalar/Levels.lean` | `Dtot_eq` (`D_tot = D_int^{1+ε₀+τ}`), `Dlow_mul`, box-endpoint lemmas |
| `Scalar/LowSieve.lean` | `lamLowPlus_sum_ge`, `lamLowMinus_sum_le` (Rosser inequalities), support and level lemmas |
| `Scalar/Ownership.lean` | `sum_Bcoef_eq_hw`: summing `B_P` over box tuples (with multiplicities `Γ_P`) gives the set-form high weight; `ellX_eq_setForm` |
| `Scalar/Majorant.lean` | `ellX_J0_sector`, `ellX_support`, `ellX_level`, `UX_eq_parity_sum`, `UX_nonneg`, `UX_majorant`, `UX_ge_one_of_prime` |
| `Scalar/Bound.lean` | `abs_ellX_le`: `|ℓ_X(d)| ≤ T² + 1` |
| `Bridge.lean` | `actualScalar`, `wX`, `maynardFull`, `twoPrimeMoment`, `majorizedMoment`; `majorizedMoment_eq_pairSum`, `pairSum_eq_packets_pos`, `majorizedMoment_eq_packets`, `twoPrimeMoment_le_packets` |
| `TypeII/HeathBrown.lean` | `Mz`, `heathBrown` (general `k`), `heathBrown_three`, `heathBrown_maynard_range`, negative control `maynard_printed_sign_false` |
| `TypeII/Cells.lean` | the six Heath–Brown variables `hbVar`, `hbTerm_eq_sum_cells`, `alphaSeq`, `betaSeq`, `cellSeq_eq_alpha_mul_beta`, `abs_alpha_le`, `alpha_support`, `abs_betaSeq_le`, `divisorPow_le` |
| `TypeII/OrderingB.lean` | `Iz`, `Uz`, `hz`, `typeII_split_Z`, `OBData`, `inner`, **`V`**, `T`, `V_eq_range`, `T_sq_le`, `V_expand`, `base_congruence`, `sum_conv_dyadic`, `source_eq_T` |
| `TypeII/Instance.lean` | `SplitRule`, **`physCoef`** `c_{ξ,l,r} = Γ_ξ ℓ_X(lr) 1[σ(lr)=(l,r)] 1[(f_ξ,lr)=1]`, `physCoef_abs_le`, `physCoef_coprime`, `physCoef_reassemble` |
| `SourceAudit.lean` | `#print axioms` for all of the above, plus negative controls |
| `../Physical.lean` | aggregator; now imports all the new modules |

## Task A details

* `λ_low^+` / `λ_low^-` use Pascadi Def. 5.1: squarefree `b`, all prime factors `< u0`, with
  the Rosser truncation conditions on `DplusSet` / `DminusSet`, level `Dlow = Dint^{ε₀}`.
  Parity convention: even `J` uses the upper weights and odd `J` the lower weights, which
  matches the proof in Lichtman §5. (Lichtman's printed statement says the opposite, but his
  proof uses even = upper.)
* Box grid: the endpoints are `u0^{(1+τ)^j}` and `boxTop j = boxEnd j^{1+τ}`, for
  `j < H`. A prime belongs to the least box containing it (`boxOf`). The parity-dependent
  threshold is `D_int` (even `J`) or `D_int^{1/(1+τ)}` (odd `J`). Tuples are summed with the
  repeated-box multiplicity `Γ_P`. The empty tuple (`J = 0`) is included, and
  `ellX_J0_sector` shows it gives back `λ_low^+`.
* `ℓ_X(d) = ∑_{J ≤ T²} ∑_P 1[BoxAdm] (-1)^J ∑_{ba=d} κ_J(b) B_P(a)`, written literally.
* The upper-majorant statement `UX_majorant` is proved separately, not by definition: if
  `v ≠ 0` and every prime factor of `v` exceeds `ztop`, then `U_X(v) = ∑_{d|v} ℓ_X(d) ≥ 1`.
  `UX_nonneg` gives `U_X ≥ 0` everywhere. Both proofs go through the parity decomposition
  `UX_eq_parity_sum`.
* Level: `ellX_level` gives `ℓ_X(d) ≠ 0 ⇒ d ≤ D_tot = X^{59/100}`, and `Dtot_eq` gives
  `D_tot = D_int^{1+ε₀+τ}`. These are kept as separate facts.

## Task B details

* The Heath–Brown identity with `k = 3` is proved for `n < (z+1)^3`:
  `Λ = 3 log∗M_z − 3 log∗1∗M_z² + log∗1²∗M_z³`.
  **Repair:** the sign `(-1)^j` printed in Maynard's Lemma 5.3 is a misprint. The correct sign
  is `(-1)^{j+1}`, and `maynard_printed_sign_false` refutes the printed version (`n = 2`).
* Each term splits exactly into dyadic cells on rough integers (`hbTerm_eq_sum_cells`). For a
  chosen critical variable `c`, the cell factors as `α ∗ β` (`cellSeq_eq_alpha_mul_beta`), with
  * `|α_n| ≤ 1 + log n`, and `α_n` supported on `[2^{e_c}, 2^{e_c+1})` and on rough `n`;
  * `|β_m| ≤ (1 + log m)^5 d_5(m)`, with `d_k(m) ≤ τ(m)^{k−1}`.
* `V_ξ` is written literally, keeping the residue mask `1_{mn≡c (f)}`, `I_l(mn)`,
  `h_r = I_r − U_r` with integer residue `B`, the plateau profile `Ψ`, and the dyadic ranges.
  Proved facts about it: `V_eq_range`; `T_sq_le` (first Cauchy–Schwarz); `V_expand`
  (Ordering-B expansion with the `m`-sum innermost); `base_congruence` (every surviving term
  has `n₁ ≡ n₂ (mod f l)` and `(n₁n₂, f l) = 1`).
* `source_eq_T`: the Type-II source, defined independently as a convolution sum over `v`, is
  exactly equal to `T_ξ`.
* `c_{ξ,l,r}` (`physCoef`): defined from the actual `ℓ_X`, with
  * `|c| ≤ |Γ_ξ|(T² + 1)`;
  * every nonzero coefficient has `(l, r) = 1`, so the exact split `typeII_split_Z` applies;
  * the reassembly `∑_{l,r} c_{ξ,l,r} g(lr) = Γ_ξ ∑_d 1[(f_ξ,d)=1] ℓ_X(d) g(d)` is lossless.

  **Blocked:** the specific anatomy-dependent split rule `σ` (needed for the well-factorable
  size ranges `l ∼ L`, `r ∼ R`) is not given by any supplied source, and the three-colour
  tensorization is not done.

## Remaining analytic hypotheses (none are discharged here)

1. An explicit well-factorable split rule `σ` with the size constraints of Pascadi Prop. 5.2,
   plus the three-colour tensorization.
2. Bombieri–Vinogradov / Barban–Davenport–Halberstam beyond `1/2` for the well-factorable
   weights (Pascadi; Maynard's Type-II estimate).
3. Bounds `R_rel = o(·)` and `R_base = o(·)` for the relative and base remainders, the Poisson
   / completion identity, and the bounds for `V_ξ` after Ordering B.
4. Fundamental-lemma main terms for `λ_low^±` (the main-term asymptotics, not just the
   pointwise inequalities proved here).
5. Partial summation from `Λ` to prime indicators, and removal of the prime-power and `log`
   weights.
6. The seven-block assembly that turns these into `Tail287`.

## Checks

* `lake build RequestProject.Erdos287.SourceChain.Physical` succeeds (8101 jobs) with no errors
  and no warnings.
* No `sorry`, `axiom`, `native_decide`, `unsafe` or `implemented_by` appears in the new files.
* `SourceAudit.lean`: every listed theorem depends only on
  `[propext, Classical.choice, Quot.sound]`.
* Negative controls:
  * `maynard_printed_sign_false`: the identity with the printed sign is refuted.
  * `Uz_mul_needs_coprime`: `U_{lr} = U_l U_r` fails at `l = r = 2`, so the coprimality
    condition in `typeII_split_Z` is necessary.
  * `ellX_J0_sector`: the full coefficient is **not** ordinary `λ^+`. Its `J = 0` sector alone
    is `λ_low^+`, and the other sectors carry the high-prime box weights.
