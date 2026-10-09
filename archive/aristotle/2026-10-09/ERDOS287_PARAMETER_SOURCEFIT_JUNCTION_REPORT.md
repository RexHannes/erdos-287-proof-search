# Erdős #287: closing the parameter and source-fit junction

**Erdős #287 is still open. This report does not claim Tail287, and provider-free `Tail287` is not declared.**

## Verdicts
- **PHYSICAL FACTORIZATION CLOSED**: proved for the actual source in the small-ε₀ regime `CritRegime`. Ordering-B composition: the source-exact identity is proved. The remaining analytic providers are stated in full below.
- **EFFECTIVE ARITHMETIC CLOSED**: `lcm(1..h) ≤ 4^(h-1)` is proved for every h. Uniform hinge positivity and the finite-bank certification remain explicit, unproved inputs.

## Priority 1: actual parameters (`Physical/Factorization/ActualParams.lean`)
- `Dlow_eq_rpow_beta`: proves `D_low = X^β` with `β = 59ε₀/(100(1+ε₀+ε₀⁹))`.
- `CritRegime S κ` is the regime `0<κ<10⁻⁵`, `T ≥ 100/κ`, `T ≥ 2`, `X > 1`. It is **not** arbitrary `Good`.
- `critRegime_Tchoice`: `T = ⌈100/κ⌉₊+2` is a compatible fixed choice.
- `beta_lt_kappa`: `β < κ/100`.
- `Dlow_sq_le`: `D_low² ≤ X^{κ/2}`.
- `CritCell S κ N` is the range `X^{3κ} ≤ N ≤ X^{1/3+κ/2}`. On it:
  - `crit_N_lo` gives `X^{2κ} ≤ N/D_low`;
  - `crit_N_hi` gives `N ≤ X^{1/3+κ}`;
  - `atomParams_of_crit` gives `AtomParams S κ N`.

**Before and after**
- Before:
  ```
  atom_factorization_clean (hA : AtomParams S δ N) (hlow : S.Dlow ^ 2 ≤ S.X ^ (δ / 2)) (hP) (hb) (hq)
  ```
- After:
  ```
  atom_factorization_actual (h : CritRegime S κ) (hN : CritCell S κ N) (hP) (hb) (hq)
  ```
- Removed hypotheses: `AtomParams S δ N` and `D_low² ≤ X^{δ/2}`. Here δ = κ.

## Priority 2: source fit (`TypeII/ProviderDictionary.lean`)
**Decision.** Prop. 5.2 is used only to produce the (5.3) factorization. The downstream trilinear input needs only:
- one-bounded sequences supported on `q ≤ Q`, `s ≤ S`, `r ≤ R`;
- the three boxed range conditions of spec §18.

The source supplies the factorization directly, so literal membership of `b∏q_i` in `𝒟⁺` is **not** retained as a blocker.

This reading rests on the spec's §18 description of what Prop. 4.4 consumes. Pascadi's full text is not in the repository.

**Proved**
- `boxed_one`, `boxed_two`, `boxed_three` and `boxed_mono`.
- `physCoefAtom_eq_dict`: the coefficient equals `σ·a₁(l)·(a₂*a₃)(r)`.
- `physAtom_provider_contract`, which gives:
  - one-boundedness;
  - the supports `≤ Q = N X^{-κ}`, `≤ S = E₁` and `≤ R = E₂`;
  - pairwise coprime supports;
  - `|σ| ≤ |Γ|w`;
  - the three boxed inequalities with ε = κ/2000.

## Priority 3: Ordering-B composition (`TypeII/SourceComposed.lean`)
- `scalarTypeII_eq_cells`: proves the exact identity `scalarTypeII = ∑_{J,P,χ} ∑_{i,i'<n} T(physCell …) + physUrem`. It preserves:
  - the signs `(-1)^J` and the box multiplicities;
  - the residue `c` mod `f` and `(A,B)`;
  - Γ and the cutoff `lr<K`.
  
  The atom coefficient is selected before Cauchy.
- `packet_typeII_eq_cells`: the same identity summed once over `Ξ = XiAll`. The designated pair is part of the packet index and is not summed again.
- `physCell_contract`: the support, norm and size-range contract for each cell.

## Remaining analytic providers (`TypeII/RemainingProviders.lean`, all unproved `Prop`s)
- `PascadiCriticalCellProvider κ`: **Pascadi's beyond-half estimate** for the critical cells. The moduli go up to `X^{59/100}`, so this is not BV/BDH.
- `OrdinaryBVUremProvider κ`: the `h_l U_r` part. Only `f·l` with `l ≤ X^{1/3}` carries a congruence, so this is **ordinary BV/BDH** range.
- `SWSeq`: the Siegel–Walfisz hypothesis on α.
- `scalarTypeII_bound_of_providers` is proved conditionally on the two providers.
- Still outside this file: non-critical routing, Heath–Brown and partial summation from `R_Σ^P`, BaseSW, and the seven-block framework (existing names in `ERDOS287_MINIMAL_ANALYTIC_INTERFACE.md`).

## Priority 4: effective arithmetic (`Effective/LcmBound.lean`, `Effective/V103Comparison.lean`)
**lcm bound and log height**
- `Lh_le_four_pow`: `lcm(1..h) ≤ 4^(h-1)` for every h. The proof uses Kummer's theorem via `Lh_dvd_Lh_mul_choose`.
- `mul_Bh_lt_eight_pow`: `h·B_h < 8^h`.
- `log_height`: `8^h ≤ M ⇒ h ≤ H_*(M)`.
- `log_height_real` and `floor_log_le_Hstar`: `⌊log M/log 8⌋ ≤ H_*(M)`.

**Before and after**
- Before:
  ```
  log_height_of_lcm_bound (hL : LcmBound3) (hM : 9 ^ h < M) : h ≤ Hstar M
  ```
  This is kept.
- After:
  ```
  log_height_nine (hM : 9 ^ h < M) : h ≤ Hstar M
  ```
- Removed hypothesis: `LcmBound3`.

**V103 comparison.** V103's text is not in the repository, so only structural facts about the Lean definitions are proved:
- multiplicity: `sbMeasure_prime_pow`;
- support: `sbMeasure_eq_zero_of_not_dvd`;
- normalization: `sbMeasure_sum` and `hingeT_le_two_mul_card`;
- moving endpoint: `Hstar_mono`.

A literal comparison still needs V103's definitions.

## Verification
- `lake build RequestProject.Erdos287.SourceChain` succeeds (8146 jobs), as does `RequestProject.Erdos287.Effective.Audit`.
- `JunctionAudit.lean` and `Effective/Audit.lean` run `#print axioms` on the composed theorems. All report only `propext`, `Classical.choice` and `Quot.sound`.
- The new files contain no `sorry`, `axiom`, `native_decide`, `unsafe` or `implemented_by`.
