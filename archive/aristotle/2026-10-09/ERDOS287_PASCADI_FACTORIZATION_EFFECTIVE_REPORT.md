# Erdős #287: constructive Pascadi factorization, three-colour source completion, effective finisher

**Erdős #287 is still open. This report does not claim Tail287 or the full problem.**

## Verdicts

* **Physical source: PARTIAL CONSTRUCTION, close to closed.** Everything combinatorial is kernel-proved:
  * the Prop. 5.2 greedy factorization;
  * the exact signed three-colour decomposition of `ℓ_X`, with factors bounded by 1, coprime supports, size ranges and a total-variation bound;
  * the constructed Type-II coefficient, with no split parameter σ, plus exact reassembly into the Ordering-B source.

  It is reported as partial, not CLOSED, for two precise reasons. These are *source-fit* caveats, not missing proofs:
  1. **Support level.** Pascadi's Def. 5.1 is applied to the *box upper endpoints*. These are proved to lie in `𝒟⁺_J(D_int^{1+τ})` (`boxVec_vecHyp`, `boxVec_vecHyp_pascadi`, which needs δ ≤ 1/5000). It is **not** proved that each actual prime-level modulus `d = b·∏q_i` lies in `𝒟⁺(x^{3/5−50δ})`. The low-sieve factor `b` (support `𝒟^±(D_low)` by sector parity, `kappa_sector`) is put into `d₁`. This costs an explicit factor `D_low²` on the second and third inequalities (`atom_factorization`). Pascadi's exact system, with δ/2 in place of δ, comes back under the extra parameter condition `D_low² ≤ X^{δ/2}` (`atom_factorization_clean`).
  2. **Repeated boxes.** Repeated boxes are handled by a random-colouring average. The atom weight is `w = 3^J ∏γ_k /(γ(P) 3^K)` rather than a multinomial expansion. The weights are proved nonnegative, and the total is bounded by `∑_{J≤T²} H^J 3^J` (`total_variation_le`). That is an explicitly paid envelope that depends only on `T`, not on `X`.

  **No SOURCE MISMATCH was found.** Every nonzero atom satisfies the support hypotheses at box-endpoint level, and the parity sectors (even J → 𝒟⁺, odd J → 𝒟⁻) are kept apart.
* **Effective finisher: FORMAL ARITHMETIC CLOSED (conditional parts stated as hypotheses).** The log-height lemma is conditional on `LcmBound3` (`lcm(1..h) ≤ 3^h`). That bound is checked by kernel computation for h ≤ 40 but is not in Mathlib in general. The global implication takes the finite exclusion and the uniform hinge bound as hypotheses. Neither the hinge estimate nor any large certificate is asserted.

## Files (new)

`RequestProject/Erdos287/SourceChain/Physical/`
* `Factorization/Additive.lean`: Lemma 5.3 (`lemma53`), placing the first six primes, in log-additive form.
* `Factorization/Prop52.lean`: `prop52_additive`, the full greedy proof (Cases 1, 3.1, 3.2). It is deterministic: positions ≥ 6 go to d₂ unless the case analysis moves them.
* `Factorization/Mult.lean`: `prop52_real` (multiplicative form, `Sys53`).
* `Factorization/Modulus.lean`: `InDplus` (Def. 5.1 on the ordered prime list with multiplicity), `natFactor`, `prop52_vector`, `prop52_nat`. The cases d = 1, fewer than six primes and boundary equalities are handled by padding with 1's (`padOne`).
* `Factorization/Support.lean`: `kappa_sector`, `boxVec_vecHyp(_pascadi)`, `AtomParams`, `atomColour`, `atom_factorization`, `atom_factorization_clean`.
* `Factorization/Colouring.lean`, `Tensor.lean`, `Atoms.lean`, `Decomposition.lean`: `bcoef_tensor`, `partCount_le`, `colFactor_le_one`, `colFactor_support`, `colFactor_coprime`, `abs_lowFactor_le`, `lowFactor_support`, `lowFactor_coprime_high`, `ellX_tensor`, `atomWeight_nonneg`, `atomWeight_mul_le`, `total_variation_le`, `H_eq_of_T`.
* `TypeII/Constructed.lean`: `physCoefAtom`, `physCoefAtom_reassemble`, `physCoefAtom_abs_le`, `physCoefAtom_coprime`, `physCoefAtom_ranges`, `typeII_source_decomp`, `physOB`, `physOB_source_eq_T`.
* `FactorizationAudit.lean`: axiom audit.

`RequestProject/Erdos287/Effective/`
* `Finisher.lean`: `Lh`, `Bh`, `Hstar`, `Counterexample287`, `Bh_values`, `num_le_Bh`, `C_le_Bh`, `row_empty`, `one_prime_finisher`.
* `Hinge.lean`: `Hstar_spec`, `le_Hstar`, `onset_nat` (M ≥ 73811 ⇒ H_* ≥ 10), `onset_exp` (M ≥ e¹²), `LcmBound3`, `lcmBound3_le_40`, `log_height_of_lcm_bound`, `sbMeasure`, `sbMeasure_sum`, `hingeT`, `not_ce_of_hingeT_pos`, `FiniteExclusion`, `UniformHingeBound`, `no_ce_of_finite_and_hinge`.
* `Audit.lean`; aggregator `RequestProject/Erdos287/Effective.lean`.

The definitions of the hinge statistic and the size-biased measure are reconstructed from the request's description. They are documented in the docstring of `Hinge.lean`.

## Before / after (split parameter removed)

Before (`TypeII/Instance.lean`, kept unchanged for preservation):
```lean
theorem physCoef_reassemble (S : Sieve.ScalarParams) (σ : SplitRule) (Γ : ℝ) (f K : ℕ)
    (g : ℕ → ℝ) :
    ∑ l ∈ Ico 1 K, ∑ r ∈ Ico 1 K,
        (if l * r < K then physCoef S σ Γ f l r * g (l * r) else 0) =
      Γ * ∑ d ∈ Ico 1 K, if Nat.Coprime f d then S.ellX d * g d else 0
```
After (`TypeII/Constructed.lean`; there is no `σ`, and the atom colouring is `S.atomColour δ N J P`, built from Prop. 5.2):
```lean
theorem physCoefAtom_reassemble (hS : S.Good) (δ N Γ : ℝ) (f K : ℕ) (g : ℕ → ℝ) :
    ∑ J ∈ range (S.T ^ 2 + 1), ∑ P : Fin J → Fin S.H, ∑ χ : Fin S.Kc → Fin 3,
      ∑ l ∈ Ico 1 K, ∑ r ∈ Ico 1 K,
        (if l * r < K then physCoefAtom S δ N Γ f J P χ l r * g (l * r) else 0) =
      Γ * ∑ d ∈ Ico 1 K, if Nat.Coprime f d then S.ellX d * g d else 0
```
Removed provider argument: `σ : SplitRule`. No other downstream declaration used `σ`, so no other signature changed.

## Heath–Brown sign

The project's proved identity has sign `(−1)^{j+1}`, which is the same as the standard `(−1)^{j−1}`. The negative control for the printed sign (`maynard_printed_sign_false`) is kept. Both are listed in `FactorizationAudit.lean`. The constructed Type-II source does not recombine Heath–Brown terms, so the false sign cannot come back in through it.

## Remaining deep analytic inputs (not proved, not counted as proved)

* Pascadi's beyond-half spectral / W4 estimate for the triply-factored sums. Ordinary BV/BDH does **not** supply this.
* BV/BDH-type level-½ inputs, the R_rel/R_base remainders, Poisson summation steps, fundamental-lemma main terms, partial summation and the seven-block assembly.
* For the effective route: the finite exclusion below M₀, the uniform hinge lower bound, and `LcmBound3` for h > 40.

## Build / audit

* `lake build RequestProject.Erdos287.SourceChain.Physical`: succeeds (includes all factorization modules).
* `lake build RequestProject.Erdos287.Effective.Audit`: succeeds.
* Every audited theorem depends only on `[propext, Classical.choice, Quot.sound]`.
* `rg` finds no `sorry`, `axiom`, `native_decide`, `unsafe` or `implemented_by` in the new files.
