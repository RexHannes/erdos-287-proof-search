# Erdős #287: External provider map (Research Bank V29/V30)

INTERNAL #287 RESEARCH PROGRAMME ONLY. **Erdős #287 is OPEN. Explicit M₀ is OPEN. Finite splice is OPEN.**

This file covers every field of `Erdos287.ResearchBankV29.ProviderElimination.MinimalExternalAnalyticProviders`.

**Honest scope.** The bank defines only some of the objects the fields talk about. The
branch functionals `D0, D1, D2, Db`, the DI class `DIClass`, the principal model `model`, the
universes `E, Psm, Prd`, and `N, Li, phiW` are **theorem parameters**. None of them is built from the
physical #287 source. Where a mapping column below says "parameter", it means this: the variable,
range or coefficient mapping to the cited theorem cannot be checked against the source until that
object is defined. That gap is the SUCCESS D finding of V30.

---

## 1. `rosser : RosserScalarProvider K h F Psm Prd lev X`
- **Lean**: `density : DimensionOneDensity h K`; `F_rosser : ∀ s, 1 ≤ s → s ≤ 3 → F s = 2 e^γ / s`;
  `F_tendsto_one : F S → 1`; `small : ∀ S>0, ∀ ε>0, ∃ x₀, ∀ x ≥ x₀, costU(Psm S x, ellRd(Psm S x, id, lev x), h) ≤ F S + ε`;
  `rough_unrounded : … costU(Prd S x, ellRd(Prd S x, id, X x), h) ≤ F s0 + ε`; `small_nonneg`.
- **Prose**: this is the dimension-one Rosser–Iwaniec upper-bound sieve. Its normalized cost at level `D` tends to `F(s)`, with `F(s) = 2e^γ/s` for `1 ≤ s ≤ 3`.
- **Source**: V22 `RosserCostProvider`, and the V22 report.
- **Variable mapping**: sifting density `h`, dimension-one constant `K`, sieve level `lev x = x^ρ` (ρ = 1/10⁶) for the small primes and `X x = x^{ϑ₀}` (ϑ₀ = 545999/10⁶) for the rough primes.
- **Range / coefficient / normalization**: `Psm, Prd` and `h` are parameters. The cost is `costU` (V22, defined).
- **Effectivity**: effective in principle. No explicit constants are recorded.

## 2. `tuple : PrimeHarmonicTupleProvider h Prd X wτ`
- **Lean**: `rounding : ∀ S>0, ∀ τ>0, ∀ ε>0, ∃ x₀, ∀ x ≥ x₀, costU(rounded ellRd) ≤ costU(unrounded ellRd) + C_{ν,R}(S) τ + ε`.
- **Prose**: rounding the prime endpoints to cells of width τ changes the sieve cost by `O(τ)`. This follows from Mertens-type prime harmonic sums.
- **Source**: V22.
- **Mapping**: the cell width `τ` and the endpoints `wτ` are parameters. `CnuR S` is defined in V22.
- **Effectivity**: effective in principle.

## 3. `euler : PrincipalEulerProvider h r Sd LF I (S0 τC W) N Li phiW model`
- **Lean**: this field is data plus properties. `euler_product : Zgen M s t = excLocal M s t · ∏_{p ∈ good M} eulerFactor p r s t`;
  `zeta_simple_pole` (provable: `zeta_simple_pole_available`); `mellin_truncation`; `mixed_derivative : |mellin M · log^r M − (Sall/Sij)·LF| ≤ ε` eventually;
  `normalization_agreement : S0Contract (S0 τC W) N`; `sifted_main : |model.sifted(pref) − Si (Sij/Si)(Sall/Sij)/Sall · gConst · (LF/I)| ≤ ε` eventually.
- **Prose**: the principal second moment is evaluated through its Euler product and a truncated Mellin integral. The zeroth moment `S0` is asymptotic to `N`.
- **Source**: V23 `PrincipalEulerProvider`, and the V23 report.
- **Mapping**: `S0 τC W` is **defined** (V16 `RouteCConsumer.S0`: the weighted window count of the physical source). `N`, `model`, `Li` and `phiW` are parameters.
- **Normalization**: the same `N` as in S1, pref, the pair baseline and the consumer (`same_normalization_end_to_end`).
- **Effectivity**: ineffective as stated (ε/eventual form).

## 4. `hat : HatReferenceApproximationProvider Kh EAB`
- **Lean**: `nonneg : ∀ M, 0 ≤ EAB M`; `bound : ∃ C ≥ 0, ∃ M₀, ∀ M ≥ M₀, EAB M ≤ C / log M ^ (Kh + 26)`.
- **Prose**: the tensor / hat reference approximation error saves `log^{-(K+26)}`.
- **Source**: V23 `HatApproximationProvider`.
- **Mapping**: `EAB` is a parameter, and it is not defined from the source.
- **Effectivity**: ineffective as stated.

## 5. `di : DISpectralProvider (1/1100) DIClass`
- **Lean**: `spectral : ∀ K : KloostermanData, DIClass K → MaynardAdmissible (1/1100) K → DIConclusion K`, where
  `DIConclusion K := 0 ≤ Ξ ∧ (∀ c supported off-diagonal, ‖Σ_b Σ_z c(z) Kl(b;z)‖ ≤ x^{ε_DI} Ξ ‖c‖₂) ∧ mass·Ξ·√Rep ≤ N_q² T √(Δ₂+Δ₃)`.
- **Prose**: this is the Deshouillers–Iwaniec bound for sums of Kloosterman sums, in Maynard's normalization with ε_DI = η/4 and η = 1/1100.
- **Source**: V27 `DISpectralProvider`.
- **Variable / range mapping**: `MaynardAdmissible` is the literal §5.2 range condition. It is defined.
- **Coefficient mapping**: `c` is supported on the off-diagonal set.
- **Class**: **`DIClass` is undefined.** The field is vacuous for the empty class and false for the full class (`DIClass_underdetermined`). The arithmetic §4 conditions alone also make it false (`arithOnlyClass_provider_false`). The kernel is load-bearing (`kernel_is_load_bearing`). Until DIClass is defined as the literal public DI class, this field cannot be matched to the published theorem.
- **Effectivity**: effective in principle (spectral large sieve). The exceptional-eigenvalue dependence is not tracked.

## 6. `zeroFreq : BranchClassBound Us Ur D0`
- **Lean**: `linear : D0 M (Σ c_i g_i) = Σ c_i D0 M g_i`; `class_bound : ∀ S, ∀ ε>0, ∃ M₀, ∀ M ≥ M₀, ∀ g, SourceFactorization g (Us S M) (Ur S M) → |D0 M g| ≤ ε`.
- **Prose**: masked Siegel–Walfisz / Barban–Davenport–Halberstam for weights of the shape `g ⋆ h`, where both factors are one-bounded and supported on the sieve universes.
- **Source**: V28, plus V25 (`zero_frequency_localized_bound`, which holds for an explicit `FullSum`).
- **Mapping**: `D0` is a **parameter**, not linked to the V25 `FullSum` or to the physical source. `SourceFactorization` is defined (V22).
- **Effectivity**: ineffective (Siegel).

## 7. `oneLarge : BranchClassBound Us Ur D1`
- Same shape as field 6, for the one-large Heath-Brown branch. `D1` is a parameter. **No literal one-large analytic theorem with sequence, modulus and coefficient hypotheses exists in the repository.** The external statement therefore cannot be checked beyond this class-bound shape.

## 8. `twoLarge : BranchClassBound Us Ur D2`
- The same as field 7, for the two-large branch.

## 9. `boundary : BranchClassBound Us Ur Db`
- Same shape as field 6, for the product-boundary contribution. The budget arithmetic is in V26 `BoundaryBudget`. `Db` is a parameter.

## 10. `s1 : S1Contract (S1 τC W) N muF`
- **Lean**: `∀ η > 0, ∃ M₀, ∀ M ≥ M₀, μ_F − η ≤ S1 M / N M`.
- **Prose**: this is the first-moment asymptotic (prime count over the window). It is Bombieri–Vinogradov type.
- **Source**: V14/V15 (`s1_contract`, which is conditional on `OrdinaryBVProvider`).
- **Mapping**: `S1 τC W` is **defined** (V16 `RouteCConsumer.S1`). `N` is the common normalization.
- **Effectivity**: ineffective (BV / Siegel).

---

## Not in the minimal bundle (for completeness)

- `FunctionalKernelCertificate muF WF`. This is a FINITE CERTIFIED INPUT: `7147687/10000 < μ_F`, `W_F < 98278402/10000`, `0 ≤ W_F`. Its provenance is `certificateProvenance`. No certificate data exists in the repository.
- `InternalGlueOwner`. This is INTERNAL and was not eliminated: the fields `tensor` and `nonzero`, as in `PROVIDER_CLASSIFICATION.md`.
