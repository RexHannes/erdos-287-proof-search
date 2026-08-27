import RequestProject.Erdos287.FordGeneratedDepth
import RequestProject.Erdos287.AffineVaughanIdentity
import RequestProject.Erdos287.AffineVaughanPrimeOuter
import RequestProject.Erdos287.AffineTwoOuterSource
import RequestProject.Erdos287.AffineTwoOuterCompiler

/-!
# V14 status ledger — the exact Vaughan / prime-modulus two-outer structural spine

**Erdős #287 remains OPEN.**  Nothing in this run proves it.  In particular nothing here
proves `AFFINE287-PRIME-MODULUS-MU-TWOOUTER45`, smallness of the `k = 0` smooth-parity
packet, FCL, Gate 1A or Gate 1B closure, `WindowPairSupply` for all large `M`, or the Twin
Prime Conjecture.

## What the spine is

```
singleton-generated affine prime packet   (banked, V13)
  -> exact Vaughan decomposition          PROVED_ALGEBRAIC   (Part 3)
  -> prime / prime-power outer split      PROVED_FINITE      (Part 5)
  -> truncated-Möbius cofactor algebra    PROVED_ALGEBRAIC   (Part 7)
  -> prime-modulus two-outer source       PROVED_ALGEBRAIC   (Parts 9, 10)
  -> determinant-one line parametrisation PROVED_ALGEBRAIC   (Part 11)
  -> honest OPEN analytic interface       OPEN_ANALYTIC      (Part 13)
```

## Final ledger

```
FORD-GENERATED-DEPTH-N0-287                    PROVED_FINITE
  (input bounds s ≤ 20, k ≤ 6, ell ≤ 12        PUBLISHED_EXTERNAL_INPUT)
AFFINE287-VAUGHAN-IDENTITY                     PROVED_ALGEBRAIC
AFFINE287-VAUGHAN-SOURCE-ALGEBRA               PROVED_ALGEBRAIC
AFFINE287-VAUGHAN-PRIME-SOURCE                 PROVED_ALGEBRAIC
AFFINE287-VAUGHAN-PRIMEPOWER                   CONDITIONAL_INTERFACE
VAUGHAN-COFACTOR-TRUNCMOBIUS-IDENTITY287       PROVED_ALGEBRAIC
VAUGHAN-COFACTOR-WELLFACTORABLE-NOGO           PROVED_FINITE
AFFINE287-PRIME-MODULUS-SOURCE                 PROVED_ALGEBRAIC
AFFINE287-TWOOUTER-LINE-PARAMETRISATION        PROVED_ALGEBRAIC
AFFINE287-TWOOUTER-LINE-LENGTH45               PROVED_ALGEBRAIC
AFFINE287-PRIME-MODULUS-MU-TWOOUTER45          OPEN_ANALYTIC
AFFINE287-TWOOUTER-COMPARISON-MATCH45          SOURCE_BLOCKED
VAUGHAN-TYPEI-GENERATED-KAPPA45                OPEN_ANALYTIC / CONDITIONAL_INTERFACE
VAUGHAN-TWOOUTER-COMPILER                      PROVED_COMPILER
K0-CELL-IDENTITY                               SOURCE_BLOCKED
SMOOTH-PARITY                                  CONDITIONAL_INTERFACE / OPEN_ANALYTIC
FCL                                            OPEN_ANALYTIC
ERDOS287                                       OPEN_ANALYTIC
```

## Hostile checks (Part 17)

1. **Vaughan identity signs.**  Checked: the identity is
   `Λ = Λ_{≤V} + μ_{≤U}*log − μ_{≤U}*Λ_{≤V}*ζ + μ_{>U}*Λ_{>V}*ζ`, derived by
   `linear_combination (−Λ_{>V}) * (μ*ζ = 1)` in `vaughan_identity_abstract`; the minus
   sign on the third term is forced by the algebra, not chosen.  The pointwise `I₂` carries
   the same minus sign by definition.
2. **Convolution associativity / parentheses.**  `conv_zeta_apply` explicitly rewrites
   `f * g * ζ` as `f * (g * ζ)` via `mul_assoc` before evaluating, so the nested divisor
   sum `∑_{d ∣ L} ∑_{e ∣ L/d}` is the sum over `d e r = L` with no ambiguity.
3. **`Λ_{≤V}` vanishing.**  `vaughan_pointwise` keeps the term as `if L ≤ V then Λ L else 0`;
   `vaughan_pointwise_of_lt` discharges it *from* the hypothesis `V < L`.  It is never
   dropped silently.
4. **Partition exhaustive on the `Λ`-support.**  `vonMangoldt_support_iff` proves the
   equivalence in both directions, and `not_isPrimeOuter_and_isProperPrimePowerOuter`
   proves disjointness.
5. **Cutoff conventions.**  `lambdaU` filters `U < d`; the banked `truncMobius` filters
   `d ≤ T`.  They are related only through the explicit theorem
   `lambdaU_eq_neg_truncMobius`, at the same cutoff value; nothing is silently identified.
6. **`q > 1` before `∑_{d ∣ q} μ(d) = 0`.**  `lambdaU_eq_neg_truncMobius` takes `1 < q` as
   a hypothesis, and `lambdaU_prime` supplies it from `Nat.Prime.one_lt`.
7. **No overclaim of well-factorability.**  The no-go is stated for the explicit
   *balanced support* hypotheses `a` supported in `[1,Q₁]`, `b` in `[1,Q₂]`, `Q₁,Q₂ < ℓ`.
   No literature definition of well-factorability is encoded, and none is refuted.
8. **`s = −1` and `Nat` subtraction.**  `affineNat minus m n = 2mn − 1` is only ever used
   through `affineNat_cast`, which requires `1 ≤ m`, `1 ≤ n` and is proved with
   `Nat.cast_sub`, so no truncation bug can occur.
9. **`p ∤ 2m` before inversion.**  `affine_prime_modulus_residue` takes
   `((2m : ℤ) : ZMod p) ≠ 0` as an explicit hypothesis and uses `eq_mul_inv_iff_mul_eq₀`.
10. **Line parametrisation both ways.**  `affine_det_one_line_param` is an `↔`;
    `affine_line_forward` is sufficiency, `affine_line_complete` necessity.
11. **Uniqueness of `t`.**  `affine_line_param_unique`, from `p ≠ 0`.
12. **Strict exponent margin.**  `twoOuter_line_exponent_lower_bound` is strict
    (`1/6 < 1 − exp M − exp P`) and derived from `σ < 1/6`;
    `twoOuter_line_exponent_margin` gives the explicit `δ` form; the endpoint equality
    `1 − 1/6 − 2/3 = 1/6` is stated separately as an equality.
13. **No hidden analytic estimate in a structure witness.**  `AffineVaughanPrimeCell` and
    `AffinePrimeModulusTwoOuterPacket` contain only finite source data (factorisation,
    primality, congruence).  Every bound lives in a separate, never-inhabited interface.
14. **Comparison main term separate.**  `Affine287TwoOuterComparisonMatch` is a distinct
    source-blocked interface with the three channel quantities as free parameters; no main
    term is defined after the fact.
15. **K0 cell identity external.**  Unchanged from V13: `K0CellIdentitySource` is carried
    as an antecedent by every compiler in this run.
16. **No Gate/F3 provider inhabited by nomenclature.**  `Affine287ToTwoOuterF3Adapter` is
    stated and never inhabited; `twoOuter_bound_transfer_of_adapter` is purely
    conditional.  No map to Gate 1A/1B is asserted.

## Uninhabited interfaces (this run)

`PrimePowerOuterBound`, `AffinePrimeModulusMuTwoOuterInput`,
`VaughanTypeIGeneratedKappaInput`, `Affine287TwoOuterComparisonMatch`,
`Affine287ToTwoOuterF3Adapter` — plus, from earlier runs, `K0CellIdentitySource`,
`SingletonPacketReduction`, `SingletonGeneratedTypeIIInput`,
`FixedCertificateSmoothParityPacket`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace VaughanV14Status

/-! ## Part 2 — Ford generated depth (PROVED_FINITE) -/

#print axioms Erdos287.FordDepth.general_ford_depth_le_112
#print axioms Erdos287.FordDepth.fixed_certificate_depth_le_76
#print axioms Erdos287.FordDepth.fixed_certificate_depth_le_76_of_factors
#print axioms Erdos287.FordDepth.k0_depth_le_40
#print axioms Erdos287.FordDepth.fordGeneratedDepth_mono

/-! ## Part 3 — the exact Vaughan identity (PROVED_ALGEBRAIC) -/

#print axioms Erdos287.Vaughan.vaughan_identity_abstract
#print axioms Erdos287.Vaughan.vaughan_identity_exact
#print axioms Erdos287.Vaughan.vaughan_pointwise
#print axioms Erdos287.Vaughan.vaughan_pointwise_of_lt
#print axioms Erdos287.Vaughan.conv_zeta_apply
#print axioms Erdos287.Vaughan.mul_log_apply
#print axioms Erdos287.Vaughan.trunc_add
#print axioms Erdos287.Vaughan.truncGt_eq_sub

/-! ## Part 4 — affine specialisation (PROVED_ALGEBRAIC) -/

#print axioms Erdos287.Vaughan.affineNat_cast
#print axioms Erdos287.Vaughan.affineNat_pos
#print axioms Erdos287.Vaughan.affineNat_odd
#print axioms Erdos287.Vaughan.vaughan_affine_pointwise
#print axioms Erdos287.Vaughan.vaughan_affine_pointwise_full

/-! ## Part 5 — the outer router (PROVED_FINITE) and its exponent ledger -/

#print axioms Erdos287.VaughanOuter.vonMangoldt_outer_partition
#print axioms Erdos287.VaughanOuter.not_isPrimeOuter_and_isProperPrimePowerOuter
#print axioms Erdos287.VaughanOuter.vonMangoldt_support_iff
#print axioms Erdos287.VaughanOuter.primepower_exponent_five_sixths
#print axioms Erdos287.VaughanOuter.primepower_exponent_saving

/-! ## Part 6 — prime-outer source cell consequences -/

#print axioms Erdos287.VaughanOuter.AffineVaughanPrimeCell.prime_dvd_value
#print axioms Erdos287.VaughanOuter.AffineVaughanPrimeCell.cofactor_dvd_value
#print axioms Erdos287.VaughanOuter.AffineVaughanPrimeCell.p_ne_two
#print axioms Erdos287.VaughanOuter.AffineVaughanPrimeCell.three_le_p

/-! ## Part 7 — cofactor fold (PROVED_ALGEBRAIC) -/

#print axioms Erdos287.VaughanOuter.lambdaU_eq_neg_truncMobius
#print axioms Erdos287.VaughanOuter.lambdaU_prime

/-! ## Part 8 — support no-go (PROVED_FINITE / STRUCTURAL_NO_GO) -/

#print axioms Erdos287.VaughanOuter.prime_support_obstruction_to_balanced_convolution
#print axioms Erdos287.VaughanOuter.vaughan_cofactor_balanced_factorization_impossible
#print axioms Erdos287.VaughanOuter.lambdaU_ne_balanced_convolution_at_prime

/-! ## Part 9 — prime-modulus orientation (PROVED_ALGEBRAIC) -/

#print axioms Erdos287.TwoOuter.affine_prime_modulus_congruence
#print axioms Erdos287.TwoOuter.affine_prime_modulus_residue
#print axioms Erdos287.TwoOuter.affine_prime_not_dvd_m
#print axioms Erdos287.TwoOuter.affine_prime_not_dvd_n
#print axioms Erdos287.TwoOuter.cell_coprime

/-! ## Part 10 — two-outer quotient and source packet -/

#print axioms Erdos287.TwoOuter.cellQuotient_mul_p
#print axioms Erdos287.TwoOuter.cellQuotient_eq_div
#print axioms Erdos287.TwoOuter.deltaMuOne_antidiagonal
#print axioms Erdos287.TwoOuter.AffinePrimeModulusTwoOuterPacket.sum_empty

/-! ## Part 11 — determinant-one line (PROVED_ALGEBRAIC) -/

#print axioms Erdos287.TwoOuter.affine_coprime_of_unit_shift
#print axioms Erdos287.TwoOuter.affine_line_forward
#print axioms Erdos287.TwoOuter.affine_line_complete
#print axioms Erdos287.TwoOuter.affine_det_one_line_param
#print axioms Erdos287.TwoOuter.affine_line_param_unique

/-! ## Part 12 — exponent kernel (PROVED_ALGEBRAIC) -/

#print axioms Erdos287.TwoOuter.twoOuter_line_exponent_lower_bound
#print axioms Erdos287.TwoOuter.twoOuter_line_exponent_margin
#print axioms Erdos287.TwoOuter.twoOuter_line_exponent_endpoint

/-! ## Part 15 — the conditional compiler (PROVED_COMPILER) -/

#print axioms Erdos287.TwoOuterCompiler.singletonTypeII_of_vaughan_twoOuter
#print axioms Erdos287.TwoOuterCompiler.smoothParity_of_vaughan_twoOuter
#print axioms Erdos287.TwoOuterCompiler.parentLeakage_of_vaughan_twoOuter
#print axioms Erdos287.TwoOuterCompiler.twoOuter_bound_transfer_of_adapter

/-! ## Interfaces stated but never inhabited

Listed by `#check` so that the claim is machine-checkable rather than prose. -/

#check @Erdos287.VaughanOuter.PrimePowerOuterBound
#check @Erdos287.TwoOuterCompiler.AffinePrimeModulusMuTwoOuterInput
#check @Erdos287.TwoOuterCompiler.VaughanTypeIGeneratedKappaInput
#check @Erdos287.TwoOuterCompiler.Affine287TwoOuterComparisonMatch
#check @Erdos287.TwoOuterCompiler.Affine287ToTwoOuterF3Adapter
#check @Erdos287.Singleton.K0CellIdentitySource
#check @Erdos287.Singleton.SingletonGeneratedTypeIIInput

end VaughanV14Status
end Erdos287
