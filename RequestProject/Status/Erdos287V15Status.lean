import RequestProject.Erdos287.AffineMuLogIdentity
import RequestProject.Erdos287.AffineMuLogHardSource
import RequestProject.Erdos287.AffineMuLogLine
import RequestProject.Erdos287.AffineMuLogExponentLedger
import RequestProject.Erdos287.BalancedSevenFinite
import RequestProject.Erdos287.BalancedSevenPolarization

/-!
# V15 status ledger — the `Λ = μ ∗ log` source-minimal chain and the balanced-seven
polarization algebra

**ERDŐS #287 REMAINS OPEN.**  Nothing in V15 proves it, and nothing in V15 proves any
analytic estimate.  The new material is finite/algebraic only:

```
Λ = μ ∗ log                                   PROVED_ALGEBRAIC   (Part 1)
  -> exact affine μ-log source at 2mn+s       PROVED_ALGEBRAIC   (Part 2)
  -> small-q / small-r / hard(q,r) partition  PROVED_FINITE      (Part 3)
  -> q r = 2 m n + s                          PROVED_ALGEBRAIC   (Part 3/4)
  -> determinant-one affine line (iff)        PROVED_ALGEBRAIC   (Part 4)
  -> exponent / short-line ledger             EXPONENT CORE ONLY (Part 5)
  -> balanced-seven binomial certificate      PROVED_FINITE      (Part 6)
  -> repeated-prime finite router             FINITE/EXPONENT    (Part 7)
  -> squarefree labelled polarization         PROVED_ALGEBRAIC   (Part 8)
  -> squarefree multiplicative encoding       FINITE INTERFACE   (Part 9)
  -> analytic interfaces                      UNINHABITED        (Part 10)
```

## V14 status hierarchy (preserved, not weakened)

Every V14 theorem is untouched and still compiles.  The V14 Vaughan route is **valid**; it
is merely no longer the *source-minimal* controlling route, because `Λ = μ ∗ log` needs no
truncation parameters `U, V` and no `ζ` factor.  Nothing in V14 is claimed to be false.

```
AFFINE287-VAUGHAN-PRIME-SOURCE45        VALID ALTERNATIVE SOURCE / NONMINIMAL CONTROLLING ROUTE
AFFINE287-PRIME-MODULUS-MU-TWOOUTER45   OPEN ALTERNATIVE CHILD, NOT CONTROLLING
AFFINE287-MULOG-IDENTITY45              PROVED_ALGEBRAIC
AFFINE287-MULOG-SOURCE45                PROVED_ALGEBRAIC
AFFINE287-MULOG-HARD-PARTITION45        PROVED_FINITE/ALGEBRAIC
AFFINE287-LINE-DICHOTOMY45              EXPONENT CORE PROVED; ANALYTIC SHORT-LINE ROUTER EXTERNAL
AFFINE287-SHORTLINE-MR-ROUTER45         EXPONENT_CORE_PROVED / ANALYTIC_SUMMATION_EXTERNAL
BALANCED7_CERTIFICATE_BINOMIAL          PROVED_FINITE
BALANCED7-REPEATED-PRIME45              FINITE/EXPONENT CORE PROVED
BALANCED7-SQUAREFREE-POLARIZATION45     PROVED_ALGEBRAIC
AFFINE287-POLARIZED-OMEGA7-SIGNED-EOD45 OPEN_ANALYTIC
AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45  SOURCE_OPEN
ERDOS287                                OPEN
```

## Hostile checks

1. **Genuine arithmetic functions.**  `vonMangoldt_eq_mobius_mul_log` is stated for
   Mathlib's `ArithmeticFunction.vonMangoldt`, `ArithmeticFunction.moebius`,
   `ArithmeticFunction.log`, `ArithmeticFunction.zeta`; it is derived by ring algebra from
   `coe_moebius_mul_coe_zeta` and `vonMangoldt_mul_zeta`, and
   `vonMangoldt_eq_mobius_mul_log_agrees` checks by `rfl` that it *is* Mathlib's
   `moebius_mul_log_eq_vonMangoldt`.  No fresh schematic `Λ` or `μ` was created.
2. **Coefficientwise identity exact.**  `vonMangoldt_eq_sum_antidiagonal` is an equality of
   real numbers over `Nat.divisorsAntidiagonal`, obtained from
   `ArithmeticFunction.mul_apply`; `vonMangoldt_eq_sum_divisors` is its divisor form.
3. **Three-way partition.**  `pairClass_exhaustive`, `pairClass_union` (exhaustive) and
   `pairClass_disjoint_QR/QH/RH` (pairwise disjoint); `pair_sum_split` recombines an
   arbitrary weighted pair sum in any `AddCommMonoid`.
4. **No illegal `Nat` subtraction for `s = −1`.**  The V14 firewall is reused verbatim:
   `affineNat minus m n` enters statements only through `affineNat_cast` (hypotheses
   `1 ≤ m`, `1 ≤ n`), e.g. in `pairHard_affine_det_one` and `muLogAffineSource_arg`.
5. **Line parameterisation is an iff with multiplicity one.**  `affine_mulog_line_iff`
   (both directions) and `affine_mulog_line_parameter_unique`.
6. **`gcd(r, 2m) = 1` really follows from the unit shift.**  `affine_mulog_coprime` exhibits
   the Bézout pair explicitly from `q r − 2 m n = ±1`; `affine_mulog_r_ne_zero` is *proved*
   (a vanishing `r` would make the left side even), not assumed.
7. **V14 untouched.**  No V14 file was edited; only import lines were added to
   `RequestProject/Main.lean`.
8. **Vaughan is valid but nonminimal**, never "false"; see the hierarchy above.
9. **No analytic `O`-estimate is promoted.**  Part 5 contains only rational exponent
   arithmetic (`mulog_delta0_pos`, `mulog_shortLine_exponent_eq`,
   `mulog_shortLine_exponent_lt_one`).  There is no theorem asserting a bound on any
   analytic sum.
10. **`−20` is binomial only.**  `balancedSeven_lowSum_eq_neg20` is
    `∑_{j<4} (−1)^j C(7,j) = −20`, derived from the banked partial alternating binomial
    identity.  No `H(n)` and no physical Ford source is instantiated.
11. **Repeated-prime negligibility is not claimed.**  Part 7 proves only
    `repeatedPrime_image_card_le_six` and `repeatedPrime_exponent_lt_one` (`6/7 < 1`).
12. **Exact permutation multiplicity.**  `coeff_balanced_eq_perm_sum` sums over
    `Equiv.Perm (Fin n)` once per permutation; the labelling-to-permutation step is the
    `iff` `degreeVector_eq_balanced_iff` and the bijection is `Finset.sum_nbij` with
    injectivity `Equiv.coe_fn_injective`.
13. **`7^7` normalisation correct.**  `sevenPow_seven : 7^7 = 823543` and
    `coeff_balancedSeven_scaled_seventh` (factor `1/823543`), kept separate from the
    permutation identity (`coeff_balanced_scaled`).
14. **No arbitrary 1-bounded enlargement** is introduced anywhere in V15.
15. **No DGS / Pascadi / Bombieri–Vinogradov theorem is assumed or stated.**
16. **Comparison low-conductor matching remains open**: `MuLogComparisonLowCondMatch` below
    is never inhabited.
17. **No Gate1A/Gate1B theorem** is declared to cover any residual.
18. **No `WindowPairSupply` theorem** is fabricated.
19. **No FCL theorem** is fabricated.
20. **No Erdős #287 solution theorem** is declared.  `ERDOS287 : OPEN`.

## Verdict

`ERDOS287_V15_MULOG_POLARIZATION_SAFE_BANK`, with `ERDOS287: OPEN` and the first
uninhabited analytic interfaces `AFFINE287-POLARIZED-OMEGA7-SIGNED-EOD45` and
`AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace V15Status

/-! ## Part 10 — the analytic interfaces, stated and left uninhabited -/

/-- **`AFFINE287-POLARIZED-OMEGA7-SIGNED-EOD45`** — `OPEN_ANALYTIC`.

The signed exponent-of-distribution statement for the polarized seven-fold weight.  It is
a *specification only*: no inhabitant is provided anywhere in this project, and none may be
provided without a genuine analytic proof (Bombieri–Vinogradov at `Q = X^{3/5}`, DGS
endpoint, Pascadi at `y = X^{1/7}`, horizontal Kuznetsov saving and sevenfold character
large-value saving are all **not** assumed here). -/
structure PolarizedOmega7SignedEoD (X Q E S : ℝ) : Prop where
  /-- Asymptotic regime. -/
  X_gt_one : 1 < X
  /-- The modulus range. -/
  Q_le : 1 ≤ Q
  /-- **The open analytic estimate.** -/
  bound : |S| ≤ E

/-- **`AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45`** — `SOURCE_OPEN`.

The statement that the hard `μ`-log source matches its comparison model up to the admitted
error.  Source-blocked: the comparison object is not formalised in this repository, so this
interface is never inhabited. -/
structure MuLogComparisonLowCondMatch (X hard model err : ℝ) : Prop where
  /-- Asymptotic regime. -/
  X_gt_one : 1 < X
  /-- **The open matching statement.** -/
  matched : |hard - model| ≤ err

/-! ## Axiom audit for the principal new theorems -/

section AxiomAudit

open Erdos287.MuLog
open Erdos287.BalancedSeven

-- Part 1
#print axioms Erdos287.MuLog.muLog_identity_abstract
#print axioms Erdos287.MuLog.vonMangoldt_eq_mobius_mul_log
#print axioms Erdos287.MuLog.vonMangoldt_eq_sum_antidiagonal
#print axioms Erdos287.MuLog.vonMangoldt_eq_sum_divisors

-- Part 2
#print axioms Erdos287.MuLog.muLog_affine_pointwise
#print axioms Erdos287.MuLog.muLogAffineSource_eq
#print axioms Erdos287.MuLog.muLogAffineSource_arg

-- Part 3
#print axioms Erdos287.MuLog.pairClass_exhaustive
#print axioms Erdos287.MuLog.pairClass_union
#print axioms Erdos287.MuLog.pairClass_disjoint_QR
#print axioms Erdos287.MuLog.pairClass_disjoint_QH
#print axioms Erdos287.MuLog.pairClass_disjoint_RH
#print axioms Erdos287.MuLog.pair_sum_split
#print axioms Erdos287.MuLog.mulog_sum_eq_smallQ_add_smallR_add_hard
#print axioms Erdos287.MuLog.mulog_affine_sum_eq_smallQ_add_smallR_add_hard
#print axioms Erdos287.MuLog.pairHard_affine_det_one

-- Part 4
#print axioms Erdos287.MuLog.affine_mulog_r_ne_zero
#print axioms Erdos287.MuLog.affine_mulog_q_ne_zero
#print axioms Erdos287.MuLog.affine_mulog_coprime
#print axioms Erdos287.MuLog.affine_mulog_coprime_symm
#print axioms Erdos287.MuLog.affine_mulog_line_forward
#print axioms Erdos287.MuLog.affine_mulog_line_reverse
#print axioms Erdos287.MuLog.affine_mulog_line_iff
#print axioms Erdos287.MuLog.affine_mulog_line_parameter_unique

-- Part 5
#print axioms Erdos287.MuLog.mulog_delta0_pos
#print axioms Erdos287.MuLog.mulog_shortLine_exponent_eq
#print axioms Erdos287.MuLog.mulog_shortLine_exponent_lt_one

-- Parts 6, 7, 9
#print axioms Erdos287.BalancedSeven.balancedSeven_lowSum_eq_neg20
#print axioms Erdos287.BalancedSeven.repeatedPrime_image_card_le_six
#print axioms Erdos287.BalancedSeven.repeatedPrime_exponent_lt_one
#print axioms Erdos287.BalancedSeven.SquarefreeEncoding.map_prod_primes
#print axioms Erdos287.BalancedSeven.SquarefreeEncoding.map_prod_seven_primes

-- Part 8
#print axioms Erdos287.BalancedSeven.coeff_balanced_eq_perm_sum
#print axioms Erdos287.BalancedSeven.coeff_balancedSeven_eq_perm_sum
#print axioms Erdos287.BalancedSeven.coeff_balanced_scaled
#print axioms Erdos287.BalancedSeven.coeff_balancedSeven_scaled_seventh

end AxiomAudit

end V15Status
end Erdos287
