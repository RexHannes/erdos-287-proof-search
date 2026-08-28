import Mathlib
import RequestProject.Erdos287.Exponent3221Ledger
import RequestProject.Erdos287.BalancedSeven3221Grouping
import RequestProject.Erdos287.SourceAssistedDiagonal3221
import RequestProject.Erdos287.OffDiagonal3221
import RequestProject.Erdos287.EHNoWrap3221
import RequestProject.Erdos287.DIKuznetsov3221Interface
import RequestProject.Erdos287.BalancedSeven3221Compiler
import RequestProject.Status.Erdos287V16Status

/-!
# Erdős #287 — V17 status: the 3221 source-assisted dispersion safe bank

**ERDŐS #287 REMAINS OPEN.**  Nothing in V17 proves it, nor Balanced7, nor the factorial
endpoint, nor the comparison match, nor any Deshouillers–Iwaniec/Kuznetsov estimate.

## 1. What V17 adds (all sorry-free, kernel-checked)

* **`BALANCED7-3221-GROUPING45` — `PROVED_FINITE / PROVED_ALGEBRAIC`.**
  `Erdos287.Grouping3221.sevenfold_regrouping`: the ordered seven-prime sum of the V16
  factorial polarization equals the `1+2+2+2` grouped sum `∑_{e a b c = m} η α β γ` with
  `α, β, γ` the exact prime-restricted Dirichlet convolutions.  The engine is
  `prod_apply_tuples`, the exact expansion of an iterated convolution over ordered tuples,
  so **every convolution multiplicity is retained**.
  Multiplicity firewall: `grouping_not_injective` exhibits two distinct ordered prime
  seven-tuples with identical `(e,m,n,ℓ)`, and `alpha_not_one_bounded` shows `α` can equal
  `2` for unimodular weights, so `α, β, γ` are **not** 1-bounded.  The correct majorant is
  the divisor bound `alpha_norm_le_card_divisors` (`‖α(a)‖ ≤ τ(a)`).
* **`PASCADI41-3221-RANGE-LEDGER` — `PROVED_ALGEBRAIC / CAPACITY_ONLY`.**
  `Erdos287.Ledger3221`: exact ℚ arithmetic for `E = X^{1/7}`, `M = N = L = X^{2/7}`,
  `Q = X^{3/5}`; `E M N L = X`; `H = Q/M = X^{11/35}`; `E H = X^{16/35} < Q` with margin
  `1/7`; `Texp = 4/35`; diagonal margin `2/35`; the range defect `(N L)/Q = X^{-1/35}`; and
  the transcribed margins `1/10, 2/21, 19/35, 4/35, 2/35`.  Pascadi's Theorem 4.1/3.9 is
  **not** formalised and is **not** claimed to fail.
* **`3221-SOURCE-ASSISTED-DIAGONAL45` — `PROVED_FINITE + CAPACITY_ONLY`.**
  `Erdos287.Diagonal3221`: exact fibrewise energy (`fiberwise_energy_le`), the `τ²`
  product-fibre bound (`productFibre_card_le`), the modulus divisor count with its
  load-bearing zero guard (`modulus_divisor_count_le`, `modulus_count_zero_case`) and the
  finite diagonal parent bound (`diagonal_parent_bound`,
  `sourceAssisted_diagonal_finite`).  `D_max` and `D_v` are explicit hypotheses, never
  analytic theorems: hence `CAPACITY_ONLY`, never unconditional.
* **`3221-OFFDIAGONAL-T-RANGE45` — `PROVED_FINITE + CAPACITY_ONLY`.**
  `Erdos287.OffDiag3221`: existence and uniqueness of the integer parameter `t`
  (over `ℤ`, never truncated `ℕ` subtraction), `t ≠ 0` exactly off the diagonal, and the
  finite range `|t| · Q_min ≤ 2 W_max`.  The dyadic layer is only `Texp = 4/35`.
* **`3221-EH-NOWRAP-ENERGY45` — `CONDITIONAL_FINITE` (hostile audit passed, not forced).**
  `Erdos287.EHNoWrap3221`: the unit-sector collision criterion, integer no-wrap rigidity,
  and an *honest* count of the collision quadruples via `ratioCollision_samePrime` and
  `ratioCollision_distinctPrimes_param` (`h₁ = c e₁`, `h₂ = c e₂`), giving
  `#collisions ≤ #E·#H + (#E)²·#C` and hence `ehRatioEnergy_le_explicit`.  At the 3221
  parameters `#C ≈ H/E`, so the total is of the claimed order `E H` — with **no** divisor
  factor and **no** `X^{o(1)}`.  The Pro claim is therefore *not retracted*, but it is
  banked only as `CONDITIONAL_FINITE`: every statement carries the literal no-wrap size
  hypothesis, which the exponent ledger alone does **not** discharge.
* **`3221-COMPLETED-SOURCE-DICTIONARY45` — `SOURCE_OPEN`.**
  A repository-wide search finds **no** completed Fourier/Poisson source, no additive
  character and no `e_q(·)` object anywhere in this project.  The post-Poisson expression
  is therefore *not* created as a theorem;
  `Erdos287.DI3221.BalancedSeven3221CompletedSource` records the required data with
  concrete equalities and support conditions and no free `Prop` field, and no physical
  instance is constructed.
* **`3221-DI-KUZNETSOV-LITERAL-SPLICE45` — `OPEN_ANALYTIC / UNINHABITED`.**
  `Erdos287.DI3221.DIKuznetsov3221Input` states one concrete, source-specific bound
  (`‖O‖ ≤ X^{39/35-η}`) for the completed value of a given dictionary.  It is never
  inhabited, and it is not an `axiom`.
* **Compiler — `CONDITIONAL_COMPILER`.**
  `Erdos287.Compiler3221.factorialEndpoint_of_3221` and `balancedSeven_of_3221`; the second
  step reuses the V16 theorem `balancedSeven_of_factorialEndpoint_and_comparison` unchanged.
  The additional bridge that the 3221 child does not supply is made explicit as the
  SOURCE-OPEN `Endpoint3221Decomposition`, never inhabited.

## 2. Source audit (Phase G)

`AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45 : SOURCE_BLOCKED`.  The physical comparison is
absent from the repository.  Exactly missing: a definition of the physical comparison
sequence `B(n)` (and `4B(n)`), of the physical expected term `M_phys`, of the principal
local density, of the small-conductor subtraction, and of the exceptional-character
convention.  None of these was invented; the V16 linearity theorem
(`factorialPolarization_commutes_linearMap`) remains the only banked statement about the
expected term, and it does not decide `M_fac = M_phys`.

## 3. Ledger

| tag | status |
| --- | --- |
| `OMEGA7-FACTORIAL-EULER-POLARIZATION45` | `PROVED_ALGEBRAIC` (V16) |
| `POLARIZED-EXPECTED-TERM-LINEARITY45` | `PROVED_ALGEBRAIC` (V16) |
| `BALANCED7-3221-GROUPING45` | `PROVED_FINITE` |
| `PASCADI41-3221-RANGE-LEDGER` | `PROVED_ALGEBRAIC / CAPACITY_ONLY` |
| `3221-SOURCE-ASSISTED-DIAGONAL45` | `PROVED_FINITE + CAPACITY_ONLY` |
| `3221-OFFDIAGONAL-T-RANGE45` | `PROVED_FINITE + CAPACITY_ONLY` |
| `3221-EH-NOWRAP-ENERGY45` | `CONDITIONAL_FINITE` |
| `3221-COMPLETED-SOURCE-DICTIONARY45` | `SOURCE_OPEN` |
| `3221-DI-KUZNETSOV-LITERAL-SPLICE45` | `OPEN_ANALYTIC` |
| `AFFINE287-FACTORIAL-OMEGA7-SIGNED-ENDPOINT45` | `OPEN_ANALYTIC` |
| `AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45` | `SOURCE_BLOCKED` |
| `AFFINE287-BALANCED7-MODULUS-AVERAGE45` | `OPEN_ANALYTIC` (no new content in V17) |
| `BALANCED7` | `CONDITIONAL / OPEN` |
| `ERDOS287` | `OPEN` |
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace V17Status

/-! ## Axiom audit for the principal new theorems -/

section AxiomAudit

-- Phase A: the labelled regrouping
#print axioms Erdos287.Grouping3221.block_card_sum
#print axioms Erdos287.Grouping3221.blocks_disjoint
#print axioms Erdos287.Grouping3221.blocks_cover
#print axioms Erdos287.Grouping3221.grouped_product_eq
#print axioms Erdos287.Grouping3221.grouping_not_injective
#print axioms Erdos287.Grouping3221.mem_tuples
#print axioms Erdos287.Grouping3221.prod_apply_tuples
#print axioms Erdos287.Grouping3221.alpha_apply_prime_pairs
#print axioms Erdos287.Grouping3221.beta_apply_prime_pairs
#print axioms Erdos287.Grouping3221.gamma_apply_prime_pairs
#print axioms Erdos287.Grouping3221.sevenfold_tuples_eq_ordFact
#print axioms Erdos287.Grouping3221.sevenfold_regrouping
#print axioms Erdos287.Grouping3221.tuples_four_product
#print axioms Erdos287.Grouping3221.alpha_norm_le_card_divisors
#print axioms Erdos287.Grouping3221.alpha_not_one_bounded

-- Phase A: the exponent ledger
#print axioms Erdos287.Ledger3221.exponents_sum_one
#print axioms Erdos287.Ledger3221.Wexp_sub_Qexp
#print axioms Erdos287.Ledger3221.Hexp_eq
#print axioms Erdos287.Ledger3221.Eexp_add_Hexp
#print axioms Erdos287.Ledger3221.Eexp_add_Hexp_lt_Qexp
#print axioms Erdos287.Ledger3221.noWrap_margin
#print axioms Erdos287.Ledger3221.Texp_eq
#print axioms Erdos287.Ledger3221.diagonal_amplitude_margin
#print axioms Erdos287.Ledger3221.range_defect
#print axioms Erdos287.Ledger3221.margin_Q_half
#print axioms Erdos287.Ledger3221.margin_two_thirds
#print axioms Erdos287.Ledger3221.margin_three_four
#print axioms Erdos287.Ledger3221.margin_one_minus_Q
#print axioms Erdos287.Ledger3221.margin_two_two
#print axioms Erdos287.Ledger3221.diagonal_exponent_identity
#print axioms Erdos287.Ledger3221.diagonal_exponent_value

-- Phase B: the source-assisted diagonal
#print axioms Erdos287.Diagonal3221.fiberwise_energy_le
#print axioms Erdos287.Diagonal3221.productFibre_card_le
#print axioms Erdos287.Diagonal3221.pushforward_energy_le
#print axioms Erdos287.Diagonal3221.modulus_divisor_count_le
#print axioms Erdos287.Diagonal3221.modulus_count_zero_case
#print axioms Erdos287.Diagonal3221.congr_iff_dvd
#print axioms Erdos287.Diagonal3221.modulus_count_physical_le
#print axioms Erdos287.Diagonal3221.diagonalParent_eq
#print axioms Erdos287.Diagonal3221.diagonal_parent_bound
#print axioms Erdos287.Diagonal3221.sourceAssisted_diagonal_finite

-- Phase C: the off-diagonal parameter
#print axioms Erdos287.OffDiag3221.offdiag_existsUnique_t
#print axioms Erdos287.OffDiag3221.offdiag_t_ne_zero
#print axioms Erdos287.OffDiag3221.offdiag_ne_of_t_ne_zero
#print axioms Erdos287.OffDiag3221.offdiag_abs_t_le
#print axioms Erdos287.OffDiag3221.offdiag_abs_t_le_div

-- Phase D: no-wrap and the ratio-fibre energy audit
#print axioms Erdos287.EHNoWrap3221.ratio_eq_iff_cross
#print axioms Erdos287.EHNoWrap3221.ratio_eq_iff_cross_zmod
#print axioms Erdos287.EHNoWrap3221.nowrap_eq_of_dvd_of_abs_lt
#print axioms Erdos287.EHNoWrap3221.nowrap_cross_eq
#print axioms Erdos287.EHNoWrap3221.eh_lt_q_capacity
#print axioms Erdos287.EHNoWrap3221.ratioCollision_samePrime
#print axioms Erdos287.EHNoWrap3221.ratioCollision_distinctPrimes_param
#print axioms Erdos287.EHNoWrap3221.ratioCollision_param_div
#print axioms Erdos287.EHNoWrap3221.cBox_card
#print axioms Erdos287.EHNoWrap3221.ratioCollision_card_bound
#print axioms Erdos287.EHNoWrap3221.card_collision_eq_sum_sq
#print axioms Erdos287.EHNoWrap3221.energy_le_collision_card
#print axioms Erdos287.EHNoWrap3221.ehRatioEnergy_le_explicit

-- Phase E: dictionary and socket
#print axioms Erdos287.DI3221.BalancedSeven3221CompletedSource.parent_norm_le
#print axioms Erdos287.DI3221.BalancedSeven3221CompletedSource.t_range_of_source
#print axioms Erdos287.DI3221.preSplice_target_gap
#print axioms Erdos287.DI3221.slot_dependence_counterguard
#print axioms Erdos287.DI3221.zeroMode_separation_guard
#print axioms Erdos287.DI3221.modulus_factorisation_not_unique

-- Phase F: the compiler
#print axioms Erdos287.Compiler3221.factorialEndpoint_of_3221
#print axioms Erdos287.Compiler3221.balancedSeven_of_3221
#print axioms Erdos287.Compiler3221.regrouping_is_unconditional

end AxiomAudit

/-! ## The two analytic/source antecedents are types, not theorems -/

section Uninhabited

#check @Erdos287.DI3221.DIKuznetsov3221Input
#check @Erdos287.Compiler3221.Endpoint3221Decomposition
#check @Erdos287.V16Status.FactorialOmega7SignedEndpoint
#check @Erdos287.V15Status.MuLogComparisonLowCondMatch

end Uninhabited

end V17Status
end Erdos287
