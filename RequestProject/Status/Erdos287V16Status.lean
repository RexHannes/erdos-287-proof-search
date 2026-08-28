import Mathlib
import RequestProject.Erdos287.FactorialEulerPolarization
import RequestProject.Erdos287.FactorialEulerLocal
import RequestProject.Erdos287.FactorialPolarizationLinearity
import RequestProject.Erdos287.PascadiParameterLedger
import RequestProject.Status.Erdos287V15Status

/-!
# Erdős #287 — V16 status: the factorial Euler polarization bank

**ERDŐS #287 REMAINS OPEN.**  Nothing in V16 proves it, nor the balanced-seven packet, nor
any exponent-of-distribution statement, nor Pascadi's theorem, nor its negation.

## 1. Retirement of a superseded controlling claim

The V15 working note *"complete multiplicativity is required for the polarized seven-box
encoding"* is **retired as controlling**.  It is not deleted from the repository and no V15
theorem is weakened or removed: `Erdos287.BalancedSeven.SquarefreeEncoding` and the
squarefree labelled polarization `coeff_balanced_eq_perm_sum` remain exactly as proved, and
remain valid mathematics.  What changes is only the *status label*: the squarefree
restriction is no longer the obstruction of record, because the factorial (divided-power)
polarization of Part 2 handles repeated primes directly.

## 2. What is newly proved (all sorry-free, kernel-checked)

* `Erdos287.FactorialEuler.factorialEulerPolarization` and
  `factorialEulerPolarization_seven`: for `F_z(p^e) = a_z(p)^e/e!` extended
  multiplicatively and `a_z(p) = (1/7) ∑_i z_i ω_i(p)`,

  `7^7 · [z_1 ⋯ z_7] F_z(n) = ∑_{p_1 ⋯ p_7 = n, ordered} ∏_i ω_i(p_i)`   for `Ω(n) = 7`,

  **including repeated primes**; the factorials cancel exactly the permutations of equal
  prime occurrences (`fiber_card_eq`, via `DomMulAct.stabilizer_card'`), and
  `mem_ordFact_iff` certifies that the right-hand sum is literally over ordered prime
  tuples.  Non-vacuity is witnessed at the extreme repeated case `n = 128 = 2^7`.
  Everything is over a characteristic-zero field (`ℂ` included), never a bare semiring,
  because of the division by `e!`.
* `Erdos287.FactorialEuler.localSeries_eq_rescale_exp` and `derivative_localSeries`: the
  **formal** Euler identity `∑_e F_z(p^e) T^e = exp(a_z(p) T)` and its formal logarithmic
  derivative `d/dT S = a · S`, with the resulting local `Λ`-bookkeeping
  (`localLambda_one`, `localLambda_of_two_le`, `localLambdaSeries_eq_C`).  The `Λ`-data is
  not merely a definition: `localLambdaSeries_unique` and `lambda_coeffs_of_logDeriv` show
  that any family satisfying the formal log-derivative equation *must* be `a` at `e = 1`
  and `0` for `e ≥ 2`.
  **Not** labelled a class-`C` statement: this repository contains no class-`C` definition,
  so per instruction only the finite/formal prime-power coefficient identity is banked.
* `Erdos287.FactorialEuler.factorialPolarization_commutes_linearMap` (+ the arithmetic and
  weighted-projection instances): balanced coefficient extraction commutes with any
  **linear** operator on the coefficient space.  Abstract and conditional: it covers a
  principal-character projection, a finite low-conductor character projection and an
  exceptional-character linear term *as instances*, and decides none of them.
* `Erdos287.PascadiLedger.pascadi_parameter_eta_le_one_div_4000`,
  `one_div_seven_gt_one_div_4000`,
  `pascadi_Q_three_fifths_y_one_seventh_incompatible`: exact rational parameter ledger.
  Pascadi's analytic theorem is **not** formalised and is **not** asserted to fail.

## 3. What stays open

* `FactorialOmega7SignedEndpoint` (`AFFINE287-FACTORIAL-OMEGA7-SIGNED-ENDPOINT45`):
  `OPEN_ANALYTIC`, never inhabited.  It replaces V15's
  `PolarizedOmega7SignedEoD` as the controlling analytic interface; the V15 structure is
  kept in place, also uninhabited.
* `Erdos287.V15Status.MuLogComparisonLowCondMatch`
  (`AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45`): `SOURCE_BLOCKED / OPEN`, never inhabited.
  The new polarization proves compatibility with **linear** expected-term operators only;
  it does **not** prove `M_fac = M_phys`.
* `BalancedSevenPacketInput`: `CONDITIONAL / OPEN`.  The only theorem about it is the
  compiler `balancedSeven_of_factorialEndpoint_and_comparison`, which is a pure implication
  from the two open inputs; no analytic interface is inhabited anywhere.

## 4. Status ledger

| tag | status |
| --- | --- |
| `OMEGA7-FACTORIAL-EULER-POLARIZATION45` | `PROVED_ALGEBRAIC` |
| `POLARIZED-EXPECTED-TERM-LINEARITY45` | `PROVED_ALGEBRAIC` |
| `PASCADI-Q3/5-Y1/7-PARAMETER-NOGO` | `PROVED_ALGEBRAIC / PARAMETER_LEDGER` |
| `AFFINE287-FACTORIAL-OMEGA7-SIGNED-ENDPOINT45` | `OPEN_ANALYTIC` |
| `AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45` | `SOURCE_BLOCKED / OPEN` |
| `BALANCED7` | `CONDITIONAL / OPEN` |
| `ERDOS287` | `OPEN` |
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace V16Status

/-! ## The new controlling analytic interface, stated and left uninhabited -/

/-- **`AFFINE287-FACTORIAL-OMEGA7-SIGNED-ENDPOINT45`** — `OPEN_ANALYTIC`.

Specification of the signed endpoint estimate for the *factorial* polarized weight:

`∫_{T^7} conj(z_1 ⋯ z_7) ∑_{q ∼ X^{3/5}} μ(q) Δ_E(F_z; X, q, −s/2) dz = o(X / log X)`,

with `S` standing for the value of that integral and `E` for the admitted `o(X/log X)`
budget.  **No inhabitant is provided anywhere in this project**, and none may be provided
without a genuine analytic proof: no Bombieri–Vinogradov at `Q = X^{3/5}`, no DGS endpoint,
no Pascadi input, no Kuznetsov or large-value saving is assumed here. -/
structure FactorialOmega7SignedEndpoint (X Q S E : ℝ) : Prop where
  /-- Asymptotic regime. -/
  X_gt_one : 1 < X
  /-- The endpoint modulus range `Q = X^{3/5}`. -/
  Q_eq : Q = X ^ (3 / 5 : ℝ)
  /-- **The open analytic estimate.** -/
  bound : |S| ≤ E

/-! ## The balanced-seven packet, conditional only -/

/-- The balanced-seven packet input: a bound for the **physical** comparison sequence.
`CONDITIONAL / OPEN` — inhabited only by the compiler below, from two open inputs. -/
structure BalancedSevenPacketInput (X S bound : ℝ) : Prop where
  /-- Asymptotic regime. -/
  X_gt_one : 1 < X
  /-- The admitted total bound. -/
  bound_le : |S| ≤ bound

/-- **Conditional compiler** — `PROVED_COMPILER / CONDITIONAL_ON_OPEN_ANALYTIC_INPUT`.

factorial endpoint analytic input **+** comparison-match input **⇒** balanced-seven packet
input, with the two error channels kept separate (`E + err`, never merged).  Both
antecedents are uninhabited interfaces, so this theorem inhabits nothing. -/
theorem balancedSeven_of_factorialEndpoint_and_comparison {X Q Sfac Sphys E err : ℝ}
    (hend : FactorialOmega7SignedEndpoint X Q Sfac E)
    (hcomp : Erdos287.V15Status.MuLogComparisonLowCondMatch X Sphys Sfac err) :
    BalancedSevenPacketInput X Sphys (E + err) := by
  refine ⟨hend.X_gt_one, ?_⟩
  have h1 : |Sphys - Sfac| ≤ err := hcomp.matched
  have h2 : |Sfac| ≤ E := hend.bound
  have h3 : |Sphys| ≤ |Sphys - Sfac| + |Sfac| := by
    calc |Sphys| = |(Sphys - Sfac) + Sfac| := by ring_nf
      _ ≤ |Sphys - Sfac| + |Sfac| := abs_add_le _ _
  linarith

/-! ## Axiom audit for the principal new theorems -/

section AxiomAudit

open Erdos287.FactorialEuler
open Erdos287.PascadiLedger

-- Part 2: the factorial Euler polarization
#print axioms Erdos287.FactorialEuler.mem_ordFact_iff
#print axioms Erdos287.FactorialEuler.count_eq_factorization
#print axioms Erdos287.FactorialEuler.exists_perm_comp
#print axioms Erdos287.FactorialEuler.image_perm_eq_ordFact
#print axioms Erdos287.FactorialEuler.fiber_card_eq
#print axioms Erdos287.FactorialEuler.factorialEulerPolarization_of_listing
#print axioms Erdos287.FactorialEuler.exists_prime_listing
#print axioms Erdos287.FactorialEuler.factorialEulerPolarization
#print axioms Erdos287.FactorialEuler.Fdiv_primePow
#print axioms Erdos287.FactorialEuler.Fz7_primePow
#print axioms Erdos287.FactorialEuler.Fz7_eq_Fdiv
#print axioms Erdos287.FactorialEuler.factorialEulerPolarization_seven
#print axioms Erdos287.FactorialEuler.factorialEulerPolarization_seven_complex
#print axioms Erdos287.FactorialEuler.const_two_mem_ordFact_128
#print axioms Erdos287.FactorialEuler.factorialEulerPolarization_seven_128

-- Part 3: the local formal Euler algebra
#print axioms Erdos287.FactorialEuler.localSeries_eq_rescale_exp
#print axioms Erdos287.FactorialEuler.derivative_localSeries
#print axioms Erdos287.FactorialEuler.localSeries_ne_zero
#print axioms Erdos287.FactorialEuler.localLambdaSeries_unique
#print axioms Erdos287.FactorialEuler.lambda_coeffs_of_logDeriv
#print axioms Erdos287.FactorialEuler.localLambda_one
#print axioms Erdos287.FactorialEuler.localLambda_of_two_le
#print axioms Erdos287.FactorialEuler.localLambdaSeries_eq_C

-- Part 4: expected-term linearity
#print axioms Erdos287.FactorialEuler.factorialPolarization_commutes_linearMap
#print axioms Erdos287.FactorialEuler.factorialPolarization_commutes_linearMap_seven
#print axioms Erdos287.FactorialEuler.factorialPolarization_commutes_arith
#print axioms Erdos287.FactorialEuler.factorialPolarization_commutes_weightedProjection

-- Part 5: the Pascadi parameter ledger
#print axioms Erdos287.PascadiLedger.pascadi_parameter_eta_le_one_div_4000
#print axioms Erdos287.PascadiLedger.one_div_seven_gt_one_div_4000
#print axioms Erdos287.PascadiLedger.pascadi_Q_three_fifths_y_one_seventh_incompatible
#print axioms Erdos287.PascadiLedger.pascadi_margin_at_one_seventh

-- Part 8: the conditional compiler
#print axioms Erdos287.V16Status.balancedSeven_of_factorialEndpoint_and_comparison

end AxiomAudit

end V16Status
end Erdos287
