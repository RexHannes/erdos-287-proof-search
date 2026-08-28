import Mathlib
import RequestProject.Erdos287.CharacterGram3221
import RequestProject.Erdos287.FactorialEndpoint3221Adapter

/-!
# V19, Phase I — the conditional high-conductor Balanced7 compiler

`3221-FIRST-CAUCHY-PREFACTOR-CERTIFICATE45 : PROVED_ALGEBRAIC`
`3221-HIGHCOND-BALANCED7-COMPILER45 : CONDITIONAL_COMPILER (Lean-proved)`
`AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45 : SOURCE_OPEN / UNINHABITED (unchanged)`
`BALANCED7 : OPEN`

The strongest purely logical compiler justified by the V19 objects is

```
first-Cauchy prefactor certificate            (PROVED_ALGEBRAIC, realisable)
  + InverseSampledHighCondLogVar3221Input     (OPEN_ANALYTIC, never inhabited)
      ⇒ high-conductor source bound  |S| ≤ E   (explicit logarithmic budget)

  + MuLogComparisonLowCondMatch               (SOURCE_OPEN,   never inhabited)
      ⇒ BalancedSevenPacketInput               (V16 compiler, reused unchanged)
```

The logarithmic budget is kept **explicit** throughout: the saving enters as the positive
parameter `Lsave`, and the admissible error `E` is tied to it by the visible hypothesis
`prefactor · (naturalScale / Lsave) ≤ E²`.  There is no hidden "sufficiently large".

The comparison interface is untouched and remains independent: it is *not* inhabited here,
and the two error channels stay separate (`E + err`, never merged).

**Nothing in this file inhabits any analytic or source antecedent**, so no unconditional
conclusion is obtained anywhere.  Erdős #287 remains OPEN; Balanced7 remains OPEN.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators

namespace Erdos287
namespace V19Compiler

open Erdos287.HighCond3221

/-! ## §17a. The first-Cauchy prefactor certificate -/

/-- **`CauchyPrefactor3221Certificate`** — `PROVED_ALGEBRAIC`, realisable.

The output of the first Cauchy step: the squared source value is controlled by the
inverse-sampled high-conductor energy with an explicit nonnegative prefactor.  Unlike the
analytic input below, this certificate is *not* open: it is produced from elementary
Cauchy–Schwarz by `cauchyPrefactor_of_firstCauchy`. -/
structure CauchyPrefactor3221Certificate (D : InverseSampledHighCond3221Data)
    (srcVal prefactor : ℝ) : Prop where
  /-- The prefactor is nonnegative. -/
  prefactor_nonneg : 0 ≤ prefactor
  /-- The post-Cauchy control of the source by the energy. -/
  cauchy : srcVal ^ 2 ≤ prefactor * D.Vhi

/-- **The certificate really is produced by the first Cauchy step.**  `LEAN_PROVED`.

If the source value is `‖∑_q μ(q) X_q‖`, if the prefactor is the (unsigned!) weight sum
`∑_q μ(q)²`, and if the `q`-wise energy of `X` is dominated by the inverse-sampled
high-conductor energy, then the certificate holds.  The `μ`-sign has already been consumed:
only `μ(q)²` appears. -/
theorem cauchyPrefactor_of_firstCauchy (D : InverseSampledHighCond3221Data)
    (mu : ℕ → ℝ) (X : ℕ → ℂ)
    (hEnergy : ∑ q ∈ D.Qbox, ‖X q‖ ^ 2 ≤ D.Vhi) :
    CauchyPrefactor3221Certificate D ‖∑ q ∈ D.Qbox, (mu q : ℂ) * X q‖
      (∑ q ∈ D.Qbox, mu q ^ 2) := by
  have hpre : 0 ≤ ∑ q ∈ D.Qbox, mu q ^ 2 :=
    Finset.sum_nonneg fun q _ => sq_nonneg _
  refine ⟨hpre, ?_⟩
  have h1 := firstCauchy_sign_consumption D.Qbox mu X
  have h2 : (∑ q ∈ D.Qbox, mu q ^ 2) * (∑ q ∈ D.Qbox, ‖X q‖ ^ 2)
      ≤ (∑ q ∈ D.Qbox, mu q ^ 2) * D.Vhi :=
    mul_le_mul_of_nonneg_left hEnergy hpre
  linarith

/-! ## §17b. The high-conductor compiler, with an explicit logarithmic budget -/

/-- **`highCond_source_bound_of_logVar`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

Cauchy prefactor certificate **+** the open inverse-sampled high-conductor variance input
⇒ the squared source bound `prefactor · naturalScale / Lsave`.  The saving `Lsave` remains
completely explicit. -/
theorem highCond_source_bound_of_logVar {D : InverseSampledHighCond3221Data}
    {srcVal prefactor naturalScale Lsave : ℝ}
    (hcert : CauchyPrefactor3221Certificate D srcVal prefactor)
    (hin : InverseSampledHighCondLogVar3221Input D naturalScale Lsave) :
    srcVal ^ 2 ≤ prefactor * (naturalScale / Lsave) := by
  have h := mul_le_mul_of_nonneg_left hin.variance_bound hcert.prefactor_nonneg
  exact le_trans hcert.cauchy h

/-- The absolute-value form, against an explicitly budgeted admissible error `E`. -/
theorem highCond_source_abs_bound {D : InverseSampledHighCond3221Data}
    {srcVal prefactor naturalScale Lsave E : ℝ}
    (hcert : CauchyPrefactor3221Certificate D srcVal prefactor)
    (hin : InverseSampledHighCondLogVar3221Input D naturalScale Lsave)
    (hE : 0 ≤ E) (hbudget : prefactor * (naturalScale / Lsave) ≤ E ^ 2) :
    |srcVal| ≤ E := by
  have h1 : srcVal ^ 2 ≤ E ^ 2 :=
    le_trans (highCond_source_bound_of_logVar hcert hin) hbudget
  nlinarith [sq_abs srcVal, abs_nonneg srcVal, hE]

/-! ## §18. The conditional Balanced7 chain

The comparison interface is reused unchanged and stays uninhabited; the second step is the
already-banked V16 implication, not duplicated here. -/

/-- **`factorialEndpoint_of_highCondLogVar`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

Cauchy prefactor certificate + high-conductor variance input + explicit budget
⇒ the V16 factorial signed endpoint interface, for the *same* source value. -/
theorem factorialEndpoint_of_highCondLogVar {D : InverseSampledHighCond3221Data}
    {X Q srcVal prefactor naturalScale Lsave E : ℝ}
    (hX : 1 < X) (hQ : Q = X ^ (3 / 5 : ℝ))
    (hcert : CauchyPrefactor3221Certificate D srcVal prefactor)
    (hin : InverseSampledHighCondLogVar3221Input D naturalScale Lsave)
    (hE : 0 ≤ E) (hbudget : prefactor * (naturalScale / Lsave) ≤ E ^ 2) :
    Erdos287.V16Status.FactorialOmega7SignedEndpoint X Q srcVal E :=
  ⟨hX, hQ, highCond_source_abs_bound hcert hin hE hbudget⟩

/-- **`balancedSeven_of_highCondLogVar`** — the new V19 conditional compiler.
`CONDITIONAL_COMPILER / LEAN_PROVED`.

high-conductor analytic input **+** physical low/principal/exceptional comparison
⇒ the V16 balanced-seven packet input, with the two error channels kept separate.

Both antecedents are uninhabited interfaces, so this theorem inhabits nothing and
`BALANCED7` stays `OPEN`. -/
theorem balancedSeven_of_highCondLogVar {D : InverseSampledHighCond3221Data}
    {X Q srcVal Sphys prefactor naturalScale Lsave E err : ℝ}
    (hX : 1 < X) (hQ : Q = X ^ (3 / 5 : ℝ))
    (hcert : CauchyPrefactor3221Certificate D srcVal prefactor)
    (hin : InverseSampledHighCondLogVar3221Input D naturalScale Lsave)
    (hE : 0 ≤ E) (hbudget : prefactor * (naturalScale / Lsave) ≤ E ^ 2)
    (hcomp : Erdos287.V15Status.MuLogComparisonLowCondMatch X Sphys srcVal err) :
    Erdos287.V16Status.BalancedSevenPacketInput X Sphys (E + err) :=
  Erdos287.V16Status.balancedSeven_of_factorialEndpoint_and_comparison
    (factorialEndpoint_of_highCondLogVar hX hQ hcert hin hE hbudget) hcomp

/-! ## §19. Non-circularity / non-automaticity

No compiler above proves its own analytic antecedent.  The high-conductor variance input is
refuted by explicit data (`Erdos287.HighCond3221.highCondLogVar_not_automatic`), and the
comparison interface is refuted by explicit data
(`Erdos287.EndpointAdapter3221.comparison_not_automatic`, reused unchanged from V18).  The
remaining endpoint of the chain is refuted here. -/

/-- **`balancedSeven_not_automatic`.**  `LEAN_PROVED`.

The balanced-seven packet conclusion is a genuine restriction: it fails for suitable data,
so the compiler above cannot be made unconditional by choosing convenient parameters. -/
theorem balancedSeven_not_automatic :
    ∃ X S bound : ℝ, 1 < X ∧ ¬ Erdos287.V16Status.BalancedSevenPacketInput X S bound := by
  refine ⟨2, 1, 0, by norm_num, ?_⟩
  intro h
  have := h.bound_le
  rw [abs_one] at this
  norm_num at this

/-- **`cauchyPrefactor_not_automatic`.**  `LEAN_PROVED`.

Even the (algebraically realisable) Cauchy certificate is not vacuous: a positive source
value against a vanishing energy refutes it.  Hence the prefactor certificate carries real
information about the data and is not a free hypothesis. -/
theorem cauchyPrefactor_not_automatic :
    ∃ (D : InverseSampledHighCond3221Data) (srcVal prefactor : ℝ),
      ¬ CauchyPrefactor3221Certificate D srcVal prefactor := by
  refine ⟨probeData, 1, 0, ?_⟩
  intro h
  have := h.cauchy
  rw [probeData_Vhi] at this
  norm_num at this

/-- **The comparison firewall stays independent.**  The V19 chain uses the comparison
interface only as an antecedent; the high-conductor input alone does **not** produce it. -/
theorem comparison_stays_independent :
    ∃ X hard model err : ℝ, 1 < X ∧
      ¬ Erdos287.V15Status.MuLogComparisonLowCondMatch X hard model err :=
  Erdos287.EndpointAdapter3221.comparison_not_automatic

end V19Compiler
end Erdos287
