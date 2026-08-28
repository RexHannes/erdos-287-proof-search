import Mathlib
import RequestProject.Erdos287.HighConductorSixthMoment3221
import RequestProject.Erdos287.BalancedSevenV19Compiler

/-!
# V20, Phases K / L / Q — the same-`B0` comparison firewall and the Balanced7 compiler

`AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45 : SOURCE_OPEN (unchanged, now B0-indexed)`
`3221-V20-BALANCED7-COMPILER45 : CONDITIONAL_COMPILER (Lean-proved)`
`BALANCED7 : OPEN`

## Contents

* **§31.**  `highConductorCutoff B0 X = (log X)^{B0}` — the cutoff dependence made
  explicit, so that `B0` is *not* free after the fact.
* **§32.**  `MuLogComparisonAtCutoff` — the physical low/principal/exceptional comparison
  interface **indexed by the same cutoff exponent `B0`**, with
  `comparisonAtCutoff_to_base` recovering the unchanged V15 interface and
  `comparisonAtCutoff_not_automatic` showing it is a genuine restriction.  This is the
  load-bearing anti-retuning firewall: the analytic decomposition and the physical
  comparison must be taken at the *same* `B0`.
* **§33.**  `balancedSeven_of_v20_package` — the V20 conditional compiler

  ```
  HHH Gram analytic input
    + routed diagonal / low-quotient / moderate children
    + the exact high-conductor reassembly
    + the same-B0 physical comparison
        ⇒ BalancedSevenPacketInput
  ```

  Every antecedent is either an uninhabited interface or an explicitly discharged finite
  hypothesis; **no antecedent is claimed**.
* **§35 (Phase Q).**  Non-vacuity and anti-circularity: none of the analytic inputs is
  automatic, the log-variance compiler cannot construct the HHH input, and the Balanced7
  compiler cannot construct the comparison.

Erdős #287 remains OPEN; Balanced7 remains OPEN.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace V20Compiler

open Erdos287.HighCond3221 Erdos287.V20HHH Erdos287.V20Router Erdos287.V19Compiler

/-! ## §31. The explicit `B0` cutoff dependence -/

/-- The high-conductor cutoff `Dcut = log^{B0} X`, as an explicit function of the cutoff
exponent `B0` and the scale `X`. -/
noncomputable def highConductorCutoff (B0 X : ℝ) : ℝ := Real.log X ^ B0

/-- Raising the cutoff exponent raises the cutoff, once `log X ≥ 1`: the dependence is
monotone, so a later "sufficiently large `B0`" cannot be smuggled in silently. -/
theorem highConductorCutoff_mono {B0 B1 X : ℝ} (hX : 1 ≤ Real.log X) (h : B0 ≤ B1) :
    highConductorCutoff B0 X ≤ highConductorCutoff B1 X :=
  Real.rpow_le_rpow_of_exponent_le hX h

/-! ## §32. The comparison interface at a fixed cutoff exponent -/

/-- **`MuLogComparisonAtCutoff`** — `SOURCE_OPEN / UNINHABITED`.

The V15 physical comparison interface, now carrying the cutoff data explicitly: the match
is asserted *at the cutoff* `Dcut = log^{B0} X` and at no other.  The underlying open
statement is unchanged. -/
structure MuLogComparisonAtCutoff (X Dcut B0 hard model err : ℝ) : Prop where
  /-- The cutoff exponent is positive. -/
  B0_pos : 0 < B0
  /-- The cutoff is literally `log^{B0} X`. -/
  cutoff_at_B0 : Dcut = highConductorCutoff B0 X
  /-- **The open source statement**, unchanged from V15. -/
  base : Erdos287.V15Status.MuLogComparisonLowCondMatch X hard model err

/-- The `B0`-indexed comparison implies the unchanged V15 interface. -/
theorem comparisonAtCutoff_to_base {X Dcut B0 hard model err : ℝ}
    (h : MuLogComparisonAtCutoff X Dcut B0 hard model err) :
    Erdos287.V15Status.MuLogComparisonLowCondMatch X hard model err := h.base

/-- **`comparisonAtCutoff_not_automatic`.**  `LEAN_PROVED`.

The `B0`-indexed comparison is a genuine restriction. -/
theorem comparisonAtCutoff_not_automatic :
    ∃ X Dcut B0 hard model err : ℝ, ¬ MuLogComparisonAtCutoff X Dcut B0 hard model err := by
  refine ⟨2, 0, 1, 1, 0, -1, ?_⟩
  intro h
  have h1 := h.base.matched
  norm_num at h1

/-- **The cutoff firewall.**  `LEAN_PROVED`.

If the analytic decomposition is taken at cutoff exponent `B0` and the physical comparison
is recorded at cutoff exponent `B0'`, then the two are compatible only when the *cutoff
values agree*; the compiler below therefore may not retune `B0` after the fact. -/
theorem comparison_cutoff_must_match {X Dcut Dcut' B0 hard model err : ℝ}
    (h : MuLogComparisonAtCutoff X Dcut B0 hard model err)
    (hsame : Dcut' = highConductorCutoff B0 X) : Dcut = Dcut' := by
  rw [h.cutoff_at_B0, hsame]

/-! ## §33. The V20 conditional Balanced7 compiler -/

/-- **`balancedSeven_of_v20_package`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

The full V20 dependency:

```
HHH Gram analytic input                    (OPEN_ANALYTIC, uninhabited)
  + diagonal / low-quotient / moderate children within budget
  + the exact four-channel high-conductor reassembly
  + the first-Cauchy prefactor certificate  (algebraically realisable)
  + the same-B0 physical comparison         (SOURCE_OPEN, uninhabited)
        ⇒ BalancedSevenPacketInput
```

Two of the antecedents are never inhabited anywhere in this repository, so this theorem
concludes nothing unconditionally and `BALANCED7` stays `OPEN`. -/
theorem balancedSeven_of_v20_package
    {Dat : InverseSampledHighCond3221Data} {Hdat : HHHGramData}
    {X Q Dcut B0 srcVal Sphys prefactor naturalScale Lsave E err : ℝ}
    {vdiag vlow vmod vhhh bound : ℝ}
    (hX : 1 < X) (hQ : Q = X ^ (3 / 5 : ℝ))
    (hcert : CauchyPrefactor3221Certificate Dat srcVal prefactor)
    (hdec : LogVarChannelDecomposition Dat vdiag vlow vmod vhhh)
    (hscale : 0 < naturalScale) (hL : 0 < Lsave)
    (hdiag : vdiag ≤ naturalScale / (4 * Lsave))
    (hlow : vlow ≤ naturalScale / (4 * Lsave))
    (hmod : vmod ≤ naturalScale / (4 * Lsave))
    (hHHH : HighQuotientFiveBoxShiftedGram3221Input Hdat bound)
    (hchannel : vhhh ≤ ‖hhhGram Hdat‖)
    (hbudget : bound ≤ naturalScale / (4 * Lsave))
    (hE : 0 ≤ E) (hEbudget : prefactor * (naturalScale / Lsave) ≤ E ^ 2)
    (hcomp : MuLogComparisonAtCutoff X Dcut B0 Sphys srcVal err)
    (hcutoff : Dcut = highConductorCutoff B0 X) :
    Erdos287.V16Status.BalancedSevenPacketInput X Sphys (E + err) := by
  have hlogvar : InverseSampledHighCondLogVar3221Input Dat naturalScale Lsave :=
    logVar_of_four_channels hdec hscale hL hdiag hlow hmod hHHH hchannel hbudget
  exact balancedSeven_of_highCondLogVar hX hQ hcert hlogvar hE hEbudget
    (comparisonAtCutoff_to_base hcomp)

/-! ## §35. Non-vacuity and anti-circularity -/

/-- The HHH analytic socket is not automatic (restated at the compiler level). -/
theorem hhh_input_not_automatic_v20 :
    ∃ (Hdat : HHHGramData) (bound : ℝ),
      ¬ HighQuotientFiveBoxShiftedGram3221Input Hdat bound :=
  hhhGram_input_not_automatic

/-- The sixth-moment input is not automatic (restated at the compiler level). -/
theorem sixthMoment_input_not_automatic_v20 :
    ∃ (Qbox : Finset ℕ) (C : (q : ℕ) → ZMod q → ℂ) (Qscale Tscale polylog : ℝ),
      ¬ Erdos287.V20Sixth.HighCondResidueSixthMoment3221Input Qbox C Qscale Tscale polylog :=
  Erdos287.V20Sixth.sixthMoment_input_not_automatic

/-- The comparison is not automatic — the V15/V18 firewall, restated at the `B0`-indexed
interface. -/
theorem comparison_not_automatic_v20 :
    ∃ X Dcut B0 hard model err : ℝ, ¬ MuLogComparisonAtCutoff X Dcut B0 hard model err :=
  comparisonAtCutoff_not_automatic

/-- **The log-variance compiler cannot construct the HHH analytic input.**  `LEAN_PROVED`.

There are data for which the log-variance interface holds while the HHH socket fails, so
the reassembly compiler cannot be closed on itself. -/
theorem logVar_cannot_construct_hhh :
    ∃ (Dat : InverseSampledHighCond3221Data) (naturalScale Lsave : ℝ)
      (Hdat : HHHGramData) (bound : ℝ),
      InverseSampledHighCondLogVar3221Input Dat naturalScale Lsave ∧
        ¬ HighQuotientFiveBoxShiftedGram3221Input Hdat bound :=
  logVar_does_not_construct_hhh

/-- **The Balanced7 compiler cannot construct the comparison.**  `LEAN_PROVED`.

There are data for which the whole analytic side (here: the log-variance interface) holds
while the physical comparison fails.  The comparison channel therefore remains an
independent open source input. -/
theorem balancedSeven_compiler_cannot_construct_comparison :
    ∃ (Dat : InverseSampledHighCond3221Data) (naturalScale Lsave : ℝ)
      (X Dcut B0 hard model err : ℝ),
      InverseSampledHighCondLogVar3221Input Dat naturalScale Lsave ∧
        ¬ MuLogComparisonAtCutoff X Dcut B0 hard model err := by
  refine ⟨probeData, 4, 2, 2, 0, 1, 1, 0, -1, ⟨by norm_num, by norm_num, ?_⟩, ?_⟩
  · rw [probeData_Vhi]; norm_num
  · intro h
    have h1 := h.base.matched
    norm_num at h1

end V20Compiler
end Erdos287
