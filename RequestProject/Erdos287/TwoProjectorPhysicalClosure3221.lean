import Mathlib
import RequestProject.Erdos287.BadCharacterLogLedger3221
import RequestProject.Erdos287.PrimeBoxL1Normalization3221
import RequestProject.Erdos287.BalancedSevenV21Compiler

/-!
# V22, Phase 4 — the physical two-projector closure criterion

`3221-TWO-HIGHPROJECTOR-FIVEBOX-SIEVE45 : CONDITIONAL`

## The closure arithmetic

After the outer Cauchy step, the physical Balanced7 error is controlled by

```
X^{31/70} · (V_hi)^{1/2} · (log X)^{C_ext}
```

so, writing `V_hi ≤ X^{39/35} (log X)^{−C_var}`, the net exponent of `log X` relative to
the trivial size `X / log X` is

```
netLogExponent C_var C_ext  =  −(2 + C_var)/2 + C_ext.
```

The closure requirement is `netLogExponent < −1`, i.e. **exactly**

```
C_var  >  2 · C_ext.
```

`C_var` is supplied by the repaired safe bad-character ledger of
`Erdos287.V22Ledger` (which already charges *two* powers of the cutoff `D`), and `C_ext`
by the physical log-prefactor audit, which is `SOURCE_OPEN`.

Everything in this file is finite rational arithmetic plus one bundling structure.  **No
analytic input is inhabited and no closure is asserted unconditionally.**
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace V22Closure

open Erdos287.V22Ledger
open Erdos287.V21PrimeBox
open Erdos287.V21Sieve
open Erdos287.V21Shiu
open Erdos287.V21Cutoff
open Erdos287.V21Outer
open Erdos287.V21LogBudget
open Erdos287.V22Ford
open Erdos287.V22PrimeBoxL1
open Erdos287.HighCond3221
open Erdos287.V21Compiler

/-! ## §1. The net log exponent -/

/-- The net power of `log X` after the outer Cauchy step and the physical prefactor. -/
def netLogExponent (cvarVal cext : ℚ) : ℚ := -(2 + cvarVal) / 2 + cext

/-- **The closure criterion.**  `netLogExponent < −1` is *equivalent* to `C_var > 2 C_ext`;
there is no slack and no hidden constant. -/
theorem netLogExponent_lt_neg_one_iff (cvarVal cext : ℚ) :
    netLogExponent cvarVal cext < -1 ↔ 2 * cext < cvarVal := by
  unfold netLogExponent
  constructor <;> intro h <;> linarith

/-- **`twoProjector_closes_of_cvar_gt_twoCext`.**  `LEAN_PROVED` (finite arithmetic). -/
theorem twoProjector_closes_of_cvar_gt_twoCext {cvarVal cext : ℚ}
    (h : 2 * cext < cvarVal) : netLogExponent cvarVal cext < -1 :=
  (netLogExponent_lt_neg_one_iff cvarVal cext).2 h

/-! ## §2. Capacity of the repaired ledger, sample by sample -/

/-- At cutoff exponent `B0 = 1` the repaired ledger gives `C_var = 5`, hence closure for
every external log-prefactor exponent with `2 C_ext < 5`. -/
theorem closure_capacity_B0_one {cext : ℚ} (h : 2 * cext < 5) :
    netLogExponent (cvar 1) cext < -1 := by
  rw [cvar_at_one]
  exact twoProjector_closes_of_cvar_gt_twoCext h

/-- At cutoff exponent `B0 = 2` the repaired ledger gives `C_var = 2`: the capacity has
shrunk to `C_ext < 1`. -/
theorem closure_capacity_B0_two {cext : ℚ} (h : cext < 1) :
    netLogExponent (cvar 2) cext < -1 := by
  rw [cvar_at_two]
  exact twoProjector_closes_of_cvar_gt_twoCext (by linarith)

/-- At cutoff exponent `B0 = 3` the repaired safe count has eaten the whole budget:
`C_var = −2 < 0`, so **no** nonnegative `C_ext` closes.  This is the concrete cost of the
`D²` repair and the reason no compiler may assume a single power of `D`. -/
theorem closure_fails_B0_three {cext : ℚ} (h : 0 ≤ cext) :
    ¬ netLogExponent (cvar 3) cext < -1 := by
  rw [cvar_at_three, netLogExponent_lt_neg_one_iff]
  push_neg
  linarith

/-- The zero-prefactor case: with `C_ext = 0` the route closes exactly when `C_var > 0`. -/
theorem closure_at_zero_prefactor (cvarVal : ℚ) :
    netLogExponent cvarVal 0 < -1 ↔ 0 < cvarVal := by
  rw [netLogExponent_lt_neg_one_iff]; constructor <;> intro h <;> linarith

/-! ## §3. The bundled physical inputs -/

/-- **`TwoProjectorPhysical3221Inputs`** — `CONDITIONAL / UNINHABITED`.

The physical layer of the V21/V22 two-projector route.  Every field is either an
uninhabited source/analytic interface, or finite arithmetic already proved.

In particular the `ledger` field is the *only* place the log budget is asserted, and it is
asserted in the repaired form `C_var(B0) > 2 C_ext` with `C_var` computed from the safe
`(D+1)²` bad-character count. -/
structure TwoProjectorPhysical3221Inputs
    (Dat : InverseSampledHighCond3221Data)
    (F : Ford723CoefficientData) (Pdat : PrimeBoxData) (C1 Y : ℝ)
    (Sdat : ShortShiftSieveData)
    (Wprime : ℕ) (s : ℤ) (Mbox : Finset ℕ) (M X Cshiu : ℝ)
    (P1 P2 MboxOuter : Finset ℕ) (w1 w2 : ℕ → ℂ) (Couter : ℝ)
    (B0 : ℕ) (Dana Dphys : ℝ) (unaccounted lowResidual : ℝ → ℝ)
    (cext : ℚ)
    (naturalScale Lsave vAA vBA vAB vBB : ℝ) : Prop where
  /-- The source dictionary for the physical `ω_i` (SOURCE_OPEN). -/
  dictionary : BalancedSevenOmegaFord723Adapter3221 F Pdat
  /-- The prime-box cardinality input (external prime counting). -/
  primeCount : PrimeBoxCardinality3221Input Pdat C1 Y
  /-- The external short-shift rough sieve input. -/
  sieve : ShortShiftRoughSieve3221Input Sdat
  /-- The external Shiu divisor-average input. -/
  shiu : ShiuLinearDivisorAverage3221Input Wprime s Mbox M X Cshiu
  /-- The outer two-prime `L²` input. -/
  outerL2 : OuterTwoPrimeL2Normalization3221Input P1 P2 MboxOuter w1 w2 M X Couter
  /-- The shared-cutoff compatibility firewall at the *same* `B0`. -/
  cutoff : HighProjectorCutoffCompat3221 X B0 Dana Dphys unaccounted lowResidual
  /-- The repaired symbolic log ledger closes: `C_var(B0) > 2 C_ext`. -/
  ledger : 2 * cext < cvar B0
  /-- The numeric budget layer transporting the ledger to the four channels. -/
  budget : TwoHighProjector3221ClosureInputs Dat naturalScale Lsave vAA vBA vAB vBB

/-- **`twoProjectorPhysical3221_closes_logVar`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

The physical package yields both the log-variance interface *and* the strict closure
inequality on the net log exponent.  There is no inhabitant. -/
theorem twoProjectorPhysical3221_closes_logVar
    {Dat : InverseSampledHighCond3221Data}
    {F : Ford723CoefficientData} {Pdat : PrimeBoxData} {C1 Y : ℝ}
    {Sdat : ShortShiftSieveData}
    {Wprime : ℕ} {s : ℤ} {Mbox : Finset ℕ} {M X Cshiu : ℝ}
    {P1 P2 MboxOuter : Finset ℕ} {w1 w2 : ℕ → ℂ} {Couter : ℝ}
    {B0 : ℕ} {Dana Dphys : ℝ} {unaccounted lowResidual : ℝ → ℝ}
    {cext : ℚ}
    {naturalScale Lsave vAA vBA vAB vBB : ℝ}
    (h : TwoProjectorPhysical3221Inputs Dat F Pdat C1 Y Sdat Wprime s Mbox M X Cshiu
      P1 P2 MboxOuter w1 w2 Couter B0 Dana Dphys unaccounted lowResidual cext
      naturalScale Lsave vAA vBA vAB vBB) :
    InverseSampledHighCondLogVar3221Input Dat naturalScale Lsave ∧
      netLogExponent (cvar B0) cext < -1 :=
  ⟨twoHighProjector3221_closes_logVar h.budget,
    twoProjector_closes_of_cvar_gt_twoCext h.ledger⟩

/-- **`twoProjectorPhysical3221_supplies_primeBoxL1`.**  `LEAN_PROVED` (conditional).

The physical package does supply the prime-box `L¹` normalisation — but only because it
*assumes* the source dictionary and the prime-counting input.  This is recorded so that
the `L¹` bound is never mistaken for something the compiler proves. -/
theorem twoProjectorPhysical3221_supplies_primeBoxL1
    {Dat : InverseSampledHighCond3221Data}
    {F : Ford723CoefficientData} {Pdat : PrimeBoxData} {C1 Y : ℝ}
    {Sdat : ShortShiftSieveData}
    {Wprime : ℕ} {s : ℤ} {Mbox : Finset ℕ} {M X Cshiu : ℝ}
    {P1 P2 MboxOuter : Finset ℕ} {w1 w2 : ℕ → ℂ} {Couter : ℝ}
    {B0 : ℕ} {Dana Dphys : ℝ} {unaccounted lowResidual : ℝ → ℝ}
    {cext : ℚ}
    {naturalScale Lsave vAA vBA vAB vBB : ℝ}
    (h : TwoProjectorPhysical3221Inputs Dat F Pdat C1 Y Sdat Wprime s Mbox M X Cshiu
      P1 P2 MboxOuter w1 w2 Couter B0 Dana Dphys unaccounted lowResidual cext
      naturalScale Lsave vAA vBA vAB vBB) :
    BalancedSevenPrimeBoxNormalization3221 Pdat 1 C1 Y :=
  primeBoxL1_of_ford723Adapter h.dictionary h.primeCount

/-! ## §4. Anti-circularity -/

/-- **`physicalClosure_not_automatic`.**  `LEAN_PROVED`.

The physical package is a genuine restriction: its ledger field alone can fail. -/
theorem physicalClosure_not_automatic :
    ∃ (B0 : ℕ) (cext : ℚ), ¬ (2 * cext < cvar B0) := by
  refine ⟨3, 0, ?_⟩
  rw [cvar_at_three]
  norm_num

/-- **`physicalClosure_cannot_construct_comparison`.**  `LEAN_PROVED`.

Nothing in the V22 physical closure layer produces a `MuLogComparisonAtCutoff`
inhabitant: the comparison channel is refutable for explicit parameters while the whole
V22 arithmetic layer is untouched. -/
theorem physicalClosure_cannot_construct_comparison :
    ∃ (Dat : InverseSampledHighCond3221Data) (naturalScale Lsave X Dcut B0r Sphys srcVal
      err : ℝ),
      InverseSampledHighCondLogVar3221Input Dat naturalScale Lsave ∧
        ¬ Erdos287.V20Compiler.MuLogComparisonAtCutoff X Dcut B0r Sphys srcVal err :=
  Erdos287.V21Compiler.twoProjectorCompiler_cannot_construct_comparison

end V22Closure
end Erdos287
