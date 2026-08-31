import Mathlib
import RequestProject.Erdos287.OuterTwoPrimeBlock3221
import RequestProject.Erdos287.PrimeBoxNormalization3221
import RequestProject.Erdos287.ShiuDivisorAverage3221
import RequestProject.Erdos287.BalancedSevenV20Compiler

/-!
# V21, Phase 10 — the conditional two-projector closure compiler

`3221-INVERSE-SAMPLED-HIGHCOND-LOGVAR45 : CONDITIONAL / OPEN`
`BALANCED7 : OPEN`

The V20 compiler `logVar_of_four_channels` is **kept** as historical infrastructure; V21
adds `logVar_of_twoHighProjectorPackage` as the preferred route, whose channels are the
four *separate* cells `AA`, `BA`, `AB`, `BB` of the two-high-projector identity.

Every source/analytic antecedent of the V21 package is an interface that is **never
inhabited** in this repository:

* `TwoProjectorAmbientCompat3221` for the physical character data;
* `ShortShiftRoughSieve3221Input`;
* `ShiuLinearDivisorAverage3221Input`;
* `BalancedSevenPrimeBoxNormalization3221`;
* `OuterTwoPrimeL2Normalization3221Input`;
* `HighProjectorCutoffCompat3221` (physical instance);
* `PhysicalLogPrefactor3221`;
* the three separate channel bounds `BAChannelBound3221`, `ABChannelBound3221`,
  `BBChannelBound3221`, and the `AA` bound.

Therefore this file proves **no** unconditional statement about Balanced7 or Erdős #287.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace V21Compiler

open Erdos287.HighCond3221 Erdos287.V19Compiler Erdos287.V20Compiler
open Erdos287.V21TwoProj Erdos287.V21Sieve Erdos287.V21Shiu Erdos287.V21PrimeBox
open Erdos287.V21Cutoff Erdos287.V21LogBudget Erdos287.V21Outer

/-! ## §1. The four channel bounds, kept strictly separate -/

/-- The `AA` (full–full) channel bound: `AA ≤ S · L^{−c}`. -/
structure AAChannelBound3221 (v S L c : ℝ) : Prop where
  /-- The channel estimate. -/
  bound : v ≤ S * L ^ (-c)

/-- The `BA` channel bound (first character bad, second full). -/
structure BAChannelBound3221 (v S L c : ℝ) : Prop where
  /-- The channel estimate. -/
  bound : v ≤ S * L ^ (-c)

/-- The `AB` channel bound (first character full, second bad). -/
structure ABChannelBound3221 (v S L c : ℝ) : Prop where
  /-- The channel estimate. -/
  bound : v ≤ S * L ^ (-c)

/-- The `BB` channel bound (both characters bad). -/
structure BBChannelBound3221 (v S L c : ℝ) : Prop where
  /-- The channel estimate. -/
  bound : v ≤ S * L ^ (-c)

/-- **`channelBounds_compile_to_min`.**  `LEAN_PROVED`.

The four separate channel bounds compile, through the symbolic log ledger, to the
`min`-exponent bound with the explicit factor `4`. -/
theorem channelBounds_compile_to_min {L S Vhi vAA vBA vAB vBB cAA cBA cAB cBB : ℝ}
    (hL : 1 ≤ L) (hS : 0 ≤ S) (hdec : Vhi ≤ vAA + vBA + vAB + vBB)
    (hAA : AAChannelBound3221 vAA S L cAA) (hBA : BAChannelBound3221 vBA S L cBA)
    (hAB : ABChannelBound3221 vAB S L cAB) (hBB : BBChannelBound3221 vBB S L cBB) :
    Vhi ≤ 4 * (S * L ^ (-(projectorLogExponent cAA cBA cAB cBB))) :=
  highVarianceLogCompiler hL hS hdec hAA.bound hBA.bound hAB.bound hBB.bound

/-! ## §2. The closure inputs -/

/-- **`TwoHighProjector3221ClosureInputs`** — the *numeric* budget layer of the V21 route.

It contains only genuine antecedents: the four channels are nonnegative, they dominate the
inverse-sampled high-conductor energy (this is the two-projector reassembly at the physical
level), and each channel is inside its own quarter of the budget. -/
structure TwoHighProjector3221ClosureInputs (Dat : InverseSampledHighCond3221Data)
    (naturalScale Lsave vAA vBA vAB vBB : ℝ) : Prop where
  /-- The natural scale is positive. -/
  scale_pos : 0 < naturalScale
  /-- The logarithmic saving is positive. -/
  Lsave_pos : 0 < Lsave
  /-- The `AA` channel is nonnegative. -/
  vAA_nonneg : 0 ≤ vAA
  /-- The `BA` channel is nonnegative. -/
  vBA_nonneg : 0 ≤ vBA
  /-- The `AB` channel is nonnegative. -/
  vAB_nonneg : 0 ≤ vAB
  /-- The `BB` channel is nonnegative. -/
  vBB_nonneg : 0 ≤ vBB
  /-- The two-projector reassembly `V_hi ≤ AA + BA + AB + BB`. -/
  reassembly : Dat.Vhi ≤ vAA + vBA + vAB + vBB
  /-- The `AA` quarter. -/
  aa_budget : vAA ≤ naturalScale / (4 * Lsave)
  /-- The `BA` quarter. -/
  ba_budget : vBA ≤ naturalScale / (4 * Lsave)
  /-- The `AB` quarter. -/
  ab_budget : vAB ≤ naturalScale / (4 * Lsave)
  /-- The `BB` quarter. -/
  bb_budget : vBB ≤ naturalScale / (4 * Lsave)

/-- **`twoHighProjector3221_closes_logVar`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

The numeric budget layer closes the log-variance interface.  No channel is absorbed into
another and the compiler has no circular dependence on its own conclusion. -/
theorem twoHighProjector3221_closes_logVar {Dat : InverseSampledHighCond3221Data}
    {naturalScale Lsave vAA vBA vAB vBB : ℝ}
    (h : TwoHighProjector3221ClosureInputs Dat naturalScale Lsave vAA vBA vAB vBB) :
    InverseSampledHighCondLogVar3221Input Dat naturalScale Lsave := by
  refine ⟨h.scale_pos, h.Lsave_pos, ?_⟩
  have hquarter : 4 * (naturalScale / (4 * Lsave)) = naturalScale / Lsave := by
    field_simp
  have hsum : vAA + vBA + vAB + vBB ≤ 4 * (naturalScale / (4 * Lsave)) := by
    linarith [h.aa_budget, h.ba_budget, h.ab_budget, h.bb_budget]
  linarith [h.reassembly, hsum, hquarter.le, hquarter.ge]

/-! ## §3. The full source/analytic package -/

/-- **`TwoHighProjector3221SourcePackage`** — the V21 controlling conditional route.

Every field is either an uninhabited source/analytic interface or the numeric budget layer
above.  **No inhabitant is constructed.** -/
structure TwoHighProjector3221SourcePackage
    (Dat : InverseSampledHighCond3221Data)
    {α : Type*} [Fintype α] [DecidableEq α] (Ambient Bad Restricted : Finset α)
    (Sdat : ShortShiftSieveData)
    (Wprime : ℕ) (s : ℤ) (Mbox : Finset ℕ) (M X Cshiu : ℝ)
    (Pdat : PrimeBoxData) (Cptw C1 Y : ℝ)
    (P1 P2 MboxOuter : Finset ℕ) (w1 w2 : ℕ → ℂ) (Couter : ℝ)
    (B0 : ℕ) (Dana Dphys : ℝ) (unaccounted lowResidual : ℝ → ℝ)
    (Pref : PhysicalLogPrefactorData) (physical normalised : ℝ)
    (naturalScale Lsave vAA vBA vAB vBB Sscale Lbase cAA cBA cAB cBB : ℝ) : Prop where
  /-- The ambient projector compatibility firewall. -/
  ambient : TwoProjectorAmbientCompat3221 Ambient Bad Restricted
  /-- The external short-shift rough sieve input. -/
  sieve : ShortShiftRoughSieve3221Input Sdat
  /-- The external Shiu divisor-average input. -/
  shiu : ShiuLinearDivisorAverage3221Input Wprime s Mbox M X Cshiu
  /-- The prime-box normalisation source input. -/
  primeBox : BalancedSevenPrimeBoxNormalization3221 Pdat Cptw C1 Y
  /-- The outer two-prime `L²` input. -/
  outerL2 : OuterTwoPrimeL2Normalization3221Input P1 P2 MboxOuter w1 w2 M X Couter
  /-- The shared cutoff compatibility. -/
  cutoff : HighProjectorCutoffCompat3221 X B0 Dana Dphys unaccounted lowResidual
  /-- The physical log-prefactor budget. -/
  prefactor : PhysicalLogPrefactor3221 Pref X physical normalised
  /-- The `AA` channel bound. -/
  aa : AAChannelBound3221 vAA Sscale Lbase cAA
  /-- The `BA` channel bound. -/
  ba : BAChannelBound3221 vBA Sscale Lbase cBA
  /-- The `AB` channel bound. -/
  ab : ABChannelBound3221 vAB Sscale Lbase cAB
  /-- The `BB` channel bound. -/
  bb : BBChannelBound3221 vBB Sscale Lbase cBB
  /-- The numeric budget layer. -/
  budget : TwoHighProjector3221ClosureInputs Dat naturalScale Lsave vAA vBA vAB vBB

/-- **`logVar_of_twoHighProjectorPackage`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

The V21 preferred log-variance compiler.  The V20 `logVar_of_four_channels` is kept
unchanged as historical infrastructure; this one routes through the two-projector cells
instead of the HHH cell. -/
theorem logVar_of_twoHighProjectorPackage {Dat : InverseSampledHighCond3221Data}
    {α : Type*} [Fintype α] [DecidableEq α] {Ambient Bad Restricted : Finset α}
    {Sdat : ShortShiftSieveData}
    {Wprime : ℕ} {s : ℤ} {Mbox : Finset ℕ} {M X Cshiu : ℝ}
    {Pdat : PrimeBoxData} {Cptw C1 Y : ℝ}
    {P1 P2 MboxOuter : Finset ℕ} {w1 w2 : ℕ → ℂ} {Couter : ℝ}
    {B0 : ℕ} {Dana Dphys : ℝ} {unaccounted lowResidual : ℝ → ℝ}
    {Pref : PhysicalLogPrefactorData} {physical normalised : ℝ}
    {naturalScale Lsave vAA vBA vAB vBB Sscale Lbase cAA cBA cAB cBB : ℝ}
    (h : TwoHighProjector3221SourcePackage Dat Ambient Bad Restricted Sdat Wprime s Mbox
      M X Cshiu Pdat Cptw C1 Y P1 P2 MboxOuter w1 w2 Couter B0 Dana Dphys unaccounted
      lowResidual Pref physical normalised naturalScale Lsave vAA vBA vAB vBB Sscale Lbase
      cAA cBA cAB cBB) :
    InverseSampledHighCondLogVar3221Input Dat naturalScale Lsave :=
  twoHighProjector3221_closes_logVar h.budget

/-- **`balancedSeven_of_v21_package`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

```
two-projector source package        (uninhabited interfaces)
  + first-Cauchy prefactor certificate
  + same-B0 physical comparison     (SOURCE_OPEN, uninhabited)
      ⇒ BalancedSevenPacketInput
```

Comparison remains an independent open channel, so `BALANCED7` stays `OPEN`. -/
theorem balancedSeven_of_v21_package {Dat : InverseSampledHighCond3221Data}
    {α : Type*} [Fintype α] [DecidableEq α] {Ambient Bad Restricted : Finset α}
    {Sdat : ShortShiftSieveData}
    {Wprime : ℕ} {s : ℤ} {Mbox : Finset ℕ} {M X Cshiu : ℝ}
    {Pdat : PrimeBoxData} {Cptw C1 Y : ℝ}
    {P1 P2 MboxOuter : Finset ℕ} {w1 w2 : ℕ → ℂ} {Couter : ℝ}
    {B0 : ℕ} {Dana Dphys : ℝ} {unaccounted lowResidual : ℝ → ℝ}
    {Pref : PhysicalLogPrefactorData} {physical normalised : ℝ}
    {naturalScale Lsave vAA vBA vAB vBB Sscale Lbase cAA cBA cAB cBB : ℝ}
    {Q Dcut srcVal Sphys prefactor E err : ℝ}
    (hX : 1 < X) (hQ : Q = X ^ (3 / 5 : ℝ))
    (hpack : TwoHighProjector3221SourcePackage Dat Ambient Bad Restricted Sdat Wprime s Mbox
      M X Cshiu Pdat Cptw C1 Y P1 P2 MboxOuter w1 w2 Couter B0 Dana Dphys unaccounted
      lowResidual Pref physical normalised naturalScale Lsave vAA vBA vAB vBB Sscale Lbase
      cAA cBA cAB cBB)
    (hcert : CauchyPrefactor3221Certificate Dat srcVal prefactor)
    (hE : 0 ≤ E) (hEbudget : prefactor * (naturalScale / Lsave) ≤ E ^ 2)
    (hcomp : MuLogComparisonAtCutoff X Dcut (B0 : ℝ) Sphys srcVal err) :
    Erdos287.V16Status.BalancedSevenPacketInput X Sphys (E + err) :=
  balancedSeven_of_highCondLogVar hX hQ hcert (logVar_of_twoHighProjectorPackage hpack) hE
    hEbudget (comparisonAtCutoff_to_base hcomp)

/-- **`sixthMoment_not_needed_if_twoProjectorClosed`.**  `LEAN_PROVED` (status theorem).

If the two-projector budget layer is supplied, the log-variance interface follows **without
any sixth-moment hypothesis**: the sixth-moment route is a *stronger sufficient* fallback,
not a necessary ingredient.  (It is neither deleted nor marked false; while the physical
two-projector inputs stay uninhabited it remains an open alternative.) -/
theorem sixthMoment_not_needed_if_twoProjectorClosed
    {Dat : InverseSampledHighCond3221Data} {naturalScale Lsave vAA vBA vAB vBB : ℝ}
    (h : TwoHighProjector3221ClosureInputs Dat naturalScale Lsave vAA vBA vAB vBB) :
    InverseSampledHighCondLogVar3221Input Dat naturalScale Lsave :=
  twoHighProjector3221_closes_logVar h

/-! ## §4. Non-vacuity and anti-circularity -/

/-- The prime-box normalisation source input is not automatic. -/
theorem primeBoxNormalization_not_automatic_v21 :
    ∃ (Pdat : PrimeBoxData) (Cptw C1 Y : ℝ),
      ¬ BalancedSevenPrimeBoxNormalization3221 Pdat Cptw C1 Y :=
  Erdos287.V21PrimeBox.primeBoxNormalization_not_automatic

/-- The short-shift sieve input is not automatic. -/
theorem shortShiftSieve_not_automatic_v21 :
    ∃ Sdat : ShortShiftSieveData, ¬ ShortShiftRoughSieve3221Input Sdat :=
  Erdos287.V21Sieve.shortShiftSieve_not_automatic

/-- The Shiu divisor-average input is not automatic. -/
theorem shiuInput_not_automatic_v21 :
    ∃ (Wprime : ℕ) (s : ℤ) (Mbox : Finset ℕ) (M X Cshiu : ℝ),
      ¬ ShiuLinearDivisorAverage3221Input Wprime s Mbox M X Cshiu :=
  Erdos287.V21Shiu.shiuInput_not_automatic

/-- The shared cutoff compatibility is not automatic. -/
theorem cutoffCompat_not_automatic_v21 :
    ∃ (X : ℝ) (B0 : ℕ) (Dana Dphys : ℝ) (unaccounted lowResidual : ℝ → ℝ),
      ¬ HighProjectorCutoffCompat3221 X B0 Dana Dphys unaccounted lowResidual :=
  Erdos287.V21Cutoff.cutoffCompat_not_automatic

/-- The physical log prefactor budget is not automatic. -/
theorem physicalLogPrefactor_not_automatic_v21 :
    ∃ (P : PhysicalLogPrefactorData) (X physical normalised : ℝ),
      ¬ PhysicalLogPrefactor3221 P X physical normalised :=
  Erdos287.V21LogBudget.physicalLogPrefactor_not_automatic

/-- The outer two-prime `L²` input is not automatic. -/
theorem outerTwoPrimeL2_not_automatic_v21 :
    ∃ (P1 P2 Mbox : Finset ℕ) (w1 w2 : ℕ → ℂ) (M X Couter : ℝ),
      ¬ OuterTwoPrimeL2Normalization3221Input P1 P2 Mbox w1 w2 M X Couter :=
  Erdos287.V21Outer.outerTwoPrimeL2_not_automatic

/-- **`twoProjectorCompiler_cannot_construct_primeBoxNormalization`.**  `LEAN_PROVED`.

The log-variance conclusion is strictly weaker than the prime-box source input: there are
data for which the former holds and the latter fails. -/
theorem twoProjectorCompiler_cannot_construct_primeBoxNormalization :
    ∃ (Dat : InverseSampledHighCond3221Data) (naturalScale Lsave : ℝ)
      (Pdat : PrimeBoxData) (Cptw C1 Y : ℝ),
      InverseSampledHighCondLogVar3221Input Dat naturalScale Lsave ∧
        ¬ BalancedSevenPrimeBoxNormalization3221 Pdat Cptw C1 Y := by
  obtain ⟨Pdat, Cptw, C1, Y, hP⟩ := Erdos287.V21PrimeBox.primeBoxNormalization_not_automatic
  refine ⟨probeData, 4, 2, Pdat, Cptw, C1, Y, ⟨by norm_num, by norm_num, ?_⟩, hP⟩
  rw [probeData_Vhi]
  norm_num

/-- **`twoProjectorCompiler_cannot_construct_comparison`.**  `LEAN_PROVED`. -/
theorem twoProjectorCompiler_cannot_construct_comparison :
    ∃ (Dat : InverseSampledHighCond3221Data) (naturalScale Lsave : ℝ)
      (X Dcut B0 hard model err : ℝ),
      InverseSampledHighCondLogVar3221Input Dat naturalScale Lsave ∧
        ¬ MuLogComparisonAtCutoff X Dcut B0 hard model err :=
  balancedSeven_compiler_cannot_construct_comparison

/-- **`balancedSevenV21_cannot_construct_comparison`.**  `LEAN_PROVED`.

The V21 Balanced7 compiler leaves the comparison channel independent and open. -/
theorem balancedSevenV21_cannot_construct_comparison :
    ∃ (Dat : InverseSampledHighCond3221Data) (naturalScale Lsave : ℝ)
      (X Dcut B0 hard model err : ℝ),
      InverseSampledHighCondLogVar3221Input Dat naturalScale Lsave ∧
        ¬ MuLogComparisonAtCutoff X Dcut B0 hard model err :=
  balancedSeven_compiler_cannot_construct_comparison

end V21Compiler
end Erdos287
