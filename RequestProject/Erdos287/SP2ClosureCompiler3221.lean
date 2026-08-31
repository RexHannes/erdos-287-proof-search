import Mathlib
import RequestProject.Erdos287.SP2PrimeBoxWeights3221
import RequestProject.Erdos287.TwoProjectorPhysicalClosure3221

/-!
# SP-2, Phase 3 — the direct Balanced7 analytic-closure compiler

`BALANCED7-SP2-DIRECT-PACKET45` / `3221-INVERSE-SAMPLED-HIGHCOND-LOGVAR45`

## The SP-2 numerology

The SP-2 packet fixes the cutoff exponent at `B0 = 1`, i.e. `D = log X`.  With the
**repaired safe** bad-character count `#Bad ≤ (D+1)²` this gives, through the V22 ledger,

```
C_var(1) = min(5, 15/2 − 2, 10 − 4) = 5,
```

and, *if* the physical log-prefactor audit returns `C_ext = 0`, the net exponent

```
netLogExponent(C_var, C_ext) = −(2 + 5)/2 + 0 = −7/2 < −1,
```

i.e. the Balanced7 error would be `o(X / log X)`.

## Status

The arithmetic above is Lean-proved and kernel-checked.  Everything it is *applied to* is
not:

* `BALANCED7-OMEGA-SP2-DIRECT-SOURCE-ADAPTER45` — `SOURCE_OPEN`;
* `PhysicalLogPrefactorSP23221` (the claim `C_ext = 0`) — `SOURCE_OPEN`;
* the short-shift sieve and Shiu divisor-average inputs — external, uninhabited;
* the comparison channel — `SOURCE_OPEN`.

Hence `BALANCED7 : OPEN` and `ERDOS287 : OPEN`.  The dual reading intended by the SP-2
programme is: *externally audited analytic closure, Lean-conditional compiler*.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace SP2Closure

open Erdos287.SP2Source
open Erdos287.SP2PrimeBox
open Erdos287.V21PrimeBox
open Erdos287.V21Sieve
open Erdos287.V21Shiu
open Erdos287.V21Cutoff
open Erdos287.V21Outer
open Erdos287.V21Compiler
open Erdos287.V22Ledger
open Erdos287.V22PrimeBoxL1
open Erdos287.V22Closure
open Erdos287.HighCond3221
open Erdos287.V19Compiler

/-! ## §1. The SP-2 cutoff -/

/-- The SP-2 cutoff exponent. -/
def sp2B0 : ℕ := 1

/-- The SP-2 cutoff is `D = log X` — the *one* shared cutoff, used on both the analytic
and the physical side. -/
theorem sp2_cutoff_eq_log (X : ℝ) :
    cutoffOfB0 sp2B0 X = Real.log X := by
  unfold cutoffOfB0 sp2B0
  simp [Real.rpow_one]

/-- The SP-2 variance exponent is `C_var(1) = 5`. -/
theorem sp2_cvar_eq_five : cvar sp2B0 = 5 := cvar_at_one

/-! ## §2. The physical log prefactor (SOURCE_OPEN) -/

/-- **`PhysicalLogPrefactorSP23221`** — `SOURCE_OPEN / UNINHABITED`.

The claim that the literal SP-2 packet carries **no** residual power of `log X` between
the physical object and the normalised `V_hi = AA − BA − AB + BB`, i.e. `C_ext = 0`.

Every scalar of the audit (powers of `log X`, powers of `log Y`, `∏ log p_i`, `7⁷`, `5!`,
Mellin factors, dyadic multiplicity, the two-sign factor, the Cauchy normalisation) is
allowed to be a *constant*; the field below asserts only that the accumulated **power of
`log X`** is zero.  This project does not discharge it. -/
structure PhysicalLogPrefactorSP23221 (cext : ℚ) : Prop where
  /-- The audited residual power of `log X`. -/
  cext_eq_zero : cext = 0

/-- **`sp2PhysicalLogPrefactor_not_automatic`.**  `LEAN_PROVED`. -/
theorem sp2PhysicalLogPrefactor_not_automatic :
    ∃ cext : ℚ, ¬ PhysicalLogPrefactorSP23221 cext := by
  refine ⟨1, ?_⟩
  intro h
  have := h.cext_eq_zero
  norm_num at this

/-! ## §3. The SP-2 closure arithmetic -/

/-- **`sp2_netLogExponent_eq_neg_seven_halves`.**  `LEAN_PROVED`.

`−(2 + C_var(1))/2 + 0 = −7/2`. -/
theorem sp2_netLogExponent_eq_neg_seven_halves :
    netLogExponent (cvar sp2B0) 0 = -7 / 2 := by
  rw [sp2_cvar_eq_five]
  unfold netLogExponent
  norm_num

/-- **`sp2_netLogExponent_lt_neg_one`.**  `LEAN_PROVED`.

`−7/2 < −1`: with `C_ext = 0` the SP-2 numerology clears the `X/log X` threshold, with
margin `5/2`. -/
theorem sp2_netLogExponent_lt_neg_one :
    netLogExponent (cvar sp2B0) 0 < -1 := by
  rw [sp2_netLogExponent_eq_neg_seven_halves]
  norm_num

/-- **`sp2_closure_margin`.**  `LEAN_PROVED`.

The SP-2 route still closes for any audited prefactor exponent `C_ext < 5/2`; the audit
therefore has genuine slack rather than being tuned to the answer. -/
theorem sp2_closure_margin {cext : ℚ} (h : cext < 5 / 2) :
    netLogExponent (cvar sp2B0) cext < -1 := by
  rw [sp2_cvar_eq_five]
  exact twoProjector_closes_of_cvar_gt_twoCext (by linarith)

/-- **`sp2_closure_fails_without_audit`.**  `LEAN_PROVED`.

If the physical prefactor audit returned `C_ext = 5/2` or more, the SP-2 route would
**not** close.  The closure is therefore genuinely contingent on the audit. -/
theorem sp2_closure_fails_without_audit {cext : ℚ} (h : 5 / 2 ≤ cext) :
    ¬ netLogExponent (cvar sp2B0) cext < -1 := by
  rw [sp2_cvar_eq_five, netLogExponent_lt_neg_one_iff]
  push_neg
  linarith

/-! ## §4. The bundled SP-2 package -/

/-- **`SP2AnalyticClosure3221Inputs`** — `CONDITIONAL / UNINHABITED`.

The SP-2 direct route to the log-variance interface.  Compared with the V22 bundle, the
source dictionary is the SP-2 one and the prefactor exponent is pinned by the SP-2 audit
interface rather than left free. -/
structure SP2AnalyticClosure3221Inputs
    (Dat : InverseSampledHighCond3221Data)
    (C : SP2FixedCertificateData) (Pdat : PrimeBoxData) (C1 Y : ℝ)
    (Sdat : ShortShiftSieveData)
    (Wprime : ℕ) (s : ℤ) (Mbox : Finset ℕ) (M X Cshiu : ℝ)
    (P1 P2 MboxOuter : Finset ℕ) (w1 w2 : ℕ → ℂ) (Couter : ℝ)
    (Dana Dphys : ℝ) (unaccounted lowResidual : ℝ → ℝ)
    (cext : ℚ)
    (naturalScale Lsave vAA vBA vAB vBB : ℝ) : Prop where
  /-- The SP-2 source identification (SOURCE_OPEN). -/
  dictionary : BalancedSevenOmegaSP2DirectSourceAdapter3221 C Pdat
  /-- The prime-box cardinality input (external prime counting). -/
  primeCount : PrimeBoxCardinality3221Input Pdat C1 Y
  /-- The external short-shift rough sieve input. -/
  sieve : ShortShiftRoughSieve3221Input Sdat
  /-- The external Shiu divisor-average input. -/
  shiu : ShiuLinearDivisorAverage3221Input Wprime s Mbox M X Cshiu
  /-- The outer two-prime `L²` input. -/
  outerL2 : OuterTwoPrimeL2Normalization3221Input P1 P2 MboxOuter w1 w2 M X Couter
  /-- The shared-cutoff compatibility firewall at `B0 = 1`. -/
  cutoff : HighProjectorCutoffCompat3221 X sp2B0 Dana Dphys unaccounted lowResidual
  /-- The SP-2 physical log-prefactor audit (SOURCE_OPEN). -/
  prefactor : PhysicalLogPrefactorSP23221 cext
  /-- The numeric budget layer transporting the ledger to the four channels. -/
  budget : TwoHighProjector3221ClosureInputs Dat naturalScale Lsave vAA vBA vAB vBB

/-- **`sp2_closes_logVar`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

The SP-2 package yields the log-variance interface together with the strict closure
inequality `netLogExponent(C_var(1), C_ext) = −7/2 < −1`.  **No inhabitant is
constructed.** -/
theorem sp2_closes_logVar
    {Dat : InverseSampledHighCond3221Data}
    {C : SP2FixedCertificateData} {Pdat : PrimeBoxData} {C1 Y : ℝ}
    {Sdat : ShortShiftSieveData}
    {Wprime : ℕ} {s : ℤ} {Mbox : Finset ℕ} {M X Cshiu : ℝ}
    {P1 P2 MboxOuter : Finset ℕ} {w1 w2 : ℕ → ℂ} {Couter : ℝ}
    {Dana Dphys : ℝ} {unaccounted lowResidual : ℝ → ℝ}
    {cext : ℚ}
    {naturalScale Lsave vAA vBA vAB vBB : ℝ}
    (h : SP2AnalyticClosure3221Inputs Dat C Pdat C1 Y Sdat Wprime s Mbox M X Cshiu
      P1 P2 MboxOuter w1 w2 Couter Dana Dphys unaccounted lowResidual cext
      naturalScale Lsave vAA vBA vAB vBB) :
    InverseSampledHighCondLogVar3221Input Dat naturalScale Lsave ∧
      netLogExponent (cvar sp2B0) cext < -1 := by
  refine ⟨twoHighProjector3221_closes_logVar h.budget, ?_⟩
  rw [h.prefactor.cext_eq_zero]
  exact sp2_netLogExponent_lt_neg_one

/-- **`sp2_supplies_primeBoxL1`.**  `LEAN_PROVED` (conditional).

The SP-2 package supplies `BALANCED7-PRIMEBOX-L1-NORMALIZATION45` with `C_ptw = 1`,
assuming only its own source identification and the external prime count. -/
theorem sp2_supplies_primeBoxL1
    {Dat : InverseSampledHighCond3221Data}
    {C : SP2FixedCertificateData} {Pdat : PrimeBoxData} {C1 Y : ℝ}
    {Sdat : ShortShiftSieveData}
    {Wprime : ℕ} {s : ℤ} {Mbox : Finset ℕ} {M X Cshiu : ℝ}
    {P1 P2 MboxOuter : Finset ℕ} {w1 w2 : ℕ → ℂ} {Couter : ℝ}
    {Dana Dphys : ℝ} {unaccounted lowResidual : ℝ → ℝ}
    {cext : ℚ}
    {naturalScale Lsave vAA vBA vAB vBB : ℝ}
    (h : SP2AnalyticClosure3221Inputs Dat C Pdat C1 Y Sdat Wprime s Mbox M X Cshiu
      P1 P2 MboxOuter w1 w2 Couter Dana Dphys unaccounted lowResidual cext
      naturalScale Lsave vAA vBA vAB vBB) :
    BalancedSevenPrimeBoxNormalization3221 Pdat 1 C1 Y :=
  sp2_primeBoxL1_of_adapter h.dictionary h.primeCount

/-! ## §5. The Balanced7 compiler -/

/-- **`balancedSeven_of_SP2_analytic_and_comparison`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

```
SP-2 analytic closure package      (SOURCE_OPEN / external, uninhabited)
  + first-Cauchy prefactor certificate
  + same-cutoff physical comparison  (SOURCE_OPEN, uninhabited)
        ⇒ BalancedSevenPacketInput
```

The comparison channel is an independent antecedent and is **not** inhabited anywhere, so
`BALANCED7` stays `OPEN`. -/
theorem balancedSeven_of_SP2_analytic_and_comparison
    {Dat : InverseSampledHighCond3221Data}
    {C : SP2FixedCertificateData} {Pdat : PrimeBoxData} {C1 Y : ℝ}
    {Sdat : ShortShiftSieveData}
    {Wprime : ℕ} {s : ℤ} {Mbox : Finset ℕ} {M X Cshiu : ℝ}
    {P1 P2 MboxOuter : Finset ℕ} {w1 w2 : ℕ → ℂ} {Couter : ℝ}
    {Dana Dphys : ℝ} {unaccounted lowResidual : ℝ → ℝ}
    {cext : ℚ}
    {naturalScale Lsave vAA vBA vAB vBB : ℝ}
    {Q Dcut srcVal Sphys prefactor E err : ℝ}
    (hX : 1 < X) (hQ : Q = X ^ (3 / 5 : ℝ))
    (hpack : SP2AnalyticClosure3221Inputs Dat C Pdat C1 Y Sdat Wprime s Mbox M X Cshiu
      P1 P2 MboxOuter w1 w2 Couter Dana Dphys unaccounted lowResidual cext
      naturalScale Lsave vAA vBA vAB vBB)
    (hcert : CauchyPrefactor3221Certificate Dat srcVal prefactor)
    (hE : 0 ≤ E) (hEbudget : prefactor * (naturalScale / Lsave) ≤ E ^ 2)
    (hcomp : Erdos287.V20Compiler.MuLogComparisonAtCutoff X Dcut ((sp2B0 : ℕ) : ℝ) Sphys
      srcVal err) :
    Erdos287.V16Status.BalancedSevenPacketInput X Sphys (E + err) :=
  balancedSeven_of_highCondLogVar hX hQ hcert (sp2_closes_logVar hpack).1 hE hEbudget
    (Erdos287.V20Compiler.comparisonAtCutoff_to_base hcomp)

/-! ## §6. Provenance and anti-circularity -/

/-- **`sp2_adapter_is_independent_of_ford723`.**  `LEAN_PROVED`.

The SP-2 identification does **not** entail the Ford-(7.23) identification: there are data
for which the SP-2 adapter holds while a Ford dictionary fails.  This is the formal side of
the provenance retraction `BALANCED7-OMEGA-FM723-SOURCE-ADAPTER45 : RETRACTED / NOT THE
LITERAL SOURCE`; the FM723 file itself is preserved. -/
theorem sp2_adapter_is_independent_of_ford723 :
    ∃ (C : SP2FixedCertificateData) (Pdat : PrimeBoxData)
      (F : Erdos287.V22Ford.Ford723CoefficientData),
      BalancedSevenOmegaSP2DirectSourceAdapter3221 C Pdat ∧
        ¬ Erdos287.V22Ford.BalancedSevenOmegaFord723Adapter3221 F Pdat := by
  classical
  refine ⟨⟨0, ∅, 7, 3, 1, fun _ => {2}⟩, sp2PrimeBoxData ⟨0, ∅, 7, 3, 1, fun _ => {2}⟩,
    ⟨fun _ _ => 2, fun _ => ∅⟩, ⟨⟨rfl, rfl, rfl, rfl, Or.inl rfl, ?_⟩, fun _ _ => rfl,
      fun _ => rfl⟩, ?_⟩
  · intro i p hp
    simp only [Finset.mem_singleton] at hp
    subst hp
    exact Nat.prime_two
  · intro h
    have h1 := h.coeff_norm_le_one 0 0
    simp only [Complex.norm_ofNat] at h1
    norm_num at h1

/-- **`sp2Closure_not_automatic`.**  `LEAN_PROVED`.

The SP-2 closure package is a genuine restriction: its prefactor field alone can fail. -/
theorem sp2Closure_not_automatic : ∃ cext : ℚ, ¬ PhysicalLogPrefactorSP23221 cext :=
  sp2PhysicalLogPrefactor_not_automatic

/-- **`sp2Closure_cannot_construct_comparison`.**  `LEAN_PROVED`.

The SP-2 analytic layer does not produce a comparison inhabitant: the comparison channel
remains refutable while the log-variance interface is available. -/
theorem sp2Closure_cannot_construct_comparison :
    ∃ (Dat : InverseSampledHighCond3221Data) (naturalScale Lsave X Dcut B0r Sphys srcVal
      err : ℝ),
      InverseSampledHighCondLogVar3221Input Dat naturalScale Lsave ∧
        ¬ Erdos287.V20Compiler.MuLogComparisonAtCutoff X Dcut B0r Sphys srcVal err :=
  Erdos287.V21Compiler.twoProjectorCompiler_cannot_construct_comparison

/-- **`sp2_does_not_prove_balancedSeven`.**  `LEAN_PROVED`.

The Balanced7 compiler above is a genuine implication and not a proof: its comparison
antecedent is refutable, so no inhabitant of the conclusion is produced here. -/
theorem sp2_does_not_prove_balancedSeven :
    ∃ (X Dcut B0r Sphys srcVal err : ℝ),
      ¬ Erdos287.V20Compiler.MuLogComparisonAtCutoff X Dcut B0r Sphys srcVal err := by
  obtain ⟨_, _, _, X, Dcut, B0r, Sphys, srcVal, err, _, h⟩ :=
    sp2Closure_cannot_construct_comparison
  exact ⟨X, Dcut, B0r, Sphys, srcVal, err, h⟩

end SP2Closure
end Erdos287
