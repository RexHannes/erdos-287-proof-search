import Mathlib
import RequestProject.Erdos287.HighProjectorCutoff3221

/-!
# V21, Phase 8 — the exponent ledger, the symbolic log budget and the physical prefactor

`3221-PHYSICAL-LOG-PREFAC45 : SOURCE_OPEN`

## §1.  Exponent ledger (kernel-checked rational arithmetic)

```
M  = X^(2/7)      W5 = X^(5/7)      Q = X^(3/5)      T = W5/Q = X^(4/35)
2/7 + 5/7 + 4/35 = 39/35        3/5 + 2/7 = 31/35        31/35 + 39/35 = 2
```

These are finite rational identities.  **No analytic theorem follows from them**; they only
fix the bookkeeping of the natural scale.

## §2.  The symbolic log budget

`projectorLogExponent` is the `min` of the four channel exponents, and
`highVarianceLogCompiler` is the (Lean-proved) statement that four separate channel bounds
`X^{39/35} log^{-c_•}` compile to `4·X^{39/35} log^{-min}`.  The four channels
`AA`, `BA`, `AB`, `BB` are kept **separate** everywhere: no exponent is guessed and no
channel is silently merged.  `outerCauchyLogCompiler` performs the outer Cauchy step with
the two exponents added and halved.

## §3.  The physical log prefactor

`PhysicalLogPrefactorData` records **every** scalar between the physical Balanced7 packet
and the normalised two-projector object (`7^7`, `5!`, dyadic multiplicity, the two-sign
factor, the Mellin factor, the Cauchy normalisation) *separately* from the external log
exponent `C_ext`.  `prefactor_enters_log_ledger` shows how a fixed positive power
`(log X)^{C_ext}` degrades the ledger exponent — which is exactly why `C_ext` may not be
dropped.  The budget interface is **not inhabited**: the literal source reconstruction
proving a value of `C_ext` is not present, so the label stays `SOURCE_OPEN`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace V21LogBudget

/-! ## §1. The exponent ledger -/

/-- `M = X^{2/7}`. -/
def Mexp : ℚ := 2 / 7

/-- `W5 = X^{5/7}`. -/
def W5exp : ℚ := 5 / 7

/-- `Q = X^{3/5}`. -/
def Qexp : ℚ := 3 / 5

/-- `T = W5/Q = X^{4/35}`. -/
def Texp : ℚ := 4 / 35

/-- **`physicalShiftScale_exponent`.**  `T = W5/Q`. -/
theorem physicalShiftScale_exponent : Texp = W5exp - Qexp := by
  unfold Texp W5exp Qexp; norm_num

/-- **`twoProjector_naturalExponent`.**  `2/7 + 5/7 + 4/35 = 39/35`. -/
theorem twoProjector_naturalExponent : Mexp + W5exp + Texp = 39 / 35 := by
  unfold Mexp W5exp Texp; norm_num

/-- **`outerCauchy_exponent`.**  `3/5 + 2/7 = 31/35`. -/
theorem outerCauchy_exponent : Qexp + Mexp = 31 / 35 := by
  unfold Qexp Mexp; norm_num

/-- **`physicalSquareRoot_exponent`.**  `31/35 + 39/35 = 2`. -/
theorem physicalSquareRoot_exponent : (31 / 35 : ℚ) + 39 / 35 = 2 := by norm_num

/-- The whole ledger in one statement. -/
theorem exponent_ledger :
    Texp = W5exp - Qexp ∧ Mexp + W5exp + Texp = 39 / 35 ∧ Qexp + Mexp = 31 / 35 ∧
      (Qexp + Mexp) + (Mexp + W5exp + Texp) = 2 := by
  unfold Mexp W5exp Qexp Texp
  norm_num

/-! ## §2. The symbolic log budget -/

/-- The projector log exponent: the `min` of the four **separate** channel exponents. -/
noncomputable def projectorLogExponent (cAA cBA cAB cBB : ℝ) : ℝ :=
  min (min cAA cBA) (min cAB cBB)

theorem projectorLogExponent_le_AA (cAA cBA cAB cBB : ℝ) :
    projectorLogExponent cAA cBA cAB cBB ≤ cAA :=
  le_trans (min_le_left _ _) (min_le_left _ _)

theorem projectorLogExponent_le_BA (cAA cBA cAB cBB : ℝ) :
    projectorLogExponent cAA cBA cAB cBB ≤ cBA :=
  le_trans (min_le_left _ _) (min_le_right _ _)

theorem projectorLogExponent_le_AB (cAA cBA cAB cBB : ℝ) :
    projectorLogExponent cAA cBA cAB cBB ≤ cAB :=
  le_trans (min_le_right _ _) (min_le_left _ _)

theorem projectorLogExponent_le_BB (cAA cBA cAB cBB : ℝ) :
    projectorLogExponent cAA cBA cAB cBB ≤ cBB :=
  le_trans (min_le_right _ _) (min_le_right _ _)

/-- A channel bound at exponent `c` is a channel bound at the smaller exponent `c'`. -/
theorem channel_bound_relax {L S v c c' : ℝ} (hL : 1 ≤ L) (hS : 0 ≤ S) (hc : c' ≤ c)
    (h : v ≤ S * L ^ (-c)) : v ≤ S * L ^ (-c') := by
  have hmono : L ^ (-c) ≤ L ^ (-c') :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  exact le_trans h (mul_le_mul_of_nonneg_left hmono hS)

/-- **`highVarianceLogCompiler`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

Four separate channel bounds at the common natural scale `S = X^{39/35}` compile to

`V_hi ≤ 4 · S · log^{−min₄(c_AA, c_BA, c_AB, c_BB)}`.

The factor `4` is printed, not hidden. -/
theorem highVarianceLogCompiler {L S Vhi vAA vBA vAB vBB cAA cBA cAB cBB : ℝ}
    (hL : 1 ≤ L) (hS : 0 ≤ S)
    (hdec : Vhi ≤ vAA + vBA + vAB + vBB)
    (hAA : vAA ≤ S * L ^ (-cAA)) (hBA : vBA ≤ S * L ^ (-cBA))
    (hAB : vAB ≤ S * L ^ (-cAB)) (hBB : vBB ≤ S * L ^ (-cBB)) :
    Vhi ≤ 4 * (S * L ^ (-(projectorLogExponent cAA cBA cAB cBB))) := by
  have h1 := channel_bound_relax hL hS (projectorLogExponent_le_AA cAA cBA cAB cBB) hAA
  have h2 := channel_bound_relax hL hS (projectorLogExponent_le_BA cAA cBA cAB cBB) hBA
  have h3 := channel_bound_relax hL hS (projectorLogExponent_le_AB cAA cBA cAB cBB) hAB
  have h4 := channel_bound_relax hL hS (projectorLogExponent_le_BB cAA cBA cAB cBB) hBB
  linarith

/-- **`outerCauchyLogCompiler`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

The outer Cauchy step: if the two factors carry log savings `c₁` and `c₂`, the product
carries `(c₁+c₂)/2` after the square root. -/
theorem outerCauchyLogCompiler {L S1 S2 V O total c1 c2 : ℝ}
    (hL : 0 < L) (hS1 : 0 ≤ S1) (hS2 : 0 ≤ S2) (hO0 : 0 ≤ O)
    (hV : V ≤ S1 * L ^ (-c1)) (hO : O ≤ S2 * L ^ (-c2))
    (htotal : total ≤ Real.sqrt (V * O)) :
    total ≤ Real.sqrt (S1 * S2) * L ^ (-(c1 + c2) / 2) := by
  have hLpow1 : 0 ≤ L ^ (-c1) := le_of_lt (Real.rpow_pos_of_pos hL _)
  have hLpow2 : 0 ≤ L ^ (-c2) := le_of_lt (Real.rpow_pos_of_pos hL _)
  have hprod : V * O ≤ (S1 * L ^ (-c1)) * (S2 * L ^ (-c2)) :=
    mul_le_mul hV hO hO0 (mul_nonneg hS1 hLpow1)
  have hrw : (S1 * L ^ (-c1)) * (S2 * L ^ (-c2)) = (S1 * S2) * L ^ (-(c1 + c2)) := by
    rw [show -(c1 + c2) = -c1 + -c2 by ring, Real.rpow_add hL (-c1) (-c2)]
    ring
  rw [hrw] at hprod
  have hsqrt : Real.sqrt (V * O) ≤ Real.sqrt ((S1 * S2) * L ^ (-(c1 + c2))) :=
    Real.sqrt_le_sqrt hprod
  have hsplit : Real.sqrt ((S1 * S2) * L ^ (-(c1 + c2)))
      = Real.sqrt (S1 * S2) * L ^ (-(c1 + c2) / 2) := by
    rw [Real.sqrt_mul (mul_nonneg hS1 hS2)]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hL)]
    congr 1
    ring
  linarith [le_trans htotal hsqrt, hsplit.le, hsplit.ge]

/-! ## §3. The physical log prefactor -/

/-- Every scalar between the physical Balanced7 packet and the normalised two-projector
object, printed **separately**.  Constants are harmless but must be recorded; the external
log exponent `C_ext` is *not* a constant and enters the ledger. -/
structure PhysicalLogPrefactorData where
  /-- The polarisation constant `7^7`. -/
  sevenPow : ℕ
  /-- The five-box factorial constant `5!`. -/
  fiveFactorial : ℕ
  /-- The dyadic decomposition multiplicity. -/
  dyadicMultiplicity : ℕ
  /-- The two-sign factor. -/
  signCount : ℕ
  /-- The Mellin-inversion factor. -/
  mellinFactor : ℝ
  /-- The Cauchy normalisation. -/
  cauchyNormalisation : ℝ
  /-- The **external log exponent** `C_ext` — amplitude-level positive log cost coming from
  Mellin inversion, condition removal, Perron/order phases, smooth partitions, dyadic
  decomposition and source reconstruction. -/
  externalLogExponent : ℝ

/-- The product of the *constant* factors (no log powers). -/
noncomputable def constantFactors (P : PhysicalLogPrefactorData) : ℝ :=
  (P.sevenPow : ℝ) * (P.fiveFactorial : ℝ) * (P.dyadicMultiplicity : ℝ) *
    (P.signCount : ℝ) * P.mellinFactor * P.cauchyNormalisation

/-- The canonical constants of the Balanced7 / five-box packet, as data. -/
def canonicalPrefactorConstants : ℕ × ℕ := (7 ^ 7, Nat.factorial 5)

theorem canonicalPrefactorConstants_values : canonicalPrefactorConstants = (823543, 120) := by
  decide

/-- **`PhysicalLogPrefactor3221`** — `SOURCE_OPEN / UNINHABITED`.

The budget relating the physical packet to the normalised object:
`physical ≤ constantFactors · (log X)^{C_ext} · normalised`, with `C_ext ≥ 0` explicitly
recorded.  The literal source reconstruction that would fix `C_ext` is not present in this
repository, so **no inhabitant is constructed**. -/
structure PhysicalLogPrefactor3221 (P : PhysicalLogPrefactorData) (X physical normalised : ℝ) :
    Prop where
  /-- The external log exponent is nonnegative (a cost, never a saving). -/
  Cext_nonneg : 0 ≤ P.externalLogExponent
  /-- Every scalar is accounted for by the recorded constants and `(log X)^{C_ext}`. -/
  provenance :
    physical ≤ constantFactors P * Real.log X ^ P.externalLogExponent * normalised

/-- **`prefactor_enters_log_ledger`.**  `LEAN_PROVED`.

A fixed positive power `(log X)^{C_ext}` degrades the ledger exponent by exactly `C_ext`:
if the normalised object obeys `normalised ≤ S · log^{−c}`, the physical amplitude obeys
`physical ≤ (constants) · S · log^{−(c − C_ext)}`. -/
theorem prefactor_enters_log_ledger {P : PhysicalLogPrefactorData} {X physical normalised S c : ℝ}
    (hL : 0 < Real.log X) (hconst : 0 ≤ constantFactors P)
    (hbudget : PhysicalLogPrefactor3221 P X physical normalised)
    (hnorm : normalised ≤ S * Real.log X ^ (-c)) :
    physical ≤ constantFactors P * (S * Real.log X ^ (-(c - P.externalLogExponent))) := by
  have hpow : 0 ≤ Real.log X ^ P.externalLogExponent :=
    le_of_lt (Real.rpow_pos_of_pos hL _)
  have h1 : physical ≤ constantFactors P * Real.log X ^ P.externalLogExponent * normalised :=
    hbudget.provenance
  have h2 : constantFactors P * Real.log X ^ P.externalLogExponent * normalised
      ≤ constantFactors P * Real.log X ^ P.externalLogExponent * (S * Real.log X ^ (-c)) :=
    mul_le_mul_of_nonneg_left hnorm (mul_nonneg hconst hpow)
  have h3 : constantFactors P * Real.log X ^ P.externalLogExponent * (S * Real.log X ^ (-c))
      = constantFactors P * (S * Real.log X ^ (-(c - P.externalLogExponent))) := by
    rw [show -(c - P.externalLogExponent) = P.externalLogExponent + -c by ring,
      Real.rpow_add hL]
    ring
  linarith [h1, h2, h3.le, h3.ge]

/-- **`physicalLogPrefactor_not_automatic`.**  `LEAN_PROVED`. -/
theorem physicalLogPrefactor_not_automatic :
    ∃ (P : PhysicalLogPrefactorData) (X physical normalised : ℝ),
      ¬ PhysicalLogPrefactor3221 P X physical normalised := by
  refine ⟨⟨1, 1, 1, 1, 1, 1, -1⟩, 2, 0, 0, ?_⟩
  intro h
  have h1 := h.Cext_nonneg
  norm_num at h1

end V21LogBudget
end Erdos287
