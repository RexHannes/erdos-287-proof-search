import Mathlib
import RequestProject.Erdos287.ProperGammaMultiplicityLedger
import RequestProject.Erdos287.ProperGammaAdmission
import RequestProject.Erdos287.Early4490RationalJetSource

/-!
# Erdős #287 effectivity — the EARLY_4490 rational-jet ledger (§48)

```
C3 OWNERSHIP ARITHMETIC 8.03976032e-9    : KERNEL-PROVED (exact rationals)
SLAB PARTITION (EARLY / LATE)            : KERNEL-PROVED
EARLY_4490 RANGE DATA                    : CERTIFICATE-BACKED INPUTS + KERNEL ARITHMETIC
J3 TARGET 6.33976032e-9                  : KERNEL-PROVED BUDGET ARITHMETIC
Jψ TARGET 4.03976032e-9                  : KERNEL-PROVED BUDGET ARITHMETIC
ALTERNATIVE-CHART FIREWALL               : KERNEL-PROVED
REPLACEMENT ERRORS 1.7e-9 / 4e-9         : CERTIFICATE-BACKED (never proved here)
LATE SUBSLAB |R_{≥6}|/B_X < 7.8e-9       : CERTIFICATE-BACKED
ERDŐS #287                               : OPEN
```

Exact ownership arithmetic, continuing the banked proper-γ ledger of §40 (whose values are
**unchanged**):

    parent allocation 8.14976032e-9 − C3 allocation 1.1e-10 = 8.03976032e-9.

The `C3` remainder ratio `|2 R[C3]|/B_X < 1.1e-10` itself is `CERTIFICATE_BACKED` (§42), never
a theorem.

Slab status data uses exact rationals: `EARLY: 429/10 ≤ L < 503/10`, `LATE: 503/10 ≤ L ≤ 125/2`;
the partition is kernel-proved, while the late-subslab bound `|R_{≥6}|/B_X < 7.8e-9` is a typed
certificate.

Replacement budgets (the two charts are **alternatives**):

    three-term: |J − J3|/B_X < 1.7e-9  ⟹ sufficient target |J3|/B_X < 6.33976032e-9,
    one-term:   |J − Jψ|/B_X < 4e-9    ⟹ sufficient target |Jψ|/B_X < 4.03976032e-9,

with only the rational subtraction kernel-proved and
`rationalJet_alternative_chart_no_double_charge` forbidding a simultaneous charge.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace Effectivity

/-! ## §48.1  The `C3` ownership arithmetic -/

/-- The early joint allocation after the `C3` charge: `8.03976032e-9`. -/
def earlyJointAllocation : ℚ := 803976032 / 10 ^ 17

/-- **`c3_ownership_arithmetic`.**  `KERNEL-PROVED`.  The exact ownership arithmetic:
`8.14976032e-9 − 1.1e-10 = 8.03976032e-9`. -/
theorem c3_ownership_arithmetic : parentAvailable - c3Allocation = earlyJointAllocation := by
  unfold parentAvailable c3Allocation earlyJointAllocation; norm_num

/-- **`properGamma_ledger_unchanged_by_early4490`.**  `KERNEL-PROVED`.  The banked proper-γ
ledger values are untouched by this layer. -/
theorem properGamma_ledger_unchanged_by_early4490 :
    parentAvailable = 814976032 / 10 ^ 17 ∧ childRemaining = 37976032 / 10 ^ 17 ∧
      properGammaTarget = 7204976032 / 10 ^ 17 := ⟨rfl, rfl, rfl⟩

/-! ## §48.2  The early / late slab partition -/

/-- The slab lower endpoint `42.9`. -/
def slabLo : ℚ := 429 / 10

/-- The early/late split point `50.3`. -/
def slabMid : ℚ := 503 / 10

/-- The slab upper endpoint `62.5`. -/
def slabHi : ℚ := 125 / 2

/-- The two slab statuses. -/
inductive SlabStatus
  | early
  | late
  deriving DecidableEq, Repr

/-- `L` lies in the EARLY slab: `42.9 ≤ L < 50.3`. -/
def IsEarlySlab (L : ℚ) : Prop := slabLo ≤ L ∧ L < slabMid

/-- `L` lies in the LATE slab: `50.3 ≤ L ≤ 62.5`. -/
def IsLateSlab (L : ℚ) : Prop := slabMid ≤ L ∧ L ≤ slabHi

/-- **`slab_partition`.**  `KERNEL-PROVED`.  The two slabs partition `[42.9, 62.5]`: every
admissible `L` lies in exactly one of them. -/
theorem slab_partition {L : ℚ} (h : slabLo ≤ L ∧ L ≤ slabHi) :
    (IsEarlySlab L ∨ IsLateSlab L) ∧ ¬ (IsEarlySlab L ∧ IsLateSlab L) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · rcases lt_or_ge L slabMid with hlt | hge
    · exact Or.inl ⟨h1, hlt⟩
    · exact Or.inr ⟨hge, h2⟩
  · rintro ⟨⟨-, hlt⟩, ⟨hge, -⟩⟩
    exact absurd hlt (not_lt.2 hge)

/-- **`slab_endpoints_exact`.**  `KERNEL-PROVED`.  The endpoints are exact rationals; no
decimal real constant occurs in the logical core. -/
theorem slab_endpoints_exact :
    slabLo = 429 / 10 ∧ slabMid = 503 / 10 ∧ slabHi = 125 / 2 ∧ slabLo < slabMid ∧
      slabMid < slabHi := by
  refine ⟨rfl, rfl, rfl, by unfold slabLo slabMid; norm_num, by unfold slabMid slabHi; norm_num⟩

/-- A typed numerical certificate for a ratio bound `|R|/B_X < bound`. -/
structure RatioCertificate where
  /-- A label for the certified object. -/
  label : ℕ
  /-- The claimed ratio. -/
  ratio : ℚ
  /-- The certified strict bound. -/
  bound : ℚ
  /-- The externally supplied certificate. -/
  certified : ratio < bound

/-- The late-subslab bound `7.8e-9`. -/
def lateSubslabBound : ℚ := 78 / 10 ^ 10

/-- **`lateSubslab_certificate_not_proved`.**  `KERNEL-PROVED`.  The late-subslab analytic
inequality is *not* proved here: the certificate type is inhabited by data with no analytic
content. -/
theorem lateSubslab_certificate_not_proved :
    ∃ C : RatioCertificate, C.bound = lateSubslabBound ∧ C.ratio = 0 :=
  ⟨⟨0, 0, lateSubslabBound, by unfold lateSubslabBound; norm_num⟩, rfl, rfl⟩

/-! ## §48.3  EARLY_4490 range data -/

/-- The source range ceiling for odd `a`. -/
def oddACeiling : ℕ := 4489

/-- The `c = 2` lane ceiling for odd `a`. -/
def c2LaneCeiling : ℕ := 2245

/-- The source range bound `z < 7.94e10`, as an exact rational. -/
def zRangeBound : ℚ := 794 * 10 ^ 8

/-- The source range bound `p < 291200`. -/
def pRangeBound : ℚ := 291200

/-- The source range bound `q < 3.913e9`, as an exact rational. -/
def qRangeBound : ℚ := 3913 * 10 ^ 6

/-- **`early4490_range_arithmetic`.**  `KERNEL-PROVED`.  The finite arithmetic consequences of
the declared range data: the ceilings are odd, the `c = 2` lane ceiling is exactly the largest
`a` with `2a ≤ 4490`, and the three real range bounds are strictly ordered
`p < q < z`. -/
theorem early4490_range_arithmetic :
    ¬ 2 ∣ oddACeiling ∧ ¬ 2 ∣ c2LaneCeiling ∧ 2 * c2LaneCeiling = oddACeiling + 1 ∧
      (∀ a : ℕ, 2 * a ≤ 2 * c2LaneCeiling ↔ a ≤ c2LaneCeiling) ∧
      pRangeBound < qRangeBound ∧ qRangeBound < zRangeBound := by
  refine ⟨by decide, by decide, by decide, fun a => by omega, ?_, ?_⟩
  · unfold pRangeBound qRangeBound; norm_num
  · unfold qRangeBound zRangeBound; norm_num

/-- **`range_integer_consequence`.**  `KERNEL-PROVED`.  A strict rational range bound on a
natural number yields the expected integer consequence. -/
theorem range_integer_consequence {n : ℕ} (h : (n : ℚ) < pRangeBound) : n ≤ 291199 := by
  have : (n : ℚ) < 291200 := by simpa [pRangeBound] using h
  have hn : n < 291200 := by exact_mod_cast this
  omega

/-- **`range_data_are_certificates`.**  `KERNEL-PROVED`.  The range data are declared inputs:
possessing a `RatioCertificate` for them adds no analytic content. -/
theorem range_data_are_certificates :
    ∃ C : RatioCertificate, C.bound = zRangeBound ∧ C.ratio = 0 :=
  ⟨⟨1, 0, zRangeBound, by unfold zRangeBound; norm_num⟩, rfl, rfl⟩

/-! ## §48.4  The replacement budgets -/

/-- The three-term chart replacement error allowance `1.7e-9`. -/
def repl3Bound : ℚ := 17 / 10 ^ 10

/-- The one-term chart replacement error allowance `4e-9`. -/
def replPsiBound : ℚ := 4 / 10 ^ 9

/-- The sufficient three-term target `6.33976032e-9`. -/
def target3 : ℚ := 633976032 / 10 ^ 17

/-- The sufficient one-term target `4.03976032e-9`. -/
def targetPsi : ℚ := 403976032 / 10 ^ 17

/-- **`target3_budget_arithmetic`.**  `KERNEL-PROVED`.
`8.03976032e-9 − 1.7e-9 = 6.33976032e-9`. -/
theorem target3_budget_arithmetic : earlyJointAllocation - repl3Bound = target3 := by
  unfold earlyJointAllocation repl3Bound target3; norm_num

/-- **`targetPsi_budget_arithmetic`.**  `KERNEL-PROVED`.
`8.03976032e-9 − 4e-9 = 4.03976032e-9`. -/
theorem targetPsi_budget_arithmetic : earlyJointAllocation - replPsiBound = targetPsi := by
  unfold earlyJointAllocation replPsiBound targetPsi; norm_num

/-- **`replacement_certificates_not_proved`.**  `KERNEL-PROVED`.  Neither replacement error is
proved here; both are typed certificates. -/
theorem replacement_certificates_not_proved :
    (∃ C : RatioCertificate, C.bound = repl3Bound ∧ C.ratio = 0) ∧
      (∃ C : RatioCertificate, C.bound = replPsiBound ∧ C.ratio = 0) :=
  ⟨⟨⟨2, 0, repl3Bound, by unfold repl3Bound; norm_num⟩, rfl, rfl⟩,
   ⟨⟨3, 0, replPsiBound, by unfold replPsiBound; norm_num⟩, rfl, rfl⟩⟩

/-! ## §48.5  The alternative-chart firewall -/

/-- The two legal rational-jet charts. -/
inductive JetChart
  | threeTerm
  | oneTerm
  deriving DecidableEq, Repr

/-- The replacement error charged by a chart. -/
def chartReplacement : JetChart → ℚ
  | .threeTerm => repl3Bound
  | .oneTerm => replPsiBound

/-- The sufficient target of a chart. -/
def chartTarget : JetChart → ℚ
  | .threeTerm => target3
  | .oneTerm => targetPsi

/-- **`chart_budget_closes`.**  `KERNEL-PROVED`.  Each chart's replacement charge plus its
target is exactly the early joint allocation. -/
theorem chart_budget_closes (c : JetChart) :
    chartReplacement c + chartTarget c = earlyJointAllocation := by
  cases c
  · unfold chartReplacement chartTarget repl3Bound target3 earlyJointAllocation; norm_num
  · unfold chartReplacement chartTarget replPsiBound targetPsi earlyJointAllocation; norm_num

/-- The (illegal) total obtained by charging *both* replacement errors and still asking for a
chart target. -/
def doubleChargedJetTotal : ℚ := repl3Bound + replPsiBound + target3

/-- **`rationalJet_alternative_chart_no_double_charge`.**  `KERNEL-PROVED`.  The `J3` chart is
legal, the `Jψ` chart is legal, and charging both replacement errors simultaneously is
illegal: it strictly overspends the early joint allocation, whereas each chart closes it
exactly. -/
theorem rationalJet_alternative_chart_no_double_charge :
    chartReplacement .threeTerm + chartTarget .threeTerm = earlyJointAllocation ∧
      chartReplacement .oneTerm + chartTarget .oneTerm = earlyJointAllocation ∧
      earlyJointAllocation < doubleChargedJetTotal ∧
      chartReplacement .threeTerm ≠ chartReplacement .oneTerm := by
  refine ⟨chart_budget_closes _, chart_budget_closes _, ?_, ?_⟩
  · unfold doubleChargedJetTotal repl3Bound replPsiBound target3 earlyJointAllocation; norm_num
  · unfold chartReplacement repl3Bound replPsiBound; norm_num

/-! ## §48.6  The remaining numerical certificate objects -/

/-- A typed numerical certificate object for a declared analytic constant. -/
structure NumericalCertificate where
  /-- A label for the constant. -/
  label : ℕ
  /-- The claimed value. -/
  value : ℚ
  /-- The declared strict bound. -/
  bound : ℚ
  /-- The externally supplied certificate. -/
  certified : value < bound

/-- The declared bound `‖W''‖_∞ < 2110`. -/
def normW2Bound : ℚ := 2110

/-- The declared bound `‖W'''‖_1 < 9800`. -/
def normW3Bound : ℚ := 9800

/-- **`numerical_certificates_not_theorems`.**  `KERNEL-PROVED`.  The declared analytic
constants are typed but not proved: the certificate structure is inhabited by data with no
analytic content, so a certificate object can never inhabit the missing analytic target. -/
theorem numerical_certificates_not_theorems :
    (∃ C : NumericalCertificate, C.bound = normW2Bound ∧ C.value = 0) ∧
      (∃ C : NumericalCertificate, C.bound = normW3Bound ∧ C.value = 0) ∧
      ¬ EarlyJointTarget 1 1 :=
  ⟨⟨⟨4, 0, normW2Bound, by unfold normW2Bound; norm_num⟩, rfl, rfl⟩,
   ⟨⟨5, 0, normW3Bound, by unfold normW3Bound; norm_num⟩, rfl, rfl⟩,
   earlyJoint_target_open⟩

end Effectivity
end Erdos287
