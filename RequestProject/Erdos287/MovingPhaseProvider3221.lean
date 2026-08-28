import Mathlib
import RequestProject.Erdos287.NormalForm3221

/-!
# V18, Phase F — the phase-provider dictionary, the small-`Z` range compiler and the
large-range analytic firewall

## Status repair (the point of this file)

A previous chat-level ledger recorded

```
PASCADI101-LEVELWISE-PHASE-LS45   : PASS
PASCADI102-MOVINGPHASE45          : PASS
PASCADI39-MOVINGPHASE-EXTENSION45 : PASS
3221-SOURCE-MOVINGPHASE-DI45      : CLOSED
```

Those four labels are **retracted as controlling status**.  They never had a Lean witness:
a repository-wide search finds no declaration mentioning a levelwise/moving phase, and no
inhabitant of any phase provider exists here.  The safe distinctions, recorded as
*metadata only*, are

* **A** fixed-level scaling-matrix phase covariance — external published mathematics;
* **B** one common fixed `ω` in the averaged-level theorem — external published
  mathematics;
* **C** arbitrary level-dependent `ω_q` in the smaller fixed-level spectral range —
  external analytic input, a *safe conditional provider*;
* **D** arbitrary `ω_q` in the larger averaged spectral range — **open analytic**.

None of A–D is formalised as an axiom, and none is inhabited.  What is formalised is:

1. the exact rational **range test** separating the small-`Z` provider range from the
   large range (`InSmallZRange`, with its algebraic characterisation and the dichotomy);
2. an **uninhabited** per-level small-`Z` analytic interface for the *specific* pinned
   3221 source, and a genuine Lean-proved compiler from it (plus an explicit counting
   hypothesis) to the V17 socket `DIKuznetsov3221Input`;
3. an **uninhabited** large-range interface, kept strictly separate, together with the
   firewall theorem that the two interfaces can never both apply to the same source.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators

namespace Erdos287
namespace Phase3221

open Erdos287.DI3221
open Erdos287.NormalForm3221

/-! ## §1. The provider dictionary A–D (metadata only) -/

/-- The four phase regimes that must be kept apart. -/
inductive PhaseRegime
  /-- **A** — fixed-level scaling-matrix phase covariance. -/
  | fixedLevelCovariance
  /-- **B** — one common fixed `ω` in the averaged-level theorem. -/
  | commonOmegaAveraged
  /-- **C** — arbitrary level-dependent `ω_q`, smaller fixed-level spectral range. -/
  | levelDependentSmallRange
  /-- **D** — arbitrary `ω_q`, larger averaged spectral range. -/
  | levelDependentLargeRange
  deriving DecidableEq, Repr

/-- The provenance classification of a regime.  This is a *label*, not a mathematical
assertion: nothing in this project proves or assumes any of A–D. -/
inductive Provenance
  /-- Published external mathematics. -/
  | published
  /-- External analytic input available as a safe conditional provider. -/
  | conditionalProvider
  /-- Open analytic. -/
  | openAnalytic
  deriving DecidableEq, Repr

/-- The dictionary. -/
def provenance : PhaseRegime → Provenance
  | .fixedLevelCovariance => .published
  | .commonOmegaAveraged => .published
  | .levelDependentSmallRange => .conditionalProvider
  | .levelDependentLargeRange => .openAnalytic

/-- The large averaged range is **not** a published regime: the dictionary keeps D apart
from A and B. -/
theorem largeRange_not_published :
    provenance .levelDependentLargeRange = .openAnalytic ∧
      provenance .levelDependentLargeRange ≠ provenance .fixedLevelCovariance ∧
      provenance .levelDependentLargeRange ≠ provenance .commonOmegaAveraged := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

/-- The small fixed-level range is a conditional provider, never a published theorem. -/
theorem smallRange_is_conditional :
    provenance .levelDependentSmallRange = .conditionalProvider := rfl

/-! ## §2. The exact small-`Z` range test -/

/-- The exact normalised small-`Z` condition `Z ≤ max(1, Q_level / N₀)`. -/
def InSmallZRange (Z Qlevel N0 : ℚ) : Prop := Z ≤ max 1 (Qlevel / N0)

instance (Z Qlevel N0 : ℚ) : Decidable (InSmallZRange Z Qlevel N0) := by
  unfold InSmallZRange; infer_instance

/-- **The range compiler.**  For `N₀ > 0` the small-`Z` condition is exactly
`Z ≤ 1 ∨ Z N₀ ≤ Q_level`. -/
theorem inSmallZRange_iff {Z Qlevel N0 : ℚ} (hN : 0 < N0) :
    InSmallZRange Z Qlevel N0 ↔ (Z ≤ 1 ∨ Z * N0 ≤ Qlevel) := by
  unfold InSmallZRange
  rw [le_max_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ((le_div_iff₀ hN).mp h)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ((le_div_iff₀ hN).mpr h)

/-- Anything of size at most `1` is in the small-`Z` range. -/
theorem inSmallZRange_of_le_one {Z Qlevel N0 : ℚ} (h : Z ≤ 1) :
    InSmallZRange Z Qlevel N0 := le_max_of_le_left h

/-- The complementary large range. -/
def InLargeZRange (Z Qlevel N0 : ℚ) : Prop := ¬ InSmallZRange Z Qlevel N0

/-- **Dichotomy** — every source is in exactly one of the two ranges. -/
theorem smallZ_or_large (Z Qlevel N0 : ℚ) :
    InSmallZRange Z Qlevel N0 ∨ InLargeZRange Z Qlevel N0 := em _

/-- **Disjointness** — the two ranges never overlap. -/
theorem not_smallZ_and_large {Z Qlevel N0 : ℚ}
    (h₁ : InSmallZRange Z Qlevel N0) (h₂ : InLargeZRange Z Qlevel N0) : False := h₂ h₁

/-- A concrete separating example, so the range test is not vacuous on either side:
`Z = 1/2` is small and `Z = 5` is large for `Q_level = 2, N₀ = 1`. -/
theorem range_test_nonvacuous :
    InSmallZRange (1 / 2) 2 1 ∧ InLargeZRange 5 2 1 := by
  refine ⟨?_, ?_⟩
  · unfold InSmallZRange; norm_num
  · unfold InLargeZRange InSmallZRange; norm_num

/-! ## §3. The per-level decomposition of the pinned normal form

These are unconditional theorems about the *pinned* data; they assert nothing analytic. -/

variable {S : BalancedSeven3221CompletedSource}

/-- The level-`r` slice of the pinned normal form. -/
noncomputable def levelValue (F : BalancedSeven3221NormalForm S) (r : ℕ) : ℂ :=
  ∑ s ∈ F.Sbox,
    (∑ m ∈ F.Mbox, F.coeff m r s) *
    (∑ n ∈ F.Nbox, phase ((n : ℝ) * F.omega r s)) *
    (∑ c ∈ F.Cbox, F.cWeight s c * F.kloostLeg s c)

/-- The completed value is the sum of its level slices — this is exactly the pinned
normal-form equality, restated. -/
theorem completedValue_eq_sum_levelValue (F : BalancedSeven3221NormalForm S) :
    S.completedValue = ∑ r ∈ F.Rbox, levelValue F r := F.normalForm

/-- **Levelwise aggregation.**  A uniform per-level bound gives the trivial (no cancellation
between levels) bound on the completed value. -/
theorem completedValue_norm_le (F : BalancedSeven3221NormalForm S) {B : ℝ}
    (h : ∀ r ∈ F.Rbox, ‖levelValue F r‖ ≤ B) :
    ‖S.completedValue‖ ≤ (F.Rbox.card : ℝ) * B := by
  rw [completedValue_eq_sum_levelValue F]
  calc ‖∑ r ∈ F.Rbox, levelValue F r‖ ≤ ∑ r ∈ F.Rbox, ‖levelValue F r‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _r ∈ F.Rbox, B := Finset.sum_le_sum h
    _ = (F.Rbox.card : ℝ) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ## §4. The small-`Z` analytic interface — `UNINHABITED` -/

/-- **`3221-PERLEVEL-SMALLZ-ADAPTER45` — `CONDITIONAL_COMPILER`; the interface itself is
`OPEN_ANALYTIC / UNINHABITED`.**

The *only* analytic estimate the small-`Z` route needs, stated for one specific pinned
source `F` and never generically: in the small-`Z` range, each individual level slice
obeys `‖K_r‖ ≤ levelTarget`.

This is **not** a Pascadi/Kuznetsov theorem, **not** an `axiom`, and **no inhabitant is
constructed anywhere in this project.** -/
structure PerLevelPhaseSmallZ3221Input (F : BalancedSeven3221NormalForm S)
    (X levelTarget : ℝ) : Prop where
  /-- Asymptotic regime. -/
  X_gt_one : 1 < X
  /-- The source is in the small-`Z` provider range (a *rational* side condition). -/
  smallZ : InSmallZRange F.Z F.Qlevel F.N0
  /-- **The open per-level analytic estimate.** -/
  levelBound : ∀ r ∈ F.Rbox, ‖levelValue F r‖ ≤ levelTarget

/-- **The small-`Z` compiler.**  `PROVED_COMPILER / CONDITIONAL`.

Per-level small-`Z` input **+** the explicit level-count budget
`#R · levelTarget ≤ X^{39/35 − η}` **⇒** the V17 analytic socket `DIKuznetsov3221Input`.
Both the input and the socket remain uninhabited; this theorem inhabits nothing. -/
theorem diKuznetsov_of_perLevelSmallZ {F : BalancedSeven3221NormalForm S}
    {X levelTarget eta : ℝ}
    (hin : PerLevelPhaseSmallZ3221Input F X levelTarget)
    (heta : 0 < eta)
    (hbudget : (F.Rbox.card : ℝ) * levelTarget ≤ X ^ ((39 / 35 : ℝ) - eta)) :
    DIKuznetsov3221Input S X eta :=
  { X_gt_one := hin.X_gt_one
    eta_pos := heta
    bound := le_trans (completedValue_norm_le F hin.levelBound) hbudget }

/-- The small-`Z` side condition, in the algebraic form produced by the range compiler. -/
theorem smallZ_condition_iff {F : BalancedSeven3221NormalForm S} {X levelTarget : ℝ}
    (hin : PerLevelPhaseSmallZ3221Input F X levelTarget) :
    F.Z ≤ 1 ∨ F.Z * F.N0 ≤ F.Qlevel :=
  (inSmallZRange_iff F.N0_pos).mp hin.smallZ

/-! ## §5. The large-range analytic firewall — `OPEN_ANALYTIC / UNINHABITED` -/

/-- **`PASCADI101-LEVELWISE-PHASE-LARGERANGE45` — `OPEN_ANALYTIC / UNINHABITED`.**

The levelwise phase estimate in the *larger averaged* spectral range (regime D).  It is a
strictly different statement from the small-`Z` interface, it is **not** implied by
scaling-matrix covariance (regime A), and **no inhabitant is constructed anywhere in this
project.** -/
structure LevelwisePhaseLargeRange3221Input (F : BalancedSeven3221NormalForm S)
    (X levelTarget : ℝ) : Prop where
  /-- Asymptotic regime. -/
  X_gt_one : 1 < X
  /-- The source is in the **large** range: the small-`Z` provider does not apply. -/
  largeRange : InLargeZRange F.Z F.Qlevel F.N0
  /-- **The open analytic estimate in the large range.** -/
  levelBound : ∀ r ∈ F.Rbox, ‖levelValue F r‖ ≤ levelTarget

/-- **The firewall.**  For one and the same pinned source the small-`Z` provider and the
large-range input can never both apply: the two ranges are disjoint.  Consequently a
small-`Z` estimate can never be relabelled as a large-range estimate. -/
theorem smallZ_largeRange_firewall {F : BalancedSeven3221NormalForm S}
    {X levelTarget levelTarget' : ℝ}
    (h₁ : PerLevelPhaseSmallZ3221Input F X levelTarget)
    (h₂ : LevelwisePhaseLargeRange3221Input F X levelTarget') : False :=
  not_smallZ_and_large h₁.smallZ h₂.largeRange

/-- The large-range regime is classified `openAnalytic` in the dictionary, so no published
regime (A or B) discharges it. -/
theorem largeRange_regime_open :
    provenance .levelDependentLargeRange ≠ provenance .fixedLevelCovariance := by decide

end Phase3221
end Erdos287
