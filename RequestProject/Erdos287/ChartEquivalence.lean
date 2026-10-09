import Mathlib
import RequestProject.Erdos287.LambdaWeights
import RequestProject.Erdos287.AllQResummation

/-!
# Erdős #287 effectivity — chart-equivalence and retired-theorem firewalls (§29)

```
CHART EQUIVALENCE       : KERNEL-PROVED (source typing)
DOUBLE-CHARGE FIREWALL  : KERNEL-PROVED
UNWEIGHTED CJOINT 0.09  : RETIRED / FIREWALLED
```

The λ-weighted covariance chart and the all-`q` resummation chart are two *representations*
of one and the same physical medium-`k` long-fibre source once the fibre modulus, the medium
cutoff `K0`, the replayed edge cutoff and the lane agree.  This is bookkeeping, not analysis:
nothing here bounds either chart.  Its content is the prohibition
`chart_double_charge_illegal`: a ledger may not charge both charts of one source as
independent errors.

§29.3 records the retired status of the unweighted per-`b` `C_joint ≤ 0.09` estimate.  The
reason is carried purely as metadata, and `unweightedCjoint_not_banked` makes it impossible
for a status file to import it from the banked list of closing estimates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace Effectivity

/-! ## §29.1  Source typing -/

/-- The identifying data of a physical medium-`k` long-fibre source: the fibre modulus `b`,
the medium cutoff `K0`, the replayed edge cutoff and the lane offset. -/
structure LongFibreSourceId where
  /-- The fibre modulus. -/
  fibre : ℕ
  /-- The medium cutoff (`K0 = 31`). -/
  mediumCutoff : ℕ
  /-- The replayed edge cutoff (`50` previously, `1000` now). -/
  edgeCutoff : ℕ
  /-- The lane offset. -/
  lane : ℕ
  deriving DecidableEq, Repr

/-- The two available representations of one long-fibre source. -/
inductive ChartRepresentation
  | lambdaCovariance
  | allQResummation
  deriving DecidableEq, Repr

/-- A ledger entry: a chart, the source it represents, and the charged amount. -/
structure ChartCharge where
  /-- Which representation is being charged. -/
  chart : ChartRepresentation
  /-- Which physical source it represents. -/
  source : LongFibreSourceId
  /-- The charged amount. -/
  amount : ℚ

/-- **`charts_same_source`.**  `KERNEL-PROVED`.  With all hypotheses and cutoffs matching,
the λ-weighted covariance chart and the all-`q` resummation chart carry the *same* source:
they are two representations, not two sources. -/
theorem charts_same_source (S : LongFibreSourceId) (x y : ℚ) :
    (ChartCharge.mk ChartRepresentation.lambdaCovariance S x).source
      = (ChartCharge.mk ChartRepresentation.allQResummation S y).source := rfl

/-- **`charts_distinct_representations`.**  `KERNEL-PROVED`.  The two charts are genuinely
different representations, so the equality above is a statement about the *source* only. -/
theorem charts_distinct_representations :
    ChartRepresentation.lambdaCovariance ≠ ChartRepresentation.allQResummation := by decide

/-! ## §29.2  The double-charge firewall -/

/-- A ledger is *chart-legal* when no source is charged through two different charts. -/
def ChartLegal (L : List ChartCharge) : Prop :=
  ∀ c₁ ∈ L, ∀ c₂ ∈ L, c₁.source = c₂.source → c₁.chart = c₂.chart

/-- **`chart_double_charge_illegal`.**  `KERNEL-PROVED`.  Charging both charts of one source
as independent errors is never chart-legal. -/
theorem chart_double_charge_illegal (S : LongFibreSourceId) (x y : ℚ) :
    ¬ ChartLegal [ChartCharge.mk ChartRepresentation.lambdaCovariance S x,
                  ChartCharge.mk ChartRepresentation.allQResummation S y] := by
  intro h
  have hmem₁ : ChartCharge.mk ChartRepresentation.lambdaCovariance S x ∈
      [ChartCharge.mk ChartRepresentation.lambdaCovariance S x,
       ChartCharge.mk ChartRepresentation.allQResummation S y] := by simp
  have hmem₂ : ChartCharge.mk ChartRepresentation.allQResummation S y ∈
      [ChartCharge.mk ChartRepresentation.lambdaCovariance S x,
       ChartCharge.mk ChartRepresentation.allQResummation S y] := by simp
  exact charts_distinct_representations (h _ hmem₁ _ hmem₂ rfl)

/-- **`chartLegal_single_chart`.**  `KERNEL-PROVED`.  In a chart-legal ledger every charge
attached to a given source uses one and the same chart. -/
theorem chartLegal_single_chart {L : List ChartCharge} (h : ChartLegal L)
    {c₁ c₂ : ChartCharge} (h₁ : c₁ ∈ L) (h₂ : c₂ ∈ L) (hs : c₁.source = c₂.source) :
    c₁.chart = c₂.chart := h c₁ h₁ c₂ h₂ hs

/-- **`chartLegal_singleton`.**  `KERNEL-PROVED`.  Charging a source through exactly one
chart is legal — the firewall forbids double charging, not charging. -/
theorem chartLegal_singleton (c : ChartCharge) : ChartLegal [c] := by
  intro c₁ h₁ c₂ h₂ _
  simp only [List.mem_singleton] at h₁ h₂
  rw [h₁, h₂]

/-! ## §29.3  The retired-theorem firewall -/

/-- Identifiers for the estimates tracked by the effectivity bank. -/
inductive EstimateId
  | unweightedPerBCjoint009
  | completePeriodEndpointIdentity
  | allQResummationAlgebra
  | lambdaFiniteAlgebra
  | edgeReplacementSemantics
  deriving DecidableEq, Repr

/-- Bank status of an estimate. -/
inductive BankStatus
  | banked
  | retired
  | openStatus
  deriving DecidableEq, Repr

/-- Retirement reasons, carried as metadata only. -/
inductive RetirementReason
  | contradictedByOnePointFibre
  deriving DecidableEq, Repr

/-- The bank status of each tracked estimate. -/
def estimateStatus : EstimateId → BankStatus
  | .unweightedPerBCjoint009 => .retired
  | .completePeriodEndpointIdentity => .banked
  | .allQResummationAlgebra => .banked
  | .lambdaFiniteAlgebra => .banked
  | .edgeReplacementSemantics => .banked

/-- The retirement reason, as pure status metadata. -/
def retirementReason : EstimateId → Option RetirementReason
  | .unweightedPerBCjoint009 => some .contradictedByOnePointFibre
  | _ => none

/-- The list of estimates that may be imported as banked closing estimates. -/
def bankedClosingEstimates : List EstimateId :=
  [.completePeriodEndpointIdentity, .allQResummationAlgebra, .lambdaFiniteAlgebra,
   .edgeReplacementSemantics]

/-- **`unweightedCjoint_retired`.**  `KERNEL-PROVED`.  The unweighted per-`b`
`C_joint ≤ 0.09` estimate is recorded as retired, with its reason as metadata. -/
theorem unweightedCjoint_retired :
    estimateStatus .unweightedPerBCjoint009 = BankStatus.retired ∧
      retirementReason .unweightedPerBCjoint009 = some .contradictedByOnePointFibre :=
  ⟨rfl, rfl⟩

/-- **`unweightedCjoint_not_banked`.**  `KERNEL-PROVED`.  It is impossible to import the
retired estimate as a banked closing estimate. -/
theorem unweightedCjoint_not_banked :
    EstimateId.unweightedPerBCjoint009 ∉ bankedClosingEstimates := by decide

/-- **`bankedClosingEstimates_are_banked`.**  `KERNEL-PROVED`.  Everything on the banked list
really has banked status. -/
theorem bankedClosingEstimates_are_banked :
    ∀ e ∈ bankedClosingEstimates, estimateStatus e = BankStatus.banked := by decide

/-- **`retired_ne_banked`.**  `KERNEL-PROVED`. -/
theorem retired_ne_banked : BankStatus.retired ≠ BankStatus.banked := by decide

end Effectivity
end Erdos287
