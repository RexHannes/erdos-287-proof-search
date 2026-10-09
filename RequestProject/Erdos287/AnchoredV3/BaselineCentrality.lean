import Mathlib

/-!
# Anchored V3 — bounded-tilt / central-baseline interface

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Three distinct notions are separated here:

1. `CompatibleBaseline` — all inherited no-`00` / tail / kernel / guard / endpoint / reservation
   constraints hold;
2. `CentralBaseline` — additionally the correction-capacity window
   `η * C_all ≤ 1 - S_* ≤ (1 - η) * C_all`;
3. `BoundedTilt` — `|λ| * D / M ≤ C`.

The asymptotic implication `CentralBaseline → BoundedTilt` is **not** proved: it is recorded as
the named OPEN analytic interface `CentralityToBoundedTilt`, which is never inhabited.

The scope fact that *is* proved here is finite and exact: mobility capacity is only a
lower-order fraction of terminal capacity, so mobility cannot repair a baseline whose remaining
gap exceeds the combined terminal and mobility capacity
(`mobility_cannot_repair_macroscopic_gap`).
-/

namespace Erdos287
namespace AnchoredV3

/-- The inherited constraint bundle of a baseline. -/
structure BaselineConstraints where
  /-- the no-`00` constraint -/
  no00 : Prop
  /-- the tail constraint -/
  tail : Prop
  /-- the kernel constraint -/
  kernel : Prop
  /-- the guard constraint -/
  guard : Prop
  /-- the endpoint constraint -/
  endpoint : Prop
  /-- the reservation constraint -/
  reservation : Prop

/-- **A compatible baseline** satisfies every inherited constraint. -/
def CompatibleBaseline (cb : BaselineConstraints) : Prop :=
  cb.no00 ∧ cb.tail ∧ cb.kernel ∧ cb.guard ∧ cb.endpoint ∧ cb.reservation

/-- **A central baseline** is compatible and lies inside the correction-capacity window
`η * C_all ≤ 1 - S_* ≤ (1 - η) * C_all`. -/
def CentralBaseline (cb : BaselineConstraints) (eta Call Sstar : ℝ) : Prop :=
  CompatibleBaseline cb ∧ eta * Call ≤ 1 - Sstar ∧ 1 - Sstar ≤ (1 - eta) * Call

/-- **Bounded tilt**: `|λ| * D / M ≤ C`. -/
def BoundedTilt (lam D M C : ℝ) : Prop := |lam| * D / M ≤ C

/-- **OPEN analytic interface.**  The conditioned-column estimate that would turn a central
compatible baseline into a bounded tilt.  It is deliberately **not** inhabited, and it is not
assumed anywhere in the project. -/
def CentralityToBoundedTilt : Prop :=
  ∀ (cb : BaselineConstraints) (eta Call Sstar lam D M C : ℝ),
    CentralBaseline cb eta Call Sstar → BoundedTilt lam D M C

/-- **Mobility cannot repair a macroscopically off-window baseline.**

If the remaining gap `1 - S_*` strictly exceeds the total available correction capacity —
terminal capacity `C_all` plus mobility capacity `C_mob` — then no combination of a terminal
increment within `C_all` and a mobility increment within `C_mob` completes the baseline. -/
theorem mobility_cannot_repair_macroscopic_gap {Sstar Call Cmob dTerm dMob : ℝ}
    (hgap : Call + Cmob < 1 - Sstar) (hterm : dTerm ≤ Call) (hmob : dMob ≤ Cmob) :
    Sstar + dTerm + dMob ≠ 1 := by
  intro h
  linarith

/-- The mobility capacity is a lower-order fraction of the terminal capacity: an explicit
conditional inequality with a supplied fraction `κ < 1`. -/
theorem mobility_capacity_fraction {Call Cmob kappa : ℝ} (hk1 : kappa < 1)
    (hmob : Cmob ≤ kappa * Call) (hCall : 0 ≤ Call) : Cmob ≤ Call := by
  nlinarith

end AnchoredV3
end Erdos287
