import RequestProject.Erdos287.AnchoredV2.Capacity

/-!
# Anchored V2 — normalised capacity slack and the negative capacity certificate

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

For a nonnegative edge weighting of total mass `1` the **normalised capacity slack** of a port
system is

`𝔖 λ = (∑_v C_v(λ)) − 1`.

This file proves:

* `slack_mono`: shrinking the local relations cannot increase the slack;
* `not_feasible_of_slack_neg`: negative slack implies integral infeasibility;
* the finite certificate record `NegativeCapacityCertificate` and
  `NegativeCapacityCertificate.not_feasible`.

The certificate is a **sound, one-directional** rejection test.  No converse is proved, no LP
duality is used, and no claim is made that such a certificate exists for any particular
arithmetic kernel.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV2

namespace PortSystem

variable {E : Type*} [DecidableEq E]

/-- The normalised capacity slack `∑_v C_v(λ) − 1`, for weightings of total mass `1`. -/
def slack (S : PortSystem E) (lam : E → ℚ) : ℚ := (∑ v ∈ S.Blocks, S.cap lam v) - 1

/-- **`slack_mono`.**  `KERNEL-PROVED`.  Relation shrinkage cannot increase the slack. -/
theorem slack_mono {S S' : PortSystem E} {lam : E → ℚ} (hlam : ∀ e, 0 ≤ lam e)
    (hBlocks : S'.Blocks = S.Blocks) (hsub : ∀ v, S'.L v ⊆ S.L v) :
    S'.slack lam ≤ S.slack lam := by
  unfold slack
  have : ∑ v ∈ S'.Blocks, S'.cap lam v ≤ ∑ v ∈ S.Blocks, S.cap lam v := by
    rw [hBlocks]
    exact Finset.sum_le_sum fun v _ => cap_mono hlam (hsub v)
  linarith

/-- **`not_feasible_of_slack_neg`.**  `KERNEL-PROVED`.  Negative normalised slack implies
integral infeasibility. -/
theorem not_feasible_of_slack_neg {S : PortSystem E} (hwf : S.WellFormed) {lam : E → ℚ}
    (hlam : ∀ e, 0 ≤ lam e) (htotal : ∑ e ∈ S.Edges, lam e = 1) (hslack : S.slack lam < 0) :
    ¬ S.Feasible := by
  intro hfeas
  have h := capacity_sound hwf hfeas hlam
  rw [htotal] at h
  unfold slack at hslack
  linarith

/-- **`not_feasible_of_capacity_lt`.**  `KERNEL-PROVED`.  The unnormalised weighted rejection
certificate: if the total block capacity is strictly below the total edge weight then the port
system is integrally infeasible. -/
theorem not_feasible_of_capacity_lt {S : PortSystem E} (hwf : S.WellFormed) {lam : E → ℚ}
    (hlam : ∀ e, 0 ≤ lam e)
    (hlt : (∑ v ∈ S.Blocks, S.cap lam v) < ∑ e ∈ S.Edges, lam e) :
    ¬ S.Feasible := by
  intro hfeas
  exact absurd (capacity_sound hwf hfeas hlam) (not_le.2 hlt)

end PortSystem

/-- A finite **negative capacity certificate** for a port system: a nonnegative edge weighting
of total mass `1` whose normalised capacity slack is negative. -/
structure NegativeCapacityCertificate {E : Type*} [DecidableEq E] (S : PortSystem E) where
  /-- the edge weighting -/
  lam : E → ℚ
  /-- the weights are nonnegative -/
  lam_nonneg : ∀ e, 0 ≤ lam e
  /-- the weights have total mass one -/
  total_one : ∑ e ∈ S.Edges, lam e = 1
  /-- the normalised capacity slack is negative -/
  slack_neg : S.slack lam < 0

/-- **`NegativeCapacityCertificate.not_feasible`.**  `KERNEL-PROVED`.  A negative capacity
certificate rejects the port system: it has no integral solution.  (Sound only; the converse
is **not** claimed.) -/
theorem NegativeCapacityCertificate.not_feasible {E : Type*} [DecidableEq E] {S : PortSystem E}
    (hwf : S.WellFormed) (cert : NegativeCapacityCertificate S) : ¬ S.Feasible :=
  PortSystem.not_feasible_of_slack_neg hwf cert.lam_nonneg cert.total_one cert.slack_neg

end AnchoredV2
end Erdos287
