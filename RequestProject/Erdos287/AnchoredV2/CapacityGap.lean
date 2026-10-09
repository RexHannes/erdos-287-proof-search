import RequestProject.Erdos287.AnchoredV2.CapacityCertificate

/-!
# Anchored V2 — the capacity incompleteness firewall

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Weighted capacity inequalities are **sound but not complete**.  This file exhibits a finite
abstract example: two blocks joined by four contact ports, with

* left admissible port sets `{{0,1}, {2,3}}`,
* right admissible port sets `{{0,2}, {1,3}}`.

Proved:

1. `gap_not_feasible` — no pair of integral local states covers all four contact edges;
2. `gap_no_negativeCapacityCertificate` — *no* nonnegative weighting has negative capacity
   slack, so no Level-1 negative capacity certificate exists;
3. `gap_fractional_mixture` — the `50/50` mixture on each side has expected coverage `1` on
   every contact edge.

Hence integral infeasibility does **not** imply the existence of a negative Level-1 capacity
certificate.  Nothing is asserted about actual arithmetic kernels by this abstract example.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV2

/-- Two blocks, four contact ports; the abstract capacity-incompleteness example. -/
def gapSystem : PortSystem ℕ where
  Blocks := {0, 1}
  Edges := {0, 1, 2, 3}
  ep := fun _ => (0, 1)
  L := fun v => if v = 0 then {{0, 1}, {2, 3}} else if v = 1 then {{0, 2}, {1, 3}} else ∅

theorem gapSystem_wellFormed : gapSystem.WellFormed := by
  intro e _
  constructor <;> simp [gapSystem]

/-- **`gap_not_feasible`.**  No pair of integral local states covers all four contact edges. -/
theorem gap_not_feasible : ¬ gapSystem.Feasible := by
  rintro ⟨β, hβ, hcov⟩
  have h0 : β 0 = ({0, 1} : Finset ℕ) ∨ β 0 = ({2, 3} : Finset ℕ) := by
    have h := hβ 0 (by decide)
    simpa [gapSystem, Finset.mem_insert, Finset.mem_singleton] using h
  have h1 : β 1 = ({0, 2} : Finset ℕ) ∨ β 1 = ({1, 3} : Finset ℕ) := by
    have h := hβ 1 (by decide)
    simpa [gapSystem, Finset.mem_insert, Finset.mem_singleton] using h
  have c : ∀ e ∈ ({0, 1, 2, 3} : Finset ℕ), e ∈ β 0 ∨ e ∈ β 1 := by
    intro e he
    simpa [gapSystem] using hcov e (by simpa [gapSystem] using he)
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · have h3 := c 3 (by decide); rw [h0, h1] at h3; revert h3; decide
  · have h2 := c 2 (by decide); rw [h0, h1] at h2; revert h2; decide
  · have h1' := c 1 (by decide); rw [h0, h1] at h1'; revert h1'; decide
  · have h0' := c 0 (by decide); rw [h0, h1] at h0'; revert h0'; decide

/-- **`gap_no_negativeCapacityCertificate`.**  No nonnegative edge weighting of total mass one
has negative capacity slack on the example: the Level-1 capacity test never rejects it. -/
theorem gap_no_negativeCapacityCertificate (cert : NegativeCapacityCertificate gapSystem) :
    False := by
  set lam := cert.lam with hlamdef
  have hL0a : ({0, 1} : Finset ℕ) ∈ gapSystem.L 0 := by decide
  have hL0b : ({2, 3} : Finset ℕ) ∈ gapSystem.L 0 := by decide
  have hL1a : ({0, 2} : Finset ℕ) ∈ gapSystem.L 1 := by decide
  have hL1b : ({1, 3} : Finset ℕ) ∈ gapSystem.L 1 := by decide
  have e01 : ∑ e ∈ ({0, 1} : Finset ℕ), lam e = lam 0 + lam 1 :=
    Finset.sum_pair (by norm_num)
  have e23 : ∑ e ∈ ({2, 3} : Finset ℕ), lam e = lam 2 + lam 3 :=
    Finset.sum_pair (by norm_num)
  have e02 : ∑ e ∈ ({0, 2} : Finset ℕ), lam e = lam 0 + lam 2 :=
    Finset.sum_pair (by norm_num)
  have e13 : ∑ e ∈ ({1, 3} : Finset ℕ), lam e = lam 1 + lam 3 :=
    Finset.sum_pair (by norm_num)
  have c0a : lam 0 + lam 1 ≤ gapSystem.cap lam 0 := e01 ▸ gapSystem.le_cap lam hL0a
  have c0b : lam 2 + lam 3 ≤ gapSystem.cap lam 0 := e23 ▸ gapSystem.le_cap lam hL0b
  have c1a : lam 0 + lam 2 ≤ gapSystem.cap lam 1 := e02 ▸ gapSystem.le_cap lam hL1a
  have c1b : lam 1 + lam 3 ≤ gapSystem.cap lam 1 := e13 ▸ gapSystem.le_cap lam hL1b
  have hsum4 : ∑ e ∈ gapSystem.Edges, lam e = lam 0 + lam 1 + lam 2 + lam 3 := by
    show ∑ e ∈ ({0, 1, 2, 3} : Finset ℕ), lam e = _
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  have htot : lam 0 + lam 1 + lam 2 + lam 3 = 1 := by
    rw [← hsum4]; exact cert.total_one
  have hsum : ∑ v ∈ gapSystem.Blocks, gapSystem.cap lam v
      = gapSystem.cap lam 0 + gapSystem.cap lam 1 := by
    show ∑ v ∈ ({0, 1} : Finset ℕ), gapSystem.cap lam v = _
    exact Finset.sum_pair (by norm_num)
  have hslack := cert.slack_neg
  unfold PortSystem.slack at hslack
  rw [hsum] at hslack
  linarith

/-- The `50/50` mixture of admissible local states on the left block. -/
def gapLeftMix (B : Finset ℕ) : ℚ := if B = {0, 1} then 1 / 2 else if B = {2, 3} then 1 / 2 else 0

/-- The `50/50` mixture of admissible local states on the right block. -/
def gapRightMix (B : Finset ℕ) : ℚ := if B = {0, 2} then 1 / 2 else if B = {1, 3} then 1 / 2 else 0

/-- The expected coverage of a contact edge by the two `50/50` mixtures. -/
def gapCoverage (e : ℕ) : ℚ :=
  (∑ B ∈ gapSystem.L 0, gapLeftMix B * (if e ∈ B then 1 else 0)) +
    (∑ B ∈ gapSystem.L 1, gapRightMix B * (if e ∈ B then 1 else 0))

/-- **`gap_fractional_mixture`.**  The `50/50` mixture on each side satisfies every contact
edge in expectation. -/
theorem gap_fractional_mixture : ∀ e ∈ gapSystem.Edges, gapCoverage e = 1 := by
  intro e he
  have hL0 : gapSystem.L 0 = ({{0, 1}, {2, 3}} : Finset (Finset ℕ)) := rfl
  have hL1 : gapSystem.L 1 = ({{0, 2}, {1, 3}} : Finset (Finset ℕ)) := rfl
  have hne0 : ({0, 1} : Finset ℕ) ≠ ({2, 3} : Finset ℕ) := by decide
  have hne1 : ({0, 2} : Finset ℕ) ≠ ({1, 3} : Finset ℕ) := by decide
  have hmem : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by
    simpa [gapSystem, Finset.mem_insert, Finset.mem_singleton] using he
  unfold gapCoverage
  rw [hL0, hL1, Finset.sum_pair hne0, Finset.sum_pair hne1]
  rcases hmem with rfl | rfl | rfl | rfl <;>
    norm_num [gapLeftMix, gapRightMix]

/-- **`capacity_incompleteness`.**  `KERNEL-PROVED` once its two inputs are: integral
infeasibility does not imply a negative Level-1 capacity certificate. -/
theorem capacity_incompleteness :
    ¬ gapSystem.Feasible ∧ (NegativeCapacityCertificate gapSystem → False) :=
  ⟨gap_not_feasible, gap_no_negativeCapacityCertificate⟩

end AnchoredV2
end Erdos287
