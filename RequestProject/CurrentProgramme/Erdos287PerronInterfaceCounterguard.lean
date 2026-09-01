import RequestProject.CurrentProgramme.Erdos287PerronSingleContour

/-!
# Erdős #287 — counterguard: a per-contour bound is not a total bound

The current Perron interface supplies a bound **per contour**.  This module records, as a
kernel-proved finite countermodel, that such an interface is *insufficient* for any fixed
global total unless the number of contours is itself controlled.

* `perContour_bound_does_not_imply_total_without_cardinality` — for every proposed global
  budget `B` there is a finite family of contours, each of mass exactly `1` (so the
  per-contour bound `1` holds), whose total mass exceeds `B`;
* `total_bound_of_perContour_and_cardinality` — the positive companion: with an explicit
  cardinality bound the aggregation *is* valid.

Consequently the status `PERRON-CURRENT-INTERFACE-SUFFICIENCY45` is recorded as **FAIL**:
the interface as currently stated does not yield the total mass bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace PerronCounterguard

/-- The countermodel family: `n` contours, each of mass exactly `1`. -/
def contourMass : ℕ → ℝ := fun _ => 1

/-- Every contour of the countermodel family satisfies the per-contour bound `B = 1`. -/
theorem contourMass_le_one (i : ℕ) : |contourMass i| ≤ 1 := by
  simp [contourMass]

/-- The total mass of `n` countermodel contours is exactly `n`. -/
theorem total_contourMass (n : ℕ) : ∑ i ∈ Finset.range n, contourMass i = (n : ℝ) := by
  simp [contourMass]

/-- **`perContour_bound_does_not_imply_total_without_cardinality`.**  `LEAN_PROVED`.
For every proposed global budget `B` there is a finite contour family satisfying the
per-contour bound `1` whose total mass exceeds `B`.  Hence a per-contour bound never
implies a fixed global total bound when the contour cardinality is uncontrolled. -/
theorem perContour_bound_does_not_imply_total_without_cardinality (B : ℝ) :
    ∃ (n : ℕ) (mass : ℕ → ℝ),
      (∀ i ∈ Finset.range n, |mass i| ≤ 1) ∧ B < ∑ i ∈ Finset.range n, mass i := by
  obtain ⟨n, hn⟩ := exists_nat_gt B
  refine ⟨n, contourMass, fun i _ => contourMass_le_one i, ?_⟩
  rw [total_contourMass]
  exact hn

/-- Sharpened form: the *same* per-contour datum (`mass ≡ 1`, bound `1`) is compatible with
arbitrarily large totals, so no function of the per-contour bound alone can be a global
bound. -/
theorem perContour_datum_compatible_with_unbounded_total (B : ℝ) :
    ∃ n : ℕ, (∀ i ∈ Finset.range n, |contourMass i| ≤ 1) ∧
      B < ∑ i ∈ Finset.range n, contourMass i := by
  obtain ⟨n, hn⟩ := exists_nat_gt B
  exact ⟨n, fun i _ => contourMass_le_one i, by rw [total_contourMass]; exact hn⟩

/-- **Positive companion.**  With an explicit cardinality bound the per-contour bound does
aggregate: `total ≤ N · B`. -/
theorem total_bound_of_perContour_and_cardinality {ι : Type*} (F : Finset ι) (mass : ι → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (N : ℕ) (hcard : F.card ≤ N) (hmass : ∀ i ∈ F, mass i ≤ B) :
    ∑ i ∈ F, mass i ≤ (N : ℝ) * B := by
  calc ∑ i ∈ F, mass i ≤ ∑ _i ∈ F, B := Finset.sum_le_sum hmass
    _ = (F.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) * B := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB

/-- **Interface-sufficiency verdict, in the kernel.**  There is no real number `G` that
bounds the total mass of every finite family satisfying the per-contour bound `1`. -/
theorem no_global_total_from_perContour_bound :
    ¬ ∃ G : ℝ, ∀ (n : ℕ) (mass : ℕ → ℝ),
        (∀ i ∈ Finset.range n, |mass i| ≤ 1) → ∑ i ∈ Finset.range n, mass i ≤ G := by
  rintro ⟨G, hG⟩
  obtain ⟨n, mass, hper, hlt⟩ := perContour_bound_does_not_imply_total_without_cardinality G
  exact absurd (hG n mass hper) (not_le.2 hlt)

end PerronCounterguard
end Erdos287
