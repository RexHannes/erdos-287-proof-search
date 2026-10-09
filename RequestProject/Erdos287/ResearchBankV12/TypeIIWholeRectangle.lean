import RequestProject.Erdos287.ResearchBankV12.ConcreteParameters

/-!
# Erdős #287 — Research Bank V12 §10: Case II — the concrete Type-II gaps on the WHOLE rectangle

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

For Case II (`ν` a partial-product exponent) put `s* = ν − ζ`, `r* = λ − ν + ζ`.  An actual box
satisfies `0 ≤ θ ≤ θ₀`, `0 ≤ r ≤ r*`, `0 ≤ s ≤ s*`, and lies outside `smallBV`
(`θ + r + s > 1/2 − 10ζ`).  The three restored Type-II gaps are

* `g1 = 1/2 + s/2 − 3θ − r − ν`,
* `g2 = 1/2 − (5/2)θ − r/2 − (5/4)ν`,
* `g3 = 1/2 − (17/8)θ − (3/4)r − ν`.

**Every point** of the clipped region (not only its corners) satisfies

* `g1 ≥ ν/2 − 3/52 + θ₀ + (287/2)ζ`,
* `g2 ≥ 3/13 − 3ν/4 − θ₀ + (99/2)ζ`,
* `g3 ≥ 5/52 − ν/4 + θ₀/8 + (297/4)ζ`,

and, for `1/8 ≤ ν ≤ 1/4`, the fixed worst-case margins `g1 ≥ 1/208`, `g2 ≥ 9/208 − θ₀`,
`g3 ≥ 7/208`; moreover `ν − s ≥ ζ`, `s − 2θ > 0` and `1 − 4θ − 2r − ν > 0`.

The proofs are direct linear arithmetic over the whole region (each bound is a nonnegative linear
combination of the region's defining inequalities), so no vertex enumeration is involved.  The
V10 vertex lemma is not needed; for completeness `g1_is_affine` records that the gaps are affine.
-/

namespace Erdos287
namespace ResearchBankV12
namespace TypeIIWholeRectangle

open ConcreteParameters

/-- `g1 = 1/2 + s/2 − 3θ − r − ν`. -/
def g1 (θ r s ν : ℚ) : ℚ := 1 / 2 + s / 2 - 3 * θ - r - ν

/-- `g2 = 1/2 − (5/2)θ − r/2 − (5/4)ν`. -/
def g2 (θ r ν : ℚ) : ℚ := 1 / 2 - (5 / 2) * θ - r / 2 - (5 / 4) * ν

/-- `g3 = 1/2 − (17/8)θ − (3/4)r − ν`. -/
def g3 (θ r ν : ℚ) : ℚ := 1 / 2 - (17 / 8) * θ - (3 / 4) * r - ν

/-- An actual Case-II box: `0 ≤ θ ≤ θ₀`, `0 ≤ r ≤ r*`, `0 ≤ s ≤ s*`, outside `smallBV`. -/
structure CaseIIBox (ν θ r s : ℚ) : Prop where
  θ_nonneg : 0 ≤ θ
  θ_le : θ ≤ theta0
  r_nonneg : 0 ≤ r
  r_le : r ≤ rStar ν
  s_nonneg : 0 ≤ s
  s_le : s ≤ sStar ν
  not_bv : ¬ smallBV θ r s

section
variable {ν θ r s : ℚ} (h : CaseIIBox ν θ r s)
include h

private theorem facts :
    0 ≤ θ ∧ θ ≤ theta0 ∧ r ≤ lam - ν + zeta ∧ s ≤ ν - zeta ∧ 1 / 2 - 10 * zeta < θ + r + s ∧
      lam = 7 / 13 - 3 * theta0 - 100 * zeta ∧ 0 < zeta ∧ 0 < theta0 := by
  refine ⟨h.θ_nonneg, h.θ_le, h.r_le, h.s_le, ?_, lam_zeta, zeta_pos, theta0_pos⟩
  have := h.not_bv; unfold smallBV at this; linarith

/-- **`g1 ≥ ν/2 − 3/52 + θ₀ + (287/2)ζ` on the whole clipped rectangle.** -/
theorem g1_lower : ν / 2 - 3 / 52 + theta0 + (287 / 2) * zeta ≤ g1 θ r s ν := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := facts h
  unfold g1; linarith

/-- **`g2 ≥ 3/13 − 3ν/4 − θ₀ + (99/2)ζ` on the whole clipped rectangle.** -/
theorem g2_lower : 3 / 13 - 3 * ν / 4 - theta0 + (99 / 2) * zeta ≤ g2 θ r ν := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := facts h
  unfold g2; linarith

/-- **`g3 ≥ 5/52 − ν/4 + θ₀/8 + (297/4)ζ` on the whole clipped rectangle.** -/
theorem g3_lower : 5 / 52 - ν / 4 + theta0 / 8 + (297 / 4) * zeta ≤ g3 θ r ν := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := facts h
  unfold g3; linarith

/-- `ν − s ≥ ζ`. -/
theorem nu_sub_s : zeta ≤ ν - s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := facts h
  linarith

/-- The region is nonempty only when `ν ≥ 1/26 − …`; in particular for `ν ≥ 1/8`,
`s − 2θ > 0`. -/
theorem s_sub_two_theta (hν : 1 / 8 ≤ ν) : 0 < s - 2 * θ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := facts h
  have : theta0 < 1 / 1000 := theta0_lt
  have : zeta = 1 / 10000000 := zeta_eq
  linarith

/-- `1 − 4θ − 2r − ν > 0` (for `ν ≥ 1/8`). -/
theorem one_sub_pos (hν : 1 / 8 ≤ ν) : 0 < 1 - 4 * θ - 2 * r - ν := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := facts h
  have : theta0 < 1 / 1000 := theta0_lt
  linarith

/-- **Fixed worst-case margins** for `1/8 ≤ ν ≤ 1/4`. -/
theorem worst_case_margins (hν1 : 1 / 8 ≤ ν) (hν2 : ν ≤ 1 / 4) :
    1 / 208 ≤ g1 θ r s ν ∧ 9 / 208 - theta0 ≤ g2 θ r ν ∧ 7 / 208 ≤ g3 θ r ν := by
  have a := g1_lower h
  have b := g2_lower h
  have c := g3_lower h
  have := zeta_pos
  have := theta0_pos
  refine ⟨by linarith, by linarith, by linarith⟩

/-- All three gaps are at least `1/208` (as `9/208 − θ₀ ≥ 1/208`). -/
theorem all_gaps_ge (hν1 : 1 / 8 ≤ ν) (hν2 : ν ≤ 1 / 4) :
    1 / 208 ≤ g1 θ r s ν ∧ 1 / 208 ≤ g2 θ r ν ∧ 1 / 208 ≤ g3 θ r ν := by
  obtain ⟨a, b, c⟩ := worst_case_margins h hν1 hν2
  have := theta0_lt
  exact ⟨a, by linarith, by linarith⟩

end

/-- The gaps are affine in `(θ, r, s, ν)` (so the whole-rectangle bounds above are the sharp
statements; no hidden non-linearity). -/
theorem g1_is_affine (θ r s ν : ℚ) :
    g1 θ r s ν = 1 / 2 + (1 / 2) * s + (-3) * θ + (-1) * r + (-1) * ν := by
  unfold g1; ring

/-- **Sharpness of the `g1` whole-rectangle bound**: it is attained at the extreme point
`θ = θ₀`, `r = r*`, `s = 1/2 − 10ζ − θ₀ − r*` (the closure of the non-BV constraint).  Hence the
constant `(287/2)ζ` cannot be improved using only these constraints. -/
theorem g1_bound_attained (ν : ℚ) :
    g1 theta0 (rStar ν) (1 / 2 - 10 * zeta - theta0 - rStar ν) ν =
      ν / 2 - 3 / 52 + theta0 + (287 / 2) * zeta := by
  unfold g1 rStar; rw [lam_zeta]; ring

end TypeIIWholeRectangle
end ResearchBankV12
end Erdos287
