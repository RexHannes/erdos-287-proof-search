import RequestProject.Erdos287.ResearchBankV12.ConcreteParameters

/-!
# Erdős #287 — Research Bank V12 §4: the permanent endpoint-only HB counterfixture (concrete)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The concrete internal support point that refuted the old endpoint-only argument:

  `θ = 0`, `ν = 1/13`, `r = 14995777969/32500000000`, `s = 1/20`.

Kernel-checked (exact rationals):

* (a) the point lies in the old well-factorable support rectangle: `θ ∈ [0, θ₀]`, `r, s ≥ 0`,
  `r + s ≤ λ`, and even `r ≤ r*(ν) = λ − ν + ζ`, `s ≤ s*(ν) = ν − ζ`;
* (b) `r + s = 16620777969/32500000000 > 1/2`, and `θ + r + s > 1/2 − 10ζ`, so the point is **not**
  in the small-total-modulus BV branch;
* (c) the old second Type-II margin
  `1/3 − (2/3) r + (2/3) s − ν − ε₀/2000 = −1161037617/65000000000 < 0`;
* (d) at the *top corner* `(r*(ν), s*(ν))` of the same rectangle the old margin is **positive**.

Hence (`endpointOnlyHBArgument_false`): checking the top corners does **not** cover the whole
well-factorable support.  This is a permanent regression firewall.
-/

namespace Erdos287
namespace ResearchBankV12
namespace EndpointCounterfixture

open ConcreteParameters

/-- The old second Type-II margin `1/3 − (2/3) r + (2/3) s − ν − ε₀/2000`. -/
def oldMargin2 (r s ν : ℚ) : ℚ := 1 / 3 - (2 / 3) * r + (2 / 3) * s - ν - epsilon0 / 2000

/-- The old well-factorable support rectangle. -/
def InOldWFSupport (θ r s : ℚ) : Prop :=
  0 ≤ θ ∧ θ ≤ theta0 ∧ 0 ≤ r ∧ 0 ≤ s ∧ r + s ≤ lam

/-- The internal point. -/
def θc : ℚ := 0
def νc : ℚ := 1 / 13
def rc : ℚ := 14995777969 / 32500000000
def sc : ℚ := 1 / 20

/-- (a) The point lies inside the old well-factorable support rectangle (and inside the
`ν = 1/13` box `[0, r*] × [0, s*]`). -/
theorem point_in_support :
    InOldWFSupport θc rc sc ∧ rc ≤ rStar νc ∧ sc ≤ sStar νc := by
  refine ⟨⟨le_rfl, theta0_pos.le, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    norm_num [θc, rc, sc, νc, rStar, sStar, lam, theta0, epsilon0, zeta]

/-- (b) `r + s = 16620777969/32500000000 > 1/2`, and the point is outside `smallBV`. -/
theorem point_not_smallBV :
    rc + sc = 16620777969 / 32500000000 ∧ (1 : ℚ) / 2 < 16620777969 / 32500000000 ∧
      ¬ smallBV θc rc sc := by
  refine ⟨by norm_num [rc, sc], by norm_num, ?_⟩
  unfold smallBV; norm_num [θc, rc, sc, zeta, epsilon0]

/-- (c) The old second Type-II margin at the point is `−1161037617/65000000000 < 0`. -/
theorem point_margin_negative :
    oldMargin2 rc sc νc = -1161037617 / 65000000000 ∧ (-1161037617 / 65000000000 : ℚ) < 0 := by
  constructor
  · norm_num [oldMargin2, rc, sc, νc, epsilon0]
  · norm_num

/-- (d) At the top corner `(r*(1/13), s*(1/13))` the old margin is strictly positive. -/
theorem top_corner_margin_positive : 0 < oldMargin2 (rStar νc) (sStar νc) νc := by
  norm_num [oldMargin2, rStar, sStar, νc, lam, theta0, epsilon0, zeta]

/-- **Permanent regression firewall: the endpoint-only HB argument is false.**  There is a point
of the old well-factorable support, outside the small-modulus BV branch, where the old second
Type-II margin is negative although it is positive at the top corner of the same box. -/
theorem endpointOnlyHBArgument_false :
    ∃ θ r s ν : ℚ, InOldWFSupport θ r s ∧ r ≤ rStar ν ∧ s ≤ sStar ν ∧ ¬ smallBV θ r s ∧
      1 / 2 < r + s ∧ oldMargin2 r s ν < 0 ∧ 0 < oldMargin2 (rStar ν) (sStar ν) ν :=
  ⟨θc, rc, sc, νc, point_in_support.1, point_in_support.2.1, point_in_support.2.2,
    point_not_smallBV.2.2, by rw [point_not_smallBV.1]; norm_num,
    by rw [point_margin_negative.1]; norm_num, top_corner_margin_positive⟩

/-- **Corollary (no ledger may claim it):** "the old margin is nonnegative at the top corner of
every support box ⟹ it is nonnegative on the whole support" is false. -/
theorem topCorner_check_does_not_cover :
    ¬ ∀ θ r s ν : ℚ, InOldWFSupport θ r s → r ≤ rStar ν → s ≤ sStar ν →
      0 ≤ oldMargin2 (rStar ν) (sStar ν) ν → 0 ≤ oldMargin2 r s ν := by
  intro h
  obtain ⟨θ, r, s, ν, h1, h2, h3, -, -, h6, h7⟩ := endpointOnlyHBArgument_false
  exact absurd (h θ r s ν h1 h2 h3 h7.le) (not_le.2 h6)

end EndpointCounterfixture
end ResearchBankV12
end Erdos287
