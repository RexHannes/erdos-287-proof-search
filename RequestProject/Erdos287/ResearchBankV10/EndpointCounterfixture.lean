import RequestProject.Erdos287.ResearchBankV10.HBSupportCoverage

/-!
# Erdős #287 — Research Bank V10 §J: the old endpoint-only HB check — permanent counterfixture

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The old coverage argument checked the Type-II margins only at the endpoint corners of the Case II
rectangle `θ ∈ [0, θ₀]`, `ν ∈ [1/8, 1/4]`.  The support of the well-factorable HB boxes is larger.

`endpointCornerChecks_do_not_cover_support` (permanent regression firewall) proves, for every
admissible parameter set `P`, at the internal support point

  `θ = 0`, `ν = 1/13`, `s = ν − ζ = 1/13 − ζ`, `r = λ − ν + ζ = λ − 1/13 + ζ`:

1. the point lies inside the original well-factorable support bounds
   (`0 ≤ r`, `0 ≤ s`, `r + s ≤ λ`, `θ ∈ [0, θ₀]`);
2. `r + s = λ > 1/2`, so ordinary small-modulus BV does not apply (the point is outside `InBV`);
3. it lies outside the checked Case II rectangle (`ν = 1/13 < 1/8`), and an affine margin that is
   non-negative at **all four** endpoint corners is strictly **negative** there (explicit
   functional `12ν − 1`, value `−1/13`).

**Caveat (not reconstructed).**  The literal "old second Type-II margin" formula of the audit was
not available in the project sources; item 3 is therefore proved for an explicit affine margin
consistent with every endpoint check, which is exactly what refutes the endpoint-only *argument*.
It is not claimed to be the historical formula.
-/

namespace Erdos287
namespace ResearchBankV10
namespace EndpointCounterfixture

open HBSupportCoverage

/-- The original well-factorable support bounds. -/
def InWFSupport (P : CoverageParams) (θ r s : ℚ) : Prop :=
  0 ≤ θ ∧ θ ≤ P.θ₀ ∧ 0 ≤ r ∧ 0 ≤ s ∧ r + s ≤ P.lam

/-- The internal support point `(θ, r, s) = (0, λ − 1/13 + ζ, 1/13 − ζ)`. -/
def cornerPoint (P : CoverageParams) : ℚ × ℚ × ℚ :=
  (0, P.lam - 1 / 13 + P.ζ, 1 / 13 - P.ζ)

/-- The explicit affine margin `12ν − 1`. -/
def oldMarginWitness : AffineGap := ⟨-1, 0, 12⟩

/-- **Permanent regression firewall: endpoint corner checks do not cover the support.** -/
theorem endpointCornerChecks_do_not_cover_support (P : CoverageParams) :
    InWFSupport P (cornerPoint P).1 (cornerPoint P).2.1 (cornerPoint P).2.2 ∧
    1 / 2 < (cornerPoint P).2.1 + (cornerPoint P).2.2 ∧
    1 / 2 - 10 * P.ζ < (cornerPoint P).1 + (cornerPoint P).2.1 + (cornerPoint P).2.2 ∧
    (1 : ℚ) / 13 < 1 / 8 ∧
    oldMarginWitness.VertexOK (caseIIRect P) 0 ∧ oldMarginWitness.eval 0 (1 / 13) < 0 := by
  have hζ := P.ζ_pos
  have hζ' := P.ζ_le
  have hl := P.lam_bounds
  refine ⟨⟨le_rfl, P.θ₀_nonneg, ?_, ?_, ?_⟩, ?_, ?_, by norm_num, ?_, ?_⟩
  · simp only [cornerPoint]; linarith
  · simp only [cornerPoint]; linarith
  · simp only [cornerPoint]; linarith
  · simp only [cornerPoint]; linarith
  · simp only [cornerPoint]; linarith
  · simp only [AffineGap.VertexOK, oldMarginWitness, caseIIRect, AffineGap.eval]; norm_num
  · simp only [oldMarginWitness, AffineGap.eval]; norm_num

/-- The support point is not in the small-total-modulus (BV) region, for any box sitting there. -/
theorem cornerPoint_not_BV (P : CoverageParams) (b : SupportBox) (hθ : b.θ = 0)
    (hr : b.r = (cornerPoint P).2.1) (hs : b.s = (cornerPoint P).2.2) : ¬ InBV P b := by
  unfold InBV
  rw [hθ, hr, hs]
  have := (endpointCornerChecks_do_not_cover_support P).2.2.1
  simp only [cornerPoint] at this ⊢
  linarith

end EndpointCounterfixture
end ResearchBankV10
end Erdos287
