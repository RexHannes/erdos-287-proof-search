import RequestProject.Erdos287.ResearchBankV10.HBSelection

/-!
# Erdős #287 — Research Bank V10 §L: adaptive HB support coverage (exact rationals)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Parameters (`CoverageParams`): `0 ≤ θ₀ ≤ 1/1000`, `0 < ε₀ ≤ 1/1000`, `ζ = ε₀/100`,
`λ = 7/13 − 3θ₀ − ε₀`.

* **Small total modulus** (`InBV`): `θ + r + s ≤ 1/2 − 10ζ` — routed to ordinary BV.
* **Case II** (`caseII_params`): `s* = ν − ζ`, `r* = λ − ν + ζ`; for `ν ∈ [1/8, 1/4]` and
  `θ ≥ 0`, exact facts `r* + s* = λ`, `s* ∈ [1/8 − ζ, 1/4 − ζ]`, `r* ∈ [λ − 1/4 + ζ, λ − 1/8 + ζ]`,
  all strictly positive, and `θ + r* + s* > 1/2 − 10ζ` (Case II really lies outside the BV region).
* **Vertex argument** (`affine_ge_of_vertices`, `GapSystem.covers_rectangle`): an affine functional
  of `(θ, ν)` that is `≥ m` at the four vertices of `[θ_lo, θ_hi] × [ν_lo, ν_hi]` is `≥ m` on the
  **whole** rectangle.  A `GapSystem` is an explicit finite list of affine Type-II gap functionals
  with recorded margins; `covers_rectangle` turns a (finite, decidable) vertex certificate into a
  whole-rectangle lower bound.
* **Case III** (`dStar`, `caseIII_overlap`, `caseIII_routed`): `d* = min(λ, (1 + 2μ − λ − 7θ)/2 − 10ζ)`;
  Type I takes `r + s ≤ d* + ζ`, Type II takes `r + s ≥ d* − ζ`; the overlap has length `2ζ > 0`.
* **Routing** (`every_box_routed`): every actual HB support box is routed to at least one of
  ordinary BV, frozen Type I, restored Type II (possibly with overlap).  The proof uses the
  **proved** selection trichotomy `HBSelection.hb_selection`.

**What is not reconstructed.**  The explicit repaired Type-II gap functionals (with recorded
margins `1/208`, `9/208 − θ₀`, `7/208`, the `g1` bound, `G5 ≥ 19ζ`) and the exact Type-I domain
condition of the frozen Type-I theorem were not available in the project sources.  They enter only
through the generic `GapSystem` interface and the provider domains; no specific formula is
invented here.  The routing theorem is purely combinatorial and implies nothing analytic.
-/

namespace Erdos287
namespace ResearchBankV10
namespace HBSupportCoverage

open HBSelection

/-- Coverage parameters. -/
structure CoverageParams where
  θ₀ : ℚ
  ε₀ : ℚ
  θ₀_nonneg : 0 ≤ θ₀
  θ₀_le : θ₀ ≤ 1 / 1000
  ε₀_pos : 0 < ε₀
  ε₀_le : ε₀ ≤ 1 / 1000

namespace CoverageParams

variable (P : CoverageParams)

/-- `ζ = ε₀ / 100`. -/
def ζ : ℚ := P.ε₀ / 100

/-- `λ = 7/13 − 3θ₀ − ε₀`. -/
def lam : ℚ := 7 / 13 - 3 * P.θ₀ - P.ε₀

theorem ζ_pos : 0 < P.ζ := by unfold ζ; linarith [P.ε₀_pos]

theorem ζ_le : P.ζ ≤ 1 / 100000 := by unfold ζ; linarith [P.ε₀_le]

theorem lam_bounds : 7 / 13 - 1 / 250 ≤ P.lam ∧ P.lam < 7 / 13 := by
  unfold lam; constructor <;> linarith [P.θ₀_nonneg, P.θ₀_le, P.ε₀_pos, P.ε₀_le]

end CoverageParams

/-- An HB support box: the modulus shift `θ`, the HB factor data, and the two modulus exponents
`(r, s)`. -/
structure SupportBox where
  θ : ℚ
  data : HBData
  r : ℚ
  s : ℚ

/-- Small-total-modulus region (ordinary BV). -/
def InBV (P : CoverageParams) (b : SupportBox) : Prop := b.θ + b.r + b.s ≤ 1 / 2 - 10 * P.ζ

/-- `d* = min(λ, (1 + 2μ − λ − 7θ)/2 − 10ζ)`. -/
def dStar (P : CoverageParams) (b : SupportBox) : ℚ :=
  min P.lam ((1 + 2 * maxSmooth b.data.factors - P.lam - 7 * b.θ) / 2 - 10 * P.ζ)

/-- Frozen Type-I region. -/
def InTypeI (P : CoverageParams) (b : SupportBox) : Prop :=
  CaseI b.data.factors ∨ (CaseIII b.data.factors ∧ b.r + b.s ≤ dStar P b + P.ζ)

/-- Restored Type-II region. -/
def InTypeII (P : CoverageParams) (b : SupportBox) : Prop :=
  CaseII b.data.factors ∨ (CaseIII b.data.factors ∧ dStar P b - P.ζ ≤ b.r + b.s)

/-- **Case III overlap**: the Type-I and Type-II windows overlap in `[d* − ζ, d* + ζ]`, of length
`2ζ > 0`, and every value of `r + s` is covered. -/
theorem caseIII_overlap (P : CoverageParams) (b : SupportBox) :
    (dStar P b + P.ζ) - (dStar P b - P.ζ) = 2 * P.ζ ∧ 0 < 2 * P.ζ ∧
      ∀ t : ℚ, t ≤ dStar P b + P.ζ ∨ dStar P b - P.ζ ≤ t := by
  refine ⟨by ring, by linarith [P.ζ_pos], fun t => ?_⟩
  by_cases h : t ≤ dStar P b + P.ζ
  · exact Or.inl h
  · right; push_neg at h; linarith [P.ζ_pos]

/-- Case III boxes are routed (to Type I or Type II). -/
theorem caseIII_routed (P : CoverageParams) (b : SupportBox) (h : CaseIII b.data.factors) :
    InTypeI P b ∨ InTypeII P b := by
  rcases (caseIII_overlap P b).2.2 (b.r + b.s) with h1 | h1
  · exact Or.inl (Or.inr ⟨h, h1⟩)
  · exact Or.inr (Or.inr ⟨h, h1⟩)

/-- `d* ≤ λ`. -/
theorem dStar_le_lam (P : CoverageParams) (b : SupportBox) : dStar P b ≤ P.lam := min_le_left _ _

/-- **Routing theorem**: every actual HB support box is routed to ordinary BV, frozen Type I or
restored Type II (possibly with overlap).  Purely combinatorial. -/
theorem every_box_routed (P : CoverageParams) (b : SupportBox) :
    InBV P b ∨ InTypeI P b ∨ InTypeII P b := by
  rcases hb_selection b.data with h | h | h
  · exact Or.inr (Or.inl (Or.inl h))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (caseIII_routed P b h)

/-! ## Case II parameters -/

/-- `s* = ν − ζ`. -/
def sStar (P : CoverageParams) (ν : ℚ) : ℚ := ν - P.ζ

/-- `r* = λ − ν + ζ`. -/
def rStar (P : CoverageParams) (ν : ℚ) : ℚ := P.lam - ν + P.ζ

/-- **Exact Case II parameter facts** for all `θ ≥ 0` and `ν ∈ [1/8, 1/4]`. -/
theorem caseII_params (P : CoverageParams) {θ ν : ℚ} (hθ0 : 0 ≤ θ)
    (hν1 : 1 / 8 ≤ ν) (hν2 : ν ≤ 1 / 4) :
    rStar P ν + sStar P ν = P.lam ∧
    1 / 8 - P.ζ ≤ sStar P ν ∧ sStar P ν ≤ 1 / 4 - P.ζ ∧
    P.lam - 1 / 4 + P.ζ ≤ rStar P ν ∧ rStar P ν ≤ P.lam - 1 / 8 + P.ζ ∧
    0 < sStar P ν ∧ 0 < rStar P ν ∧
    1 / 2 - 10 * P.ζ < θ + rStar P ν + sStar P ν := by
  have hζ := P.ζ_pos
  have hζ' := P.ζ_le
  have hl := P.lam_bounds
  unfold rStar sStar
  refine ⟨by ring, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith⟩

/-! ## The vertex / affine-monotonicity argument -/

/-- 1-D: an affine function on `[t₀, t₁]` is bounded below by the smaller endpoint value. -/
theorem affine_ge_min_1d {a b t₀ t₁ t : ℚ} (h0 : t₀ ≤ t) (h1 : t ≤ t₁) :
    min (a + b * t₀) (a + b * t₁) ≤ a + b * t := by
  rcases le_total 0 b with hb | hb
  · exact (min_le_left _ _).trans (by nlinarith)
  · exact (min_le_right _ _).trans (by nlinarith)

/-- An affine functional `g(θ, ν) = a + b θ + c ν`. -/
structure AffineGap where
  a : ℚ
  b : ℚ
  c : ℚ
  deriving DecidableEq, Repr

/-- Evaluation. -/
def AffineGap.eval (g : AffineGap) (θ ν : ℚ) : ℚ := g.a + g.b * θ + g.c * ν

/-- A rectangle `[θ_lo, θ_hi] × [ν_lo, ν_hi]`. -/
structure Rect where
  θlo : ℚ
  θhi : ℚ
  νlo : ℚ
  νhi : ℚ
  deriving DecidableEq, Repr

/-- The four vertex values are all `≥ m`. -/
def AffineGap.VertexOK (g : AffineGap) (R : Rect) (m : ℚ) : Prop :=
  m ≤ g.eval R.θlo R.νlo ∧ m ≤ g.eval R.θlo R.νhi ∧ m ≤ g.eval R.θhi R.νlo ∧
    m ≤ g.eval R.θhi R.νhi

instance (g : AffineGap) (R : Rect) (m : ℚ) : Decidable (g.VertexOK R m) := by
  unfold AffineGap.VertexOK; infer_instance

/-- **Vertex argument**: vertex values `≥ m` ⟹ `≥ m` on the whole rectangle. -/
theorem affine_ge_of_vertices {g : AffineGap} {R : Rect} {m : ℚ} (h : g.VertexOK R m)
    {θ ν : ℚ} (hθ0 : R.θlo ≤ θ) (hθ1 : θ ≤ R.θhi) (hν0 : R.νlo ≤ ν) (hν1 : ν ≤ R.νhi) :
    m ≤ g.eval θ ν := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold AffineGap.eval at *
  -- first in ν at the two θ-endpoints, then in θ
  have hlo : m ≤ g.a + g.b * R.θlo + g.c * ν := by
    have := affine_ge_min_1d (a := g.a + g.b * R.θlo) (b := g.c) hν0 hν1
    exact le_trans (le_min h1 h2) this
  have hhi : m ≤ g.a + g.b * R.θhi + g.c * ν := by
    have := affine_ge_min_1d (a := g.a + g.b * R.θhi) (b := g.c) hν0 hν1
    exact le_trans (le_min h3 h4) this
  have := affine_ge_min_1d (a := g.a + g.c * ν) (b := g.b) hθ0 hθ1
  have e1 : g.a + g.c * ν + g.b * R.θlo = g.a + g.b * R.θlo + g.c * ν := by ring
  have e2 : g.a + g.c * ν + g.b * R.θhi = g.a + g.b * R.θhi + g.c * ν := by ring
  have e3 : g.a + g.c * ν + g.b * θ = g.a + g.b * θ + g.c * ν := by ring
  rw [e1, e2, e3] at this
  exact le_trans (le_min hlo hhi) this

/-- A Type-II gap system: explicit affine gap functionals with recorded margins. -/
structure GapSystem where
  gaps : List (AffineGap × ℚ)

/-- The finite vertex certificate. -/
def GapSystem.VertexCertificate (G : GapSystem) (R : Rect) : Prop :=
  ∀ gm ∈ G.gaps, gm.1.VertexOK R gm.2

instance (G : GapSystem) (R : Rect) : Decidable (G.VertexCertificate R) := by
  unfold GapSystem.VertexCertificate; infer_instance

/-- **Whole-rectangle coverage from the vertex certificate.** -/
theorem GapSystem.covers_rectangle {G : GapSystem} {R : Rect} (h : G.VertexCertificate R)
    {θ ν : ℚ} (hθ0 : R.θlo ≤ θ) (hθ1 : θ ≤ R.θhi) (hν0 : R.νlo ≤ ν) (hν1 : ν ≤ R.νhi) :
    ∀ gm ∈ G.gaps, gm.2 ≤ gm.1.eval θ ν :=
  fun gm hgm => affine_ge_of_vertices (h gm hgm) hθ0 hθ1 hν0 hν1

/-- The Case II rectangle `[0, θ₀] × [1/8, 1/4]`. -/
def caseIIRect (P : CoverageParams) : Rect := ⟨0, P.θ₀, 1 / 8, 1 / 4⟩

/-- **Firewall: corner checks on a rectangle do not certify points outside it.**  An affine gap
that is positive at the four corners of the Case II rectangle can be negative at a support point
with `ν = 1/13 < 1/8` (explicit functional `g = 13ν − 1`, margin `0`). -/
theorem corners_do_not_certify_outside :
    ∃ g : AffineGap, g.VertexOK ⟨0, 1 / 1000, 1 / 8, 1 / 4⟩ 0 ∧ g.eval 0 (1 / 13 - 1 / 1000) < 0 := by
  refine ⟨⟨-1, 0, 13⟩, ?_, ?_⟩ <;> norm_num [AffineGap.VertexOK, AffineGap.eval]

end HBSupportCoverage
end ResearchBankV10
end Erdos287
