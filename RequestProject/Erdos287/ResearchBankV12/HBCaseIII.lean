import RequestProject.Erdos287.ResearchBankV12.HBSelectionConcrete
import RequestProject.Erdos287.ResearchBankV12.TypeIIWholeRectangle

/-!
# Erdős #287 — Research Bank V12 §12: Case III — overlapping Type-I / Type-II routing

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Case III: `7/24 < μ < 4/13`, partial product `ν` with `1 − 3μ ≤ ν < 1/8`, `ν > 1/13`.  Boxes are
the legal factorization boxes `0 ≤ r ≤ r*(ν)`, `0 ≤ s ≤ s*(ν)`, `0 ≤ θ ≤ θ₀`.  Put

  `B(μ, θ) = (1 + 2μ − λ − 7θ)/2 − 10ζ`,   `d* = min(λ, B)`.

* **Overlap** (`overlap`): Type I is used for `r + s ≤ d* + ζ`, Type II for `r + s ≥ d* − ζ`;
  every value of `r + s` is covered and the overlap has length `2ζ > 0`.
* **Type-II `g1`** (`g1 = 1/2 + s/2 − 3θ − r − ν`):
  - `g1_ge_of_ge_B`: on `r + s ≥ B` (in particular on `r + s ≥ d*` when `d* = B`),
    `g1 ≥ 4/13 − μ + θ₀/2 + (337/2)ζ > 0`;
  - `g1_ge_window_B`: on the full window side `r + s ≥ B − ζ`, `g1 ≥ 4/13 − μ + θ₀/2 + 168ζ`;
  - `g1_ge_window_lam`: on `r + s ≥ λ − ζ`, `g1 ≥ 3(θ₀ − θ) + 98ζ`;
  - `g1_pos_on_typeII_window`: **`g1 > 0` on the whole Type-II window `r + s ≥ d* − ζ`.**
* **Audit finding** (`g1_337_fails_on_full_window`): the `(337/2)ζ` constant does **not** hold on
  the whole window `r + s ≥ d* − ζ`: at the explicit legal box `μ = 3/10`, `θ = θ₀`, `ν = 1/10`,
  `r = r*(ν)`, `s = B − ζ − r*(ν)` one has `d* = B`, `r + s = d* − ζ`, and
  `g1 = 4/13 − μ + θ₀/2 + 168ζ` exactly, which is `ζ/2` below the `(337/2)ζ` claim.  The
  `(337/2)ζ` form is the bound on `r + s ≥ d*`; on the overlap strip the sharp constant is `168ζ`.
  Positivity of `g1` (all that routing needs) holds throughout.
  `g1_337_fails_in_lam_branch`: in the branch `d* = λ` the `(337/2)ζ` bound fails even at
  `r + s = d*` (explicit point `μ = 4/13 − θ₀/2`, `θ = θ₀`, `ν = 1 − 3μ`, top corner); in that branch
  Type I already covers every legal box (`typeI_covers_all_in_lam_branch`).
* **Type-I side** (`typeI_level_reserve`): on `r + s ≤ d* + ζ`, `(1 + 2μ − λ − 7θ)/2 − (r+s) ≥ 9ζ`.
  **`G5 ≥ 19ζ` is NOT reconstructed**: the formula for the Type-I reserve `G5` was not supplied.
-/

namespace Erdos287
namespace ResearchBankV12
namespace HBCaseIII

open ConcreteParameters TypeIIWholeRectangle

/-- `B(μ, θ) = (1 + 2μ − λ − 7θ)/2 − 10ζ`. -/
def B (μ θ : ℚ) : ℚ := (1 + 2 * μ - lam - 7 * θ) / 2 - 10 * zeta

/-- `d* = min(λ, B)`. -/
def dStar (μ θ : ℚ) : ℚ := min lam (B μ θ)

/-- Agreement with the V10 `dStar` at the concrete parameters. -/
theorem dStar_eq_v10 (b : ResearchBankV10.HBSupportCoverage.SupportBox) :
    dStar (ResearchBankV10.HBSelection.maxSmooth b.data.factors) b.θ =
      ResearchBankV10.HBSupportCoverage.dStar concreteParams b := rfl

/-- **Overlap**: the two windows cover all `t` and overlap in a strip of length `2ζ`. -/
theorem overlap (μ θ : ℚ) :
    (dStar μ θ + zeta) - (dStar μ θ - zeta) = 2 * zeta ∧ 0 < 2 * zeta ∧
      ∀ t : ℚ, t ≤ dStar μ θ + zeta ∨ dStar μ θ - zeta ≤ t := by
  have hz := zeta_pos
  refine ⟨by ring, by linarith, fun t => ?_⟩
  rcases le_or_gt t (dStar μ θ + zeta) with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- A legal Case-III box (for the selected `ν`). -/
structure LegalBox (ν θ r s : ℚ) : Prop where
  θ_nonneg : 0 ≤ θ
  θ_le : θ ≤ theta0
  r_nonneg : 0 ≤ r
  r_le : r ≤ rStar ν
  s_nonneg : 0 ≤ s
  s_le : s ≤ sStar ν

section
variable {μ ν θ r s : ℚ} (hb : LegalBox ν θ r s)
include hb

/-- `g1 ≥ 4/13 − μ + θ₀/2 + (337/2)ζ` on `r + s ≥ B`. -/
theorem g1_ge_of_ge_B (hν : 1 - 3 * μ ≤ ν) (ht : B μ θ ≤ r + s) :
    4 / 13 - μ + theta0 / 2 + (337 / 2) * zeta ≤ g1 θ r s ν := by
  have h1 := hb.r_le; have h2 := hb.θ_le; have hl := lam_zeta
  unfold rStar at h1; unfold B at ht; unfold g1; linarith

/-- `g1 ≥ 4/13 − μ + θ₀/2 + 168ζ` on the window side `r + s ≥ B − ζ`. -/
theorem g1_ge_window_B (hν : 1 - 3 * μ ≤ ν) (ht : B μ θ - zeta ≤ r + s) :
    4 / 13 - μ + theta0 / 2 + 168 * zeta ≤ g1 θ r s ν := by
  have h1 := hb.r_le; have h2 := hb.θ_le; have hl := lam_zeta
  unfold rStar at h1; unfold B at ht; unfold g1; linarith

/-- `g1 ≥ 3(θ₀ − θ) + 98ζ` on `r + s ≥ λ − ζ` (using `ν ≥ 1/13`). -/
theorem g1_ge_window_lam (hν : 1 / 13 ≤ ν) (ht : lam - zeta ≤ r + s) :
    3 * (theta0 - θ) + 98 * zeta ≤ g1 θ r s ν := by
  have h1 := hb.r_le; have hl := lam_zeta
  unfold rStar at h1; unfold g1; linarith

/-- **`g1 > 0` on the whole Type-II window `r + s ≥ d* − ζ`** (Case-III hypotheses). -/
theorem g1_pos_on_typeII_window (hμ : μ < 4 / 13) (hν : 1 - 3 * μ ≤ ν) (hν' : 1 / 13 < ν)
    (ht : dStar μ θ - zeta ≤ r + s) : 0 < g1 θ r s ν := by
  have hz := zeta_pos; have h2 := hb.θ_le; have ht0 := theta0_pos
  unfold dStar at ht
  rcases le_total lam (B μ θ) with h | h
  · rw [min_eq_left h] at ht
    have := g1_ge_window_lam hb hν'.le ht; linarith
  · rw [min_eq_right h] at ht
    have := g1_ge_window_B hb hν ht; linarith

/-- The `(337/2)ζ` form holds on `r + s ≥ d*` whenever `d* = B`. -/
theorem g1_ge_of_ge_dStar (hν : 1 - 3 * μ ≤ ν) (hB : B μ θ ≤ lam) (ht : dStar μ θ ≤ r + s) :
    4 / 13 - μ + theta0 / 2 + (337 / 2) * zeta ≤ g1 θ r s ν := by
  unfold dStar at ht; rw [min_eq_right hB] at ht
  exact g1_ge_of_ge_B hb hν ht

omit hb in
/-- `g1 > 0` in the strong form: `4/13 − μ + θ₀/2 + (337/2)ζ > 0` for `μ < 4/13`. -/
theorem g1_337_pos (hμ : μ < 4 / 13) : 0 < 4 / 13 - μ + theta0 / 2 + (337 / 2) * zeta := by
  have := zeta_pos; have := theta0_pos; linarith

omit hb in
/-- **Type-I side**: on `r + s ≤ d* + ζ`, the level reserve `(1 + 2μ − λ − 7θ)/2 − (r+s) ≥ 9ζ`
and `r + s ≤ λ + ζ`. -/
theorem typeI_level_reserve (ht : r + s ≤ dStar μ θ + zeta) :
    9 * zeta ≤ (1 + 2 * μ - lam - 7 * θ) / 2 - (r + s) ∧ r + s ≤ lam + zeta := by
  have h1 : dStar μ θ ≤ B μ θ := min_le_right _ _
  have h2 : dStar μ θ ≤ lam := min_le_left _ _
  unfold B at h1
  constructor <;> linarith

end

/-! ## The audit counterfixture for the `(337/2)ζ` constant -/

def μx : ℚ := 3 / 10
def νx : ℚ := 1 / 10
def θx : ℚ := theta0
def rx : ℚ := rStar νx
def sx : ℚ := B μx θx - zeta - rStar νx

/-- **The `(337/2)ζ` claim fails on the full Type-II window `r + s ≥ d* − ζ`.**  The explicit
legal box above satisfies all Case-III hypotheses, lies on the window (`r + s = d* − ζ`,
`d* = B`), and has `g1 = 4/13 − μ + θ₀/2 + 168ζ < 4/13 − μ + θ₀/2 + (337/2)ζ`. -/
theorem g1_337_fails_on_full_window :
    LegalBox νx θx rx sx ∧ 7 / 24 < μx ∧ μx < 4 / 13 ∧ 1 - 3 * μx ≤ νx ∧ νx < 1 / 8 ∧
      1 / 13 < νx ∧ B μx θx ≤ lam ∧ rx + sx = dStar μx θx - zeta ∧
      g1 θx rx sx νx = 4 / 13 - μx + theta0 / 2 + 168 * zeta ∧
      g1 θx rx sx νx < 4 / 13 - μx + theta0 / 2 + (337 / 2) * zeta := by
  have hB : B μx θx ≤ lam := by
    unfold B μx θx; rw [lam_eq, zeta_eq, theta0_eq]; norm_num
  have hd : dStar μx θx = B μx θx := min_eq_right hB
  refine ⟨⟨theta0_pos.le, le_rfl, ?_, le_rfl, ?_, ?_⟩, by norm_num [μx], by norm_num [μx],
    by norm_num [μx, νx], by norm_num [νx], by norm_num [νx], hB, ?_, ?_, ?_⟩
  · unfold rx rStar νx; rw [lam_eq, zeta_eq]; norm_num
  · unfold sx B rStar μx θx νx; rw [lam_eq, zeta_eq, theta0_eq]; norm_num
  · unfold sx B rStar sStar μx θx νx; rw [lam_eq, zeta_eq, theta0_eq]; norm_num
  · rw [hd]; unfold rx sx; ring
  · unfold g1 sx rx B rStar μx θx νx; rw [lam_zeta]; ring
  · unfold g1 sx rx B rStar μx θx νx; rw [lam_zeta]; have := zeta_pos; linarith

/-- In the branch `d* = λ` (i.e. `λ ≤ B`) the Type-I window `r + s ≤ d* + ζ` already contains
every legal box (since `r + s ≤ r* + s* = λ`), so Type II is not needed there. -/
theorem typeI_covers_all_in_lam_branch {μ ν θ r s : ℚ} (hb : LegalBox ν θ r s)
    (hB : lam ≤ B μ θ) : r + s ≤ dStar μ θ + zeta := by
  have h1 := hb.r_le; have h2 := hb.s_le; have hz := zeta_pos
  unfold dStar; rw [min_eq_left hB]
  have := rStar_add_sStar ν; linarith

/-! ## Second audit counterfixture: the branch `d* = λ` -/

def μy : ℚ := 4 / 13 - theta0 / 2
def νy : ℚ := 1 - 3 * μy

/-- **The `(337/2)ζ` claim also fails at `r + s = d*` in the branch `d* = λ`**: take
`μ = 4/13 − θ₀/2`, `θ = θ₀`, `ν = 1 − 3μ`, `(r, s) = (r*(ν), s*(ν))`.  All Case-III hypotheses
hold, `d* = λ = r + s`, and `g1 = 3θ₀/4 + (197/2)ζ < θ₀ + (337/2)ζ = 4/13 − μ + θ₀/2 + (337/2)ζ`.
(In this branch Type I covers every legal box, `typeI_covers_all_in_lam_branch`, so routing is
unaffected; `g1 > 0` still holds.) -/
theorem g1_337_fails_in_lam_branch :
    LegalBox νy theta0 (rStar νy) (sStar νy) ∧ 7 / 24 < μy ∧ μy < 4 / 13 ∧ 1 - 3 * μy ≤ νy ∧
      νy < 1 / 8 ∧ 1 / 13 < νy ∧ lam ≤ B μy theta0 ∧ rStar νy + sStar νy = dStar μy theta0 ∧
      g1 theta0 (rStar νy) (sStar νy) νy = 3 * theta0 / 4 + (197 / 2) * zeta ∧
      g1 theta0 (rStar νy) (sStar νy) νy < 4 / 13 - μy + theta0 / 2 + (337 / 2) * zeta ∧
      0 < g1 theta0 (rStar νy) (sStar νy) νy := by
  have hB : lam ≤ B μy theta0 := by
    unfold B μy; rw [lam_eq, zeta_eq, theta0_eq]; norm_num
  have ht := theta0_eq; have hz := zeta_eq; have hl := lam_eq
  refine ⟨⟨theta0_pos.le, le_rfl, ?_, le_rfl, ?_, le_rfl⟩, ?_, ?_, le_rfl, ?_, ?_, hB, ?_, ?_, ?_,
    ?_⟩
  · unfold rStar νy μy; rw [hl, hz, ht]; norm_num
  · unfold sStar νy μy; rw [hz, ht]; norm_num
  · unfold μy; rw [ht]; norm_num
  · unfold μy; rw [ht]; norm_num
  · unfold νy μy; rw [ht]; norm_num
  · unfold νy μy; rw [ht]; norm_num
  · unfold dStar; rw [min_eq_left hB]; exact rStar_add_sStar νy
  · unfold g1 rStar sStar νy μy; rw [lam_zeta]; ring
  · unfold g1 rStar sStar νy μy; rw [lam_zeta]; have := zeta_pos; have := theta0_pos; linarith
  · unfold g1 rStar sStar νy μy; rw [lam_zeta]; have := zeta_pos; have := theta0_pos; linarith

end HBCaseIII
end ResearchBankV12
end Erdos287
