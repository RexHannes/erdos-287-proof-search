import RequestProject.Erdos287.ResearchBankV12.HBCaseI
import RequestProject.Erdos287.ResearchBankV12.HBCaseII
import RequestProject.Erdos287.ResearchBankV12.HBCaseIII

/-!
# Erdős #287 — Research Bank V12 §13: full support routing (concrete)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

An **actual HB support box** (`ActualHBBox`) consists of

* HB factor data `D` (at most eight exponents, `∑ = 1`, Möbius labels `≤ 1/4`);
* `θ ∈ [0, θ₀]`, modulus exponents `r, s ≥ 0`;
* a selected partial-product exponent `ν` together with the **explicit classification
  hypothesis** `selected`: Case I, or `ν` is a Case-II witness, or `ν` is a Case-III witness.
  This hypothesis is always satisfiable (`selection_available`, from the proved selection
  theorem), so it is not an extra assumption on `D`;
* the **legal factorization** bounds `legal`: in Case I, `r ≤ rI`, `s ≤ sI`; otherwise
  `r ≤ r*(ν)`, `s ≤ s*(ν)` (a legal factorization chosen at the original level, §14).

`every_actual_HB_box_routed`: every actual box falls into at least one of
(1) `smallBV`, (2) the frozen Type-I domain, (3) the restored Type-II domain (overlap allowed).
`every_actual_HB_box_routed_with_margins` attaches the proved margins in each branch.  Both depend
only on exact rational geometry and the classification hypothesis — **not** on the truth of any
analytic estimate.
-/

namespace Erdos287
namespace ResearchBankV12
namespace HBFullSupportConcrete

open ConcreteParameters TypeIIWholeRectangle HBSelectionConcrete ResearchBankV10.HBSelection
  HBCaseI HBCaseIII

/-- An actual HB support box. -/
structure ActualHBBox where
  D : HBData
  θ : ℚ
  r : ℚ
  s : ℚ
  ν : ℚ
  θ_nonneg : 0 ≤ θ
  θ_le : θ ≤ theta0
  r_nonneg : 0 ≤ r
  s_nonneg : 0 ≤ s
  selected : CaseI D.factors ∨ CaseIIWitness D.factors ν ∨ CaseIIIWitness D.factors ν
  legal : (CaseI D.factors → r ≤ rI (maxSmooth D.factors) θ ∧ s ≤ sI (maxSmooth D.factors) θ) ∧
    (¬ CaseI D.factors → r ≤ rStar ν ∧ s ≤ sStar ν)

namespace ActualHBBox

variable (b : ActualHBBox)

/-- `μ` = the largest smooth exponent. -/
def μ : ℚ := maxSmooth b.D.factors

/-- The frozen Type-I domain. -/
def InTypeI : Prop :=
  (CaseI b.D.factors ∧ CaseIBox b.μ b.θ b.r b.s) ∨
    (CaseIIIWitness b.D.factors b.ν ∧ b.r + b.s ≤ dStar b.μ b.θ + zeta)

/-- The restored Type-II domain. -/
def InTypeII : Prop :=
  (CaseIIWitness b.D.factors b.ν ∧ CaseIIBox b.ν b.θ b.r b.s) ∨
    (CaseIIIWitness b.D.factors b.ν ∧ HBCaseIII.LegalBox b.ν b.θ b.r b.s ∧
      dStar b.μ b.θ - zeta ≤ b.r + b.s)

end ActualHBBox

/-- The classification hypothesis is always satisfiable: for all HB data there is a selection. -/
theorem selection_available (D : HBData) :
    ∃ ν, CaseI D.factors ∨ CaseIIWitness D.factors ν ∨ CaseIIIWitness D.factors ν := by
  rcases concrete_selection D with h | ⟨ν, h⟩ | ⟨ν, h⟩
  · exact ⟨0, Or.inl h⟩
  · exact ⟨ν, Or.inr (Or.inl h)⟩
  · exact ⟨ν, Or.inr (Or.inr h)⟩

/-- **Every actual HB box is routed** to BV, frozen Type I, or restored Type II. -/
theorem every_actual_HB_box_routed (b : ActualHBBox) :
    smallBV b.θ b.r b.s ∨ b.InTypeI ∨ b.InTypeII := by
  by_cases hI : CaseI b.D.factors
  · obtain ⟨h1, h2⟩ := b.legal.1 hI
    exact Or.inr (Or.inl (Or.inl ⟨hI, ⟨hI, b.θ_nonneg, b.θ_le, b.r_nonneg, h1, b.s_nonneg, h2⟩⟩))
  · obtain ⟨h1, h2⟩ := b.legal.2 hI
    rcases b.selected with h | h | h
    · exact absurd h hI
    · by_cases hbv : smallBV b.θ b.r b.s
      · exact Or.inl hbv
      · exact Or.inr (Or.inr (Or.inl ⟨h, b.θ_nonneg, b.θ_le, b.r_nonneg, h1, b.s_nonneg, h2, hbv⟩))
    · rcases (overlap b.μ b.θ).2.2 (b.r + b.s) with ht | ht
      · exact Or.inr (Or.inl (Or.inr ⟨h, ht⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h, ⟨b.θ_nonneg, b.θ_le, b.r_nonneg, h1, b.s_nonneg, h2⟩, ht⟩))

/-- **Routing with margins**: in each branch the corresponding proved margin is available. -/
theorem every_actual_HB_box_routed_with_margins (b : ActualHBBox) :
    smallBV b.θ b.r b.s ∨
    (b.InTypeI ∧ (zeta ≤ b.μ - 3 * b.θ - b.s ∨
      9 * zeta ≤ (1 + 2 * b.μ - lam - 7 * b.θ) / 2 - (b.r + b.s))) ∨
    (b.InTypeII ∧ ((1 / 208 ≤ g1 b.θ b.r b.s b.ν ∧ 9 / 208 - theta0 ≤ g2 b.θ b.r b.ν ∧
      7 / 208 ≤ g3 b.θ b.r b.ν) ∨ 0 < g1 b.θ b.r b.s b.ν)) := by
  rcases every_actual_HB_box_routed b with h | h | h
  · exact Or.inl h
  · refine Or.inr (Or.inl ⟨h, ?_⟩)
    rcases h with ⟨-, hb⟩ | ⟨-, ht⟩
    · exact Or.inl (HBCaseI.reserve _ _ _ _ hb)
    · exact Or.inr (typeI_level_reserve ht).1
  · refine Or.inr (Or.inr ⟨h, ?_⟩)
    rcases h with ⟨hw, hb⟩ | ⟨⟨h1, h2, -, h4, -, h6⟩, hb, ht⟩
    · exact Or.inl (worst_case_margins hb hw.2.1 hw.2.2)
    · exact Or.inr (g1_pos_on_typeII_window hb h2 h4 h6 ht)

/-- The routing is not vacuous: an explicit actual box (the Case-III fixture) exists. -/
def fixtureData : HBData where
  factors := caseIIIList
  length_le := by decide
  nonneg := by intro x hx; simp [caseIIIList] at hx; rcases hx with rfl | rfl <;> norm_num
  sum_one := by norm_num [caseIIIList]
  mobius_le := by
    intro x hx hs; simp [caseIIIList] at hx; rcases hx with rfl | rfl
    · simp at hs
    · norm_num

def fixtureBox : ActualHBBox where
  D := fixtureData
  θ := 0
  r := 0
  s := 0
  ν := 1 / 10
  θ_nonneg := le_rfl
  θ_le := theta0_pos.le
  r_nonneg := le_rfl
  s_nonneg := le_rfl
  selected := Or.inr (Or.inr caseIII_fixture)
  legal := ⟨fun h => absurd h caseIII_fixture_only.1, fun _ => by
    unfold rStar sStar; rw [lam_eq, zeta_eq]; constructor <;> norm_num⟩

theorem fixtureBox_routed : smallBV fixtureBox.θ fixtureBox.r fixtureBox.s ∨
    fixtureBox.InTypeI ∨ fixtureBox.InTypeII :=
  every_actual_HB_box_routed fixtureBox

/-! ## §14 Well-factorability firewall (preserved) and the legal data flow -/

open ResearchBankV10.WellFactorableCutoff in
/-- **Firewall preserved**: well-factorable at level `D` does **not** imply that the truncation
to `D' ≤ D` is well-factorable at level `D'` (V10 counterexample `δ₃`, `D = 6`, `D' = 4`). -/
theorem wf_truncation_firewall :
    ¬ ∀ (lam : ℕ → ℤ) (D D' : ℕ), D' ≤ D → WellFactorable lam D →
      WellFactorable (truncate lam D') D' :=
  wf_truncation_not_automatic

open ResearchBankV10.WellFactorableCutoff in
/-- **The legal routing data flow**: (1) choose a legal factorization `λ = α ⋆ β` at the
*original* level; (2) insert the product cutoff afterwards; (3) separate the cutoff
(Mellin/Fourier separation, an explicit external object `CutoffSeparation`).  The truncated
weight is then the sum of bilinear pieces with the original supports, up to
`ε · #{(a, b) : ab = n}`.  No shortcut through "the truncation is well-factorable" is used. -/
theorem legal_cutoff_dataflow (lam α β : ℕ → ℂ) (hconv : ∀ n, lam n = dconv α β n)
    (hα : ∀ n, ‖α n‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) {D' : ℕ} {ε : ℝ}
    (sep : CutoffSeparation D' ε) (n : ℕ) :
    ‖truncate lam D' n -
        ∑ j ∈ sep.J, dconv (fun a => α a * sep.f j a) (fun b => β b * sep.g j b) n‖ ≤
      ε * (n.divisorsAntidiagonal.card : ℝ) :=
  cutoff_separated_bilinear lam α β hconv hα hβ sep n

end HBFullSupportConcrete
end ResearchBankV12
end Erdos287
