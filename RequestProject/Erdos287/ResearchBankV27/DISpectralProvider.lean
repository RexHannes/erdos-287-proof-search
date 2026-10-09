import RequestProject.Erdos287.ResearchBankV27.DecoratedMaynardSetup

/-!
# Erdős #287 — Research Bank V27 §5.9: the ONE minimal DI / spectral provider

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`DISpectralProvider` is the single public Deshouillers–Iwaniec / Maynard spectral input used
AFTER the grouped coefficient has been constructed.  It is an EXTERNAL PROVIDER (never
constructed).  Its contract exposes exactly:

* the modulus variables `Q, R, S, N, d` and the scale `x`;
* the smooth Kloostermann-type kernel `Kl(b; z)` on regrouped outer variables `b` and grouped
  frequencies `z`;
* the coefficient vector `c(z)`, required to be supported on the off-diagonal range `offDiag`;
* the coefficient `L²` norm `‖c‖₂ = (Σ_z |c(z)|²)^{1/2}`;
* the loss `ε_DI`;
* the output bound `|Σ_b Σ_z c(z) Kl(b; z)| ≤ x^{ε_DI} Ξ ‖c‖₂`, together with its Maynard
  normalisation `mass · Ξ · √Rep ≤ N_q² T (Δ₂ + Δ₃)^{1/2}`.

Admissibility (`MaynardAdmissible`) is the literal range condition of §5.2 with `ε_DI = η/4`.
The provider replaces the former monolithic V16 source-class provider; nothing else analytic
about the clean sum is assumed.
-/

namespace Erdos287
namespace ResearchBankV27
namespace DISpectral

open DecoratedMaynardSetup

/-- The data of one Kloosterman-type bilinear form (modulus variables, kernel, range, loss,
normalisation parameters). -/
structure KloostermanData where
  B : Type
  Z : Type
  [fB : Fintype B]
  [fZ : Fintype Z]
  [dZ : DecidableEq Z]
  Kl : B → Z → ℂ
  offDiag : Finset Z
  Q : ℝ
  R : ℝ
  S : ℝ
  N : ℝ
  d : ℝ
  x : ℝ
  epsDI : ℝ
  Xi : ℝ
  mass : ℝ
  Rep : ℝ
  Nq : ℝ
  T : ℝ
  Delta2 : ℝ
  Delta3 : ℝ

attribute [instance] KloostermanData.fB KloostermanData.fZ KloostermanData.dZ

/-- The bilinear form `Σ_b Σ_z c(z) Kl(b; z)`. -/
noncomputable def bilinear (K : KloostermanData) (c : K.Z → ℂ) : ℂ :=
  ∑ b, ∑ z, c z * K.Kl b z

/-- The coefficient `L²` norm. -/
noncomputable def l2 {Z : Type} [Fintype Z] (c : Z → ℂ) : ℝ := Real.sqrt (∑ z, ‖c z‖ ^ 2)

/-- The conclusion of the DI / spectral estimate for one form. -/
def DIConclusion (K : KloostermanData) : Prop :=
  0 ≤ K.Xi ∧
    (∀ c : K.Z → ℂ, (∀ z, z ∉ K.offDiag → c z = 0) →
      ‖bilinear K c‖ ≤ K.x ^ K.epsDI * K.Xi * l2 c) ∧
    K.mass * K.Xi * Real.sqrt K.Rep ≤ K.Nq ^ 2 * K.T * Real.sqrt (K.Delta2 + K.Delta3)

/-- Maynard admissibility: literal range conditions of §5.2 and `ε_DI = η/4`. -/
def MaynardAdmissible (η : ℝ) (K : KloostermanData) : Prop :=
  1 < K.x ∧ K.epsDI = η / 4 ∧ RangeConditions K.N K.R K.S K.Q K.x η ∧
    K.Delta2 = Delta2 K.N K.R K.S K.Q K.x ∧ K.Delta3 = Delta3 K.N K.R K.S K.Q K.x

/-- **The ONE minimal DI / spectral provider** (EXTERNAL PROVIDER; never constructed).
`DIClass` is the class of bilinear forms covered by the public Deshouillers–Iwaniec /
Maynard spectral estimate (forms whose kernel is the smooth Kloosterman-type sum of the decorated lemma, with its
true normalisation parameters); membership of each realized form is certified by the clean
realization.  Without such a class restriction the statement is FALSE
(`unrestricted_provider_false`). -/
structure DISpectralProvider (η : ℝ) (DIClass : KloostermanData → Prop) : Prop where
  spectral : ∀ K : KloostermanData, DIClass K → MaynardAdmissible η K → DIConclusion K

/-- A degenerate admissible form violating the DI conclusion: `Kl ≡ 1` on one point, `Ξ = 0`. -/
noncomputable def degenerateForm (η : ℝ) : KloostermanData where
  B := Unit
  Z := Unit
  Kl := fun _ _ => 1
  offDiag := Finset.univ
  Q := 0
  R := 0
  S := 0
  N := 0
  d := 0
  x := 2
  epsDI := η / 4
  Xi := 0
  mass := 0
  Rep := 0
  Nq := 0
  T := 0
  Delta2 := 0
  Delta3 := 0

theorem degenerateForm_admissible (η : ℝ) : MaynardAdmissible η (degenerateForm η) := by
  refine ⟨by norm_num [degenerateForm], rfl, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp [degenerateForm, Delta1, Delta2, Delta3, Real.rpow_nonneg]

theorem degenerateForm_not_DI (η : ℝ) : ¬ DIConclusion (degenerateForm η) := by
  rintro ⟨-, hb, -⟩
  have := hb (fun _ => 1) (fun z hz => absurd (Finset.mem_univ z) hz)
  simp [bilinear, degenerateForm] at this
  linarith

/-- **The DI conclusion is not automatic** (FINITE REGRESSION): some admissible form violates it. -/
theorem DI_not_automatic : ¬ ∀ K : KloostermanData, DIConclusion K :=
  fun h => degenerateForm_not_DI 0 (h _)

/-- **The unrestricted provider is false** (FINITE REGRESSION): the class restriction is
load-bearing. -/
theorem unrestricted_provider_false (η : ℝ) : ¬ DISpectralProvider η (fun _ => True) :=
  fun h => degenerateForm_not_DI η (h.spectral _ trivial (degenerateForm_admissible η))

/-- Admissible forms satisfy the range bounds on `Δ₂, Δ₃` (LEAN BANK bookkeeping). -/
theorem admissible_delta_bounds {η : ℝ} {K : KloostermanData} (h : MaynardAdmissible η K) :
    K.Delta2 ≤ K.x ^ (-14 * η) ∧ K.Delta3 ≤ K.x ^ (-14 * η) := by
  obtain ⟨-, -, ⟨-, h2, h3⟩, e2, e3⟩ := h
  exact ⟨e2 ▸ h2, e3 ▸ h3⟩

end DISpectral
end ResearchBankV27
end Erdos287
