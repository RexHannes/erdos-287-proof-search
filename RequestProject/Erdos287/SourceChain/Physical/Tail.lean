import RequestProject.Erdos287.SourceChain.OneSidedSevenBlock
import RequestProject.Erdos287.SourceChain.Physical.Remainder
import RequestProject.Erdos287.SourceChain.Physical.Presieve

/-!
# Erdős #287 — physical source: the physical remainder plugged into the one-sided tail boundary

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.  Every theorem here is CONDITIONAL.**

The existing tail consumer `tail_of_remainder_littleO_oneSided` only uses the remainder as a
function of the scale.  Here it is restated for an arbitrary remainder function
(`OneSidedFrameworkFor`, `tail_of_littleO_for`; `framework_iff` shows the old framework is the
special case `R = (S.T X).RSigmaP`), and then instantiated with the **literal physical
remainder** `physicalFamily.R X = R_Σ^P(X)` built in `Physical/Remainder.lean`:

* `physDataAt P₀ X` — the physical data at scale `X` with the actual presieve `W = physW X`;
* `physDataAt_wgood` — the presieve hypotheses hold for all large `X` (proved);
* `physical_littleO_of_rel_base` — `R_rel = o(target)` and `R_base = o(target)` imply
  `R_Σ^P = o(target)` (via the proved exact centering `R_Σ^P = R_rel + R_base`);
* `Tail287_of_physical` — **conditional**: the one-sided seven-block framework for the physical
  remainder, plus `R_rel = o`, `R_base = o`, imply `Tail287Statement`.

The framework, `R_rel = o(𝒩_X I)` and `R_base = o(𝒩_X I)` remain explicit hypotheses.
-/

open scoped BigOperators
open Finset

namespace Erdos287.Physical

open Erdos287 Erdos287.PostV71V87 Erdos287.PostV87V90R Erdos287.CurrentTail
  Erdos287.SourceChain

/-- The one-sided seven-block framework, for an arbitrary remainder function `R`. -/
structure OneSidedFrameworkFor (R target : ℕ → ℝ) : Prop where
  errors : ∃ e₁ e₂ : ℕ → ℝ, (∀ ε > 0, ∃ X0 : ℕ, ∀ X ≥ X0, e₁ X ≤ ε ∧ e₂ X ≤ ε) ∧
    ∀ X0 : ℕ, ∃ M0 : ℕ, ∀ W : ExactWord, 1 < W.a → M0 ≤ W.M →
      ∃ X ≥ X0, ∃ (K : ℕ) (C : AffineContactCompiler 7 2 K) (F : FiniteWeights) (H : ℕ),
        OneSidedSevenBlockDictionary F (blockCount C) (e₁ X) (e₂ X) (R X) (target X) ∧
        ∀ t ∈ F.T, 0 < F.w t → WindowControl C W.a W.M H t

/-- The old framework is the special case `R X = (S.T X).RSigmaP`. -/
theorem framework_iff {ι : Type*} (S : TailSourceFamily ι) :
    OneSidedSevenBlockTailFramework S ↔
      OneSidedFrameworkFor (fun X => (S.T X).RSigmaP) S.target :=
  ⟨fun h => ⟨h.errors⟩, fun h => ⟨h.errors⟩⟩

/-- **Tail boundary for an arbitrary remainder function** (conditional). -/
theorem tail_of_littleO_for {R target : ℕ → ℝ} (Fw : OneSidedFrameworkFor R target)
    (h : IsLittleOTarget R target) : Tail287Statement := by
  obtain ⟨e₁, e₂, he, hscale⟩ := Fw.errors
  obtain ⟨X1, hX1⟩ := h (1 / 2) (by norm_num)
  obtain ⟨X2, hX2⟩ := he (1 / 2) (by norm_num)
  obtain ⟨M0, hM0⟩ := hscale (max X1 X2)
  refine ⟨M0, fun A hA => ?_⟩
  by_contra hlt
  push_neg at hlt
  set W := ofCounterexample hA
  have ha : 1 < W.a := ofCounterexample_one_lt_a hA
  have hM : M0 ≤ W.M := by rw [ofCounterexample_M]; exact hlt
  obtain ⟨X, hX, K, C, F, H, D, hctrl⟩ := hM0 W ha hM
  have hR : |R X| ≤ 1 / 2 * target X := by
    simpa using hX1 X ((le_max_left _ _).trans hX)
  obtain ⟨h1, h2⟩ := hX2 X ((le_max_right _ _).trans hX)
  have hq : |R X| / target X ≤ 1 / 2 := by
    rw [div_le_iff₀ D.NI_pos]; linarith
  exact seven_block_contact_false_oneSided W C F D (by linarith) (by linarith) hctrl

/-- The physical data at scale `X`: fixed slopes/test function from `P₀`, scale `X`, and the
actual presieve modulus `W = physW X`. -/
noncomputable def physDataAt (P₀ : PhysData) (X : ℕ) : PhysData :=
  { P₀ with W := physW X, X := X }

/-- The presieve hypotheses hold at the physical `W` for all large `X`. -/
theorem physDataAt_wgood (P₀ : PhysData) (ha : ∀ i, 0 < P₀.a i)
    (hinj : Function.Injective P₀.a) : ∃ X0 : ℕ, ∀ X ≥ X0, (physDataAt P₀ X).WGood := by
  obtain ⟨Y0, hY0⟩ := wgood_eventually P₀ ha hinj
  refine ⟨⌈Y0⌉₊, fun X hX => ?_⟩
  have hX' : Y0 ≤ (X : ℝ) := (Nat.le_ceil Y0).trans (by exact_mod_cast hX)
  have h := hY0 X hX'
  exact ⟨h.a_pos, h.W_pos, h.slope, h.diff⟩

/-- A scale-indexed physical source: physical data and scalar sieve at each scale, with the
normalisation `target X = 𝒩_X I(F)`. -/
structure PhysicalFamily where
  P : ℕ → PhysData
  S : ℕ → ScalarSieve
  target : ℕ → ℝ

namespace PhysicalFamily

variable (F : PhysicalFamily)

/-- The literal physical remainder `R_Σ^P(X)` of the family. -/
noncomputable def R (X : ℕ) : ℝ := (F.P X).RSigmaP (F.S X)

/-- The relative part `R_rel(X)`. -/
noncomputable def Rrel (X : ℕ) : ℝ := (F.P X).Rrel (F.S X)

/-- The base part `R_base(X)`. -/
noncomputable def Rbase (X : ℕ) : ℝ := (F.P X).Rbase (F.S X)

/-- `R_rel = o(target)`, `R_base = o(target)` ⟹ `R_Σ^P = o(target)` (exact centering). -/
theorem physical_littleO_of_rel_base
    (hgood : ∃ X0 : ℕ, ∀ X ≥ X0, (F.P X).WGood ∧ (F.S X).Good (F.P X).W)
    (hrel : IsLittleOTarget F.Rrel F.target) (hbase : IsLittleOTarget F.Rbase F.target) :
    IsLittleOTarget F.R F.target := by
  obtain ⟨X0, hX0⟩ := hgood
  intro ε hε
  obtain ⟨X1, hX1⟩ := hrel.add hbase ε hε
  refine ⟨max X0 X1, fun X hX => ?_⟩
  obtain ⟨hP, hS⟩ := hX0 X ((le_max_left _ _).trans hX)
  have := hX1 X ((le_max_right _ _).trans hX)
  unfold R
  rw [PhysData.RSigmaP_eq_rel_add_base hP (F.S X) hS]
  exact this

/-- **Conditional tail theorem with the literal physical remainder.**  Hypotheses: the
one-sided seven-block framework for `R_Σ^P`, the presieve/support conditions for large `X`,
and `R_rel = o(𝒩_X I)`, `R_base = o(𝒩_X I)`.  NOT unconditional. -/
theorem Tail287_of_physical (Fw : OneSidedFrameworkFor F.R F.target)
    (hgood : ∃ X0 : ℕ, ∀ X ≥ X0, (F.P X).WGood ∧ (F.S X).Good (F.P X).W)
    (hrel : IsLittleOTarget F.Rrel F.target) (hbase : IsLittleOTarget F.Rbase F.target) :
    Tail287Statement :=
  tail_of_littleO_for Fw (F.physical_littleO_of_rel_base hgood hrel hbase)

end PhysicalFamily

end Erdos287.Physical
