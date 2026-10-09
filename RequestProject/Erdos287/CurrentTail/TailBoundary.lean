import RequestProject.Erdos287.CurrentTail.RemainderRecombination
import RequestProject.Erdos287.CurrentTail.SevenBlockConsumer

/-!
# Erdős #287 — current tail consolidation: the tail-theorem boundary

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

* `Tail287Statement` — the asymptotic tail: there is `M₀` such that every #287 counterexample
  has `max A < M₀` (existential; no numeral).
* `SevenBlockTailFramework` — the structural (paper-level, `Candidate`) framework: for every
  exact word beyond some onset there is a scale `X ≥ X₀` and a `7`-block affine compiler for
  `Γ_{7,2}` with window control whose normalised moments are `(μ, ν)` up to `R_Σ^P(X)/𝒩_X I`.
  Analogue of the W3 framework input; it contains no analytic estimate and no tail conclusion.
* `tail_of_remainder_littleO` — framework + `R_Σ^P = o(𝒩_X I)` ⟹ `Tail287Statement`
  (kernel-proved; uses the seven-block consumer and the trusted affine compiler / row rigidity).
* **`Tail287_of_AnalyticProviders`** — the *conditional* tail theorem: framework + source
  dictionary + all listed analytic providers ⟹ `Tail287Statement`.

**No unconditional tail theorem is constructed.**  It must not be constructed until every
analytic provider has a genuine proof or imported formal theorem *and* the latest Ordering-B
repair has passed independent referee audit.  No alias identifies the two.
-/

open scoped BigOperators
open Finset

namespace Erdos287.CurrentTail

open Erdos287 Erdos287.PostV71V87 Erdos287.PostV87V90R

/-- **The asymptotic tail statement** (existential onset). -/
def Tail287Statement : Prop :=
  ∃ M0 : ℕ, ∀ A : Finset ℕ, ∀ hA : Erdos287Counterexample A, A.max' hA.nonempty < M0

variable {ι : Type*}

/-- **Seven-block tail framework (structural input, status `Candidate`).** -/
structure SevenBlockTailFramework (S : TailSourceFamily ι) : Prop where
  scale : ∀ X0 : ℕ, ∃ M0 : ℕ, ∀ W : ExactWord, 1 < W.a → M0 ≤ W.M →
    ∃ X ≥ X0, ∃ (K : ℕ) (C : AffineContactCompiler 7 2 K) (F : FiniteWeights) (H : ℕ),
      SevenBlockMainTermDictionary F (blockCount C) ((S.T X).RSigmaP) (S.target X) ∧
      ∀ t ∈ F.T, 0 < F.w t → WindowControl C W.a W.M H t

/-- **Framework + `R_Σ^P = o(𝒩_X I)` ⟹ asymptotic tail.** -/
theorem tail_of_remainder_littleO (S : TailSourceFamily ι) (Fw : SevenBlockTailFramework S)
    (h : IsLittleOTarget (fun X => (S.T X).RSigmaP) S.target) : Tail287Statement := by
  obtain ⟨X0, hX0⟩ := h 1 one_pos
  obtain ⟨M0, hM0⟩ := Fw.scale X0
  refine ⟨M0, fun A hA => ?_⟩
  by_contra hlt
  push_neg at hlt
  set W := ofCounterexample hA
  have ha : 1 < W.a := ofCounterexample_one_lt_a hA
  have hM : M0 ≤ W.M := by rw [ofCounterexample_M]; exact hlt
  obtain ⟨X, hX, K, C, F, H, D, hctrl⟩ := hM0 W ha hM
  have hR : |(S.T X).RSigmaP| ≤ S.target X := by simpa using hX0 X hX
  exact seven_block_contact_false_of_remainder W C F D hR hctrl

/-- **Conditional tail theorem `Tail287_of_AnalyticProviders`.**  Kernel-proved implication
from: the seven-block framework, the Ordering-B source dictionary, and the analytic providers
(`MaynardE1Estimate`, `PascadiE2Printed`, `QuantitativeTH`, `BDHFamily`,
`SpectatorMomentFamily`, `BaseSWProvider`, `AuxPieceProviders`).  NOT an unconditional result. -/
theorem Tail287_of_AnalyticProviders (S : TailSourceFamily ι)
    {θ σlo σhi δ A0 A θQ θR θH δ2 : ℝ} {B E : ℕ} {Q0 Q Xmax : ℕ → ℕ}
    {Bf : ℕ → ℝ → ℝ → ℝ} {Cm : ℕ → ℝ}
    (Fw : SevenBlockTailFramework S)
    (D : OrderingBSourceDictionary S (MaynardE1Estimate θ σlo σhi δ B A0 A)
      (PascadiE2Printed θQ θR θH δ2) (QuantitativeTH θQ θR θH δ2) (BDHFamily S Q0 Q Bf)
      (SpectatorMomentFamily E Xmax Cm))
    (hE1 : MaynardE1Estimate θ σlo σhi δ B A0 A)
    (hE2p : PascadiE2Printed θQ θR θH δ2) (hE2q : QuantitativeTH θQ θR θH δ2)
    (hBDH : BDHFamily S Q0 Q Bf) (hMom : SpectatorMomentFamily E Xmax Cm)
    (hBase : BaseSWProvider S) (hAux : AuxPieceProviders S) :
    Tail287Statement :=
  tail_of_remainder_littleO S Fw
    (RSigmaP_littleO_of_providers S D hE1 hE2p hE2q hBDH hMom hBase hAux)

end Erdos287.CurrentTail
