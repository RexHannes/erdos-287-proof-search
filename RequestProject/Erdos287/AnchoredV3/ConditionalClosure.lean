import RequestProject.Erdos287.AnchoredV3.AlignmentPolynomial
import RequestProject.Erdos287.AnchoredV3.ResonanceInterfaces
import RequestProject.Erdos287.AnchoredV3.BaselineCentrality

/-!
# Anchored V3 — the conditional terminal closure theorem

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

This module contains the exact **dependency theorem** of the V3 layer.  Every analytic
ingredient enters as an explicit hypothesis; nothing analytic is proved or assumed here.

Given

* a compatible baseline and a central baseline (declared inputs);
* legal target-mobility reservations (carried by the `AlignedBank` structure);
* the global column compiler instantiated on the fixed bank (`AlignedBank.alignment_coefficient`);
* the bounded-tilt interface (declared input);
* the sparse-resonance arc budget, the central-lobe budget and the remaining-spectrum budget,
  with total constant below `5 / 6`;
* the OPEN Fourier anti-hole bridge and a coefficient model of `F(X) M_Z(X)`;

the theorem concludes that the exact target coefficient is positive and hence that an exact
globally band-neutral terminal completion of that prepared baseline exists.

**The chain stops there.**  No bridge from a terminal completion to a global Erdős #287
counterexample exists in this project, and none is invented here.

The compatibility, centrality and bounded-tilt hypotheses are carried as declared inputs of the
dependency statement (as specified); the formal derivation runs through the budget chain and the
compiler.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV3

/-- A finite coefficient object **models** the terminal × mobility coefficient of a fixed bank
when positivity of its coefficient at `T` witnesses a terminal/mobility decomposition of `T`. -/
def CoefficientModel {H : ℕ} (A : AlignedBank H) (K : FiniteCoeff) : Prop :=
  ∀ T : ℕ, 0 < K.c T → ∃ y : Finset (Fin H), ∃ t : ℕ, A.B.InSupport t ∧ t + A.mobWeight y = T

/-- **The conditional terminal closure theorem.**

Under the declared baseline hypotheses, the three analytic budgets, the OPEN Fourier anti-hole
bridge and a coefficient model of the combined terminal × mobility object, the exact target
coefficient is positive and an exact globally band-neutral terminal completion of the prepared
baseline exists. -/
theorem conditional_terminal_closure {H : ℕ} (A : AlignedBank H) (K : FiniteCoeff)
    (cb : BaselineConstraints) (eta Call : ℝ)
    (hcompat : CompatibleBaseline cb)
    (hcentral : CentralBaseline cb eta Call ((A.Sstar : ℚ) : ℝ))
    (lam Dreal Mreal Ctilt : ℝ) (htilt : BoundedTilt lam Dreal Mreal Ctilt)
    (S : Resonance.SpectrumSplit K) (b₁ b₂ b₃ : ℝ)
    (harc : Resonance.SparseResonanceArcBudget S b₁)
    (hlobe : Resonance.CentralLobeBudget S b₂)
    (hrest : Resonance.RemainingSpectrumBudget S b₃)
    (hb : b₁ + b₂ + b₃ < 5 / 6)
    (hmean : K.mean S.lam = (A.Tstar : ℝ)) (hvar : S.sigma ^ 2 = K.var S.lam)
    (bridge : AntiHoleBridge) (model : CoefficientModel A K) :
    0 < K.c A.Tstar ∧
      ∃ y : Finset (Fin H), ∃ sel : ℕ → Finset ℕ,
        A.B.Neutral sel ∧ A.S y + A.B.delta sel = 1 := by
  have hinput : K.AntiHoleInput A.Tstar :=
    { lam := S.lam
      sigma := S.sigma
      hsigma := S.hsigma
      hvar := hvar
      hmean := hmean
      harc := Resonance.arc_bound_of_budgets S harc hlobe hrest hb }
  have hpos : 0 < K.c A.Tstar := bridge K A.Tstar ⟨hinput⟩
  refine ⟨hpos, ?_⟩
  obtain ⟨y, t, ht, hsum⟩ := model A.Tstar hpos
  exact (A.alignment_coefficient).mpr ⟨y, t, ht, hsum⟩

end AnchoredV3
end Erdos287
