import RequestProject.Erdos287.AnchoredV3.ConditionalClosure
import RequestProject.Erdos287.AnchoredV2.RouteBridge
import RequestProject.Erdos287.AnchoredV2.CoupledBatchSupply

/-!
# Anchored V3 — the actual remaining open owners

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Every currently unproved research obligation of the V3 layer is an ordinary `Prop` with **no
inhabitant**, used only as a hypothesis of a conditional theorem.  There is no custom `axiom`,
no `sorry`, no `native_decide`, no `opaque` and no `@[implemented_by]` anywhere in this layer,
and no theorem named `erdos287_closed`, `counterexample` or `fullClosure` exists.

The owners are:

* `CompatibleActualBaseline` — an actual baseline satisfying every inherited constraint;
* `CentralCompatibleActualBaseline` — such a baseline additionally inside the
  correction-capacity window;
* `CentralityToBoundedTilt` — the conditioned-column estimate turning centrality into a bounded
  tilt (`BaselineCentrality.lean`);
* `AntiHoleBridge` — the Fourier-inversion anti-hole theorem (`FourierHitInterface.lean`);
* `SparseResonanceArcBudget`, `CentralLobeBudget`, `RemainingSpectrumBudget` — the three
  analytic spectrum budgets (`ResonanceInterfaces.lean`);
* `AsymptoticUniformRowFibres` — the uniform row-fibre estimate (`SupportMultiplicity.lean`);
* the inherited Anchored V2 owners `FixedPowerCoupledSupply`, `UniformNegativeCapacity` and
  `UniformLevel2Rejection`, which are referenced here and **not** re-proved, re-stated or
  weakened.
-/

namespace Erdos287
namespace AnchoredV3
namespace OpenOwners

/-- **OPEN owner.**  An actual baseline meeting every inherited constraint.  The constraint
bundle `cb` is the one carried by the concrete baseline; supplying this proposition is exactly
the unproved obligation.  It is never inhabited in this project. -/
def CompatibleActualBaseline (cb : BaselineConstraints) : Prop := CompatibleBaseline cb

/-- **OPEN owner.**  An actual compatible baseline that additionally lies inside the
correction-capacity window.  Never inhabited in this project. -/
def CentralCompatibleActualBaseline (cb : BaselineConstraints) (eta Call Sstar : ℝ) : Prop :=
  CentralBaseline cb eta Call Sstar

/-- **OPEN owner** (alias): centrality implies bounded tilt. -/
abbrev CentralityToBoundedTiltOwner : Prop := CentralityToBoundedTilt

/-- **OPEN owner** (alias): the Fourier anti-hole bridge. -/
abbrev AntiHoleBridgeOwner : Prop := AntiHoleBridge

/-- **OPEN owner** (alias): the sparse-resonance arc budget. -/
abbrev SparseResonanceArcBudgetOwner {K : FiniteCoeff} (S : Resonance.SpectrumSplit K)
    (b : ℝ) : Prop := Resonance.SparseResonanceArcBudget S b

/-- **OPEN owner** (alias): the central-lobe budget. -/
abbrev CentralLobeBudgetOwner {K : FiniteCoeff} (S : Resonance.SpectrumSplit K) (b : ℝ) : Prop :=
  Resonance.CentralLobeBudget S b

/-- **OPEN owner** (alias): the remaining-spectrum budget. -/
abbrev RemainingSpectrumBudgetOwner {K : FiniteCoeff} (S : Resonance.SpectrumSplit K)
    (b : ℝ) : Prop := Resonance.RemainingSpectrumBudget S b

/-! ## Inherited Anchored V2 owners

These are referenced, never re-proved or weakened. -/

#check @Erdos287.AnchoredV2.FixedPowerCoupledSupply
#check @Erdos287.AnchoredV2.UniformNegativeCapacity
#check @Erdos287.AnchoredV2.UniformLevel2Rejection

end OpenOwners
end AnchoredV3
end Erdos287
