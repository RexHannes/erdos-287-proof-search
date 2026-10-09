import Mathlib.Tactic
import RequestProject.Erdos287.ResearchBankV15.OneLemmaReduction
import RequestProject.Erdos287.ResearchBankV15.CRTResidues
import RequestProject.Erdos287.ResearchBankV14.EffectivityFirewall

/-!
# Erdős #287 — Research Bank V15 §C: Pascadi / Maynard scope firewalls

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Documentation / provider metadata only:

* `pascadiNotes` — Pascadi's `5/8 − o(1)` result requires triply-well-factorable weights;
  well-factorable results carry explicit factorization contracts; a modulus exponent `< 5/8` is
  not by itself sufficient; fixed-residue statements need not handle the actual root-dependent
  CRT residue;
* `exponent_fact_does_not_construct_provider` — the true numerical fact `0.624 < 5/8` does **not**
  imply the pair provider for every source: there is source data (`N_X ≡ 0`, `W_F = −1000`) at
  which the provider is false.  So no theorem can construct `ActualWeightedColouredPairProvider`
  from that statement alone;
* `residue_is_root_dependent` — the CRT residue moves with the tuple (V15 `CRTResidues`), so a
  fixed-residue estimate is not automatically the required one;
* `v15_effectivity_firewall` — the V14 effectivity firewall is unchanged.
-/

namespace Erdos287
namespace ResearchBankV15
namespace ScopeFirewalls

open ResearchBankV14 ResearchBankV14.BalancedKernelParameters
open ResearchBankV14.ConditionalAsymptoticImplication
open FixedAffineSource Normalization PairProvider

/-- Pascadi / Maynard metadata (documentation only; no theorem is derived from it). -/
def pascadiNotes : List String :=
  [ "Pascadi 5/8 - o(1): requires triply-well-factorable weights"
  , "well-factorable results: explicit factorization contracts"
  , "modulus exponent < 5/8: not sufficient by itself"
  , "fixed-residue statements: may not handle the actual root-dependent CRT residue" ]

/-- Degenerate source data with `N_X ≡ 0`. -/
noncomputable def degenerateSource : SourceData where
  G := fun _ => 0
  Xs := fun _ => 2
  W0 := 1
  W0_pos := Nat.one_pos
  b0 := 0
  D := fun _ => ∅
  CX := fun _ => 0
  SW0 := 0
  I := 0

theorem A0_real : ((A0 : ℚ) : ℝ) = 2000599 / 599000 := by unfold A0; norm_num

/-- The pair provider is a genuine (falsifiable) proposition. -/
theorem provider_fails_degenerate :
    ¬ PairProvider.ActualWeightedColouredPairProvider degenerateSource (-1000) := by
  intro h
  obtain ⟨M₀, hM⟩ := h.eventual 1 one_pos
  have := hM M₀ le_rfl
  have hN : NX degenerateSource M₀ = 0 := by simp [NX, degenerateSource]
  rw [hN, div_zero, A0_real] at this
  norm_num at this

/-- **`0.624 < 5/8` does not construct the pair provider.** -/
theorem exponent_fact_does_not_construct_provider :
    (0.624 : ℝ) < 5 / 8 ∧
      ¬ ((0.624 : ℝ) < 5 / 8 →
        ∀ (src : SourceData) (WF : ℝ), PairProvider.ActualWeightedColouredPairProvider src WF) :=
  ⟨by norm_num, fun h => provider_fails_degenerate (h (by norm_num) _ _)⟩

/-- The CRT residue is root-dependent (re-export of the V15 fixture): `t = 4` solves the
congruence system for slope `1` modulo `5` but not for slope `2`. -/
theorem residue_is_root_dependent :
    CRTResidues.Solves (K := 1) ![1] ![5] 4 ∧ ¬ CRTResidues.Solves (K := 1) ![2] ![5] 4 :=
  CRTResidues.residue_moves_with_tuple

/-- The V14 effectivity firewall is unchanged in V15. -/
theorem v15_effectivity_firewall (A : ℝ) :
    EffectivityFirewall.compilerUsefulHeightBound = none ∧
      EffectivityFirewall.explicitAnalyticThreshold = none ∧
      ResearchBankV11.AnalyticActivation.current_M_an A = none ∧
      EffectivityFirewall.finiteSpliceClosed = false ∧
      ResearchBankV13.AuditedEndpoint.concreteFinitePayload =
        ResearchBankV13.AuditedEndpoint.PayloadStatus.notSupplied :=
  EffectivityFirewall.effectivity_firewall A

end ScopeFirewalls
end ResearchBankV15
end Erdos287
