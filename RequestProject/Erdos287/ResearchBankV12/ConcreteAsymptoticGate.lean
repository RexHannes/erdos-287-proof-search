import RequestProject.Erdos287.ResearchBankV12.RestoredTypeIIEnvelope
import RequestProject.Erdos287.ResearchBankV12.HBFullSupportConcrete
import RequestProject.Erdos287.ResearchBankV12.RoughSeedConcrete

/-!
# Erdős #287 — Research Bank V12 §16: concrete asymptotic composition and the exact gate

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`mtSpecificAsymptotic_concrete` — the MT-specific asymptotic pair-distribution statement at level

  `ϑ = 7/13 − 3θ₀ − ε₀`,   `θ₀ = 1/25000 + 1/625000000`, `ε₀ = 1/100000`,

**conditional on visible hypotheses**:
* frozen V9/V10 algebra (`FrozenV9Bank`);
* Type-I analytic provider (`ZhengKloostermanInput`, `SmoothTypeIInput`);
* the restored Type-II spectral providers (`RestoredTypeIISpectralProvider`, one per Type-II box)
  together with the external Type-II reduction that consumes them;
* ordinary BV provider (`OrdinaryBVInput`);
* rough-seed SW provider (`SiegelWalfiszSeedInput`);
* conductor/root/base assumptions (`PacketCoprime`) and the HB decomposition bound.

It then proves the exact gate `ϑ > 78/145` and the existence of a rational `ξ > 0` with
`2/ϑ + ξ < 145/39`.

The theorem is **not** called `erdos287`; it proves nothing about #287 itself.  The firewall
`composition_does_not_construct_constants` records that the composition does not construct
`NumericalExternalConstants` (and hence no `M_an`).
-/

namespace Erdos287
namespace ResearchBankV12
namespace ConcreteAsymptoticGate

open ConcreteParameters RestoredTypeIIEnvelope ResearchBankV10.HBSupportCoverage
  ResearchBankV10.Providers ResearchBankV10.AsymptoticComposition ResearchBankV10.FrozenFrontier
  ResearchBankV10.TypeIICoefficient

/-- **Exact gate**: `ϑ > 78/145` and some rational `ξ > 0` has `2/ϑ + ξ < 145/39`. -/
theorem exact_gate : 78 / 145 < vartheta ∧ ∃ ξ : ℚ, 0 < ξ ∧ 2 / vartheta + ξ < 145 / 39 := by
  refine ⟨vartheta_gt, 52426455 / 18953756081 / 2, by norm_num, ?_⟩
  have h := pair_gap.1
  linarith [pair_gap.2]

/-- **The concrete asymptotic composition** (conditional on visible external providers). -/
theorem mtSpecificAsymptotic_concrete
    (boxes : Finset SupportBox) (E : SupportBox → ℝ → ℝ) (Δseed : ℕ → ℤ → ℝ → ℝ)
    (aSeed : ℕ → ℤ) {Bexp : ℝ} (hB : 0 ≤ Bexp) (Total : ℝ → ℝ) (Kl : ℕ → ℝ) (κ : ℝ)
    (packets : Finset CoeffVars)
    -- restored Type-II spectral data, one provider per Type-II box
    (Eh El Ed : SupportBox → ℝ → ℝ) (νOf : SupportBox → ℚ) (K ε : ℝ)
    -- frozen V9/V10 algebra
    (hfrozen : FrozenV9Bank)
    -- Type-I analytic provider
    (hZ : ZhengKloostermanInput Kl κ)
    (hI : SmoothTypeIInput concreteParams E Kl κ)
    -- restored Type-II spectral provider and the external reduction consuming it
    (hSpec : ∀ b, InTypeII concreteParams b →
      RestoredTypeIISpectralProvider (Eh b) (El b) (Ed b) b.θ b.r b.s (νOf b) K ε)
    (hIIred : (∀ b, InTypeII concreteParams b →
      RestoredTypeIISpectralProvider (Eh b) (El b) (Ed b) b.θ b.r b.s (νOf b) K ε) →
        RestoredTypeIIInput concreteParams E Kl κ packets)
    -- ordinary BV provider
    (hBV : OrdinaryBVInput concreteParams E)
    -- rough-seed SW provider
    (hSW : SiegelWalfiszSeedInput Δseed)
    -- conductor/root/base provider assumptions
    (hcond : PacketCoprime packets)
    -- HB decomposition
    (hHB : HBDecompositionBound boxes E Δseed aSeed Bexp Total) :
    MTSpecificAsymptotic concreteParams Total ∧ concreteParams.lam = vartheta ∧
      78 / 145 < vartheta ∧ ∃ ξ : ℚ, 0 < ξ ∧ 2 / vartheta + ξ < 145 / 39 := by
  have hII := hIIred hSpec
  refine ⟨(mtSpecific_at_repaired_parameters boxes E Δseed aSeed hB Total Kl κ packets hfrozen hZ
    hI hII hBV hSW hcond hHB).1, rfl, exact_gate⟩

/-- **Non-vacuity**: all hypotheses of `mtSpecificAsymptotic_concrete` are jointly satisfiable
(zero-error model); this inhabits nothing about the actual arithmetic errors. -/
theorem concrete_hypotheses_satisfiable :
    ZhengKloostermanInput (fun _ => 0) 0 ∧ SmoothTypeIInput concreteParams (fun _ _ => 0) (fun _ => 0) 0 ∧
    (∀ b, InTypeII concreteParams b →
      RestoredTypeIISpectralProvider (fun _ => 0) (fun _ => 0) (fun _ => 0) b.θ b.r b.s 0 0 0) ∧
    RestoredTypeIIInput concreteParams (fun _ _ => 0) (fun _ => 0) 0 ∅ ∧
    OrdinaryBVInput concreteParams (fun _ _ => 0) ∧ SiegelWalfiszSeedInput (fun _ _ _ => 0) ∧
    PacketCoprime ∅ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := providers_jointly_satisfiable concreteParams
  exact ⟨h1, h2, fun b _ => spectralProvider_zero _ _ _ _ _, h3, h4, h5, h6⟩

/-- **Firewall (b)**: the conditional asymptotic composition does not construct
`NumericalExternalConstants`; the bank's constants and `M_an` remain `none`. -/
theorem composition_does_not_construct_constants :
    ResearchBankV11.AnalyticActivation.AsymptoticCompositionHolds ∧
      ResearchBankV11.EffectiveConstants.currentConstants = none ∧
      ∀ A, ResearchBankV11.AnalyticActivation.current_M_an A = none :=
  ⟨ResearchBankV11.AnalyticActivation.asymptoticCompositionHolds_in_zero_model, rfl,
    ResearchBankV11.AnalyticActivation.current_M_an_eq_none⟩

end ConcreteAsymptoticGate
end ResearchBankV12
end Erdos287
