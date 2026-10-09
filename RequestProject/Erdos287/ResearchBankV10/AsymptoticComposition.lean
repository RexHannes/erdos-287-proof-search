import RequestProject.Erdos287.ResearchBankV10.FrozenFrontier
import RequestProject.Erdos287.ResearchBankV10.TypeIProvider
import RequestProject.Erdos287.ResearchBankV10.TypeIIHighLow
import RequestProject.Erdos287.ResearchBankV10.WellFactorableCutoff
import RequestProject.Erdos287.ResearchBankV10.ExponentGate

/-!
# Erdős #287 — Research Bank V10 §O: the final asymptotic composition (conditional)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`mtSpecificAsymptotic_of_repairedProviders` is a machine-checked **implication** whose assumptions
are all visible:

* the frozen V9 bank (`FrozenV9Bank`);
* the explicit spectral input (`ZhengKloostermanInput`);
* the smooth Type-I provider (`SmoothTypeIInput`), the restored Type-II spectral provider
  (`RestoredTypeIIInput`), the ordinary BV provider (`OrdinaryBVInput`), the rough-seed SW
  provider (`SiegelWalfiszSeedInput`);
* the conductor/root/base hypotheses (`PacketCoprime`) on the Type-II packets;
* the HB support data: a finite set of support boxes and the HB decomposition bound
  (`HBDecompositionBound`: `|Total(X)| ≤ ∑_boxes |E_b(X)| + seed aggregate`).

Its conclusion is `MTSpecificAsymptotic P Total` — the log-power saving of the pair-distribution
error at level `λ = 7/13 − 3θ₀ − ε₀` — together with the exact level/gate equivalence
`78/145 < λ ⟺ 3θ₀ + ε₀ < 1/1885` (taken from the frozen V9 margin).

Inside the proof, the kernel-proved finite inputs are consumed: the routing theorem
(`every_box_routed`, which uses the proved HB trichotomy), the Type-I combinatorics
(`typeICombinatorialFacts_holds`), the compatible-cell count (`compatibleCellFacts_holds`), the
reciprocal phases (`reciprocalPhaseFacts_of_coprime`) and the elementary seed aggregation
(`seed_aggregate_of_SW`).

`mtSpecific_at_repaired_parameters` specializes to `θ₀ = 1/25000 + 1/625000000`, `ε₀ = 1/100000`,
where the gate passes exactly (`λ > 78/145`, `145/39 − 2/λ = 52426455/18953756081`).

**This theorem is not named `erdos287`/`closed`; it proves no statement about #287 itself.**
-/

namespace Erdos287
namespace ResearchBankV10
namespace AsymptoticComposition

open HBSupportCoverage Providers FrozenFrontier TypeIICoefficient

/-- The MT-bridge target: log-power saving of the pair-distribution error at level `P.lam`. -/
def MTSpecificAsymptotic (_P : CoverageParams) (Total : ℝ → ℝ) : Prop := LogPowerSaving Total

/-- The HB decomposition bound (HB support data). -/
def HBDecompositionBound (boxes : Finset SupportBox) (E : SupportBox → ℝ → ℝ)
    (Δseed : ℕ → ℤ → ℝ → ℝ) (aSeed : ℕ → ℤ) (B : ℝ) (Total : ℝ → ℝ) : Prop :=
  ∀ X : ℝ, |Total X| ≤ ∑ b ∈ boxes, |E b X| + seedAggregate Δseed aSeed B X

theorem logPowerSaving_abs {f : ℝ → ℝ} (hf : LogPowerSaving f) :
    LogPowerSaving (fun X => |f X|) := by
  intro A hA
  obtain ⟨C, X₀, h⟩ := hf A hA
  exact ⟨C, X₀, fun X hX => by rw [abs_abs]; exact h X hX⟩

theorem logPowerSaving_of_abs_le {f g : ℝ → ℝ} (hg : LogPowerSaving g)
    (hfg : ∀ X, |f X| ≤ g X) : LogPowerSaving f := by
  intro A hA
  obtain ⟨C, X₀, h⟩ := hg A hA
  exact ⟨C, X₀, fun X hX => (hfg X).trans ((le_abs_self _).trans (h X hX))⟩

/-- **The level/gate equivalence** from the frozen V9 margin `7/13 − 78/145 = 1/1885`. -/
theorem level_gate_iff (hfrozen : FrozenV9Bank) (P : CoverageParams) :
    78 / 145 < P.lam ↔ 3 * P.θ₀ + P.ε₀ < 1 / 1885 := by
  have h := hfrozen.1
  unfold CoverageParams.lam
  constructor <;> intro h' <;> linarith

/-- **The final asymptotic composition** (conditional on visible providers). -/
theorem mtSpecificAsymptotic_of_repairedProviders
    (P : CoverageParams) (boxes : Finset SupportBox) (E : SupportBox → ℝ → ℝ)
    (Δseed : ℕ → ℤ → ℝ → ℝ) (aSeed : ℕ → ℤ) {B : ℝ} (hB : 0 ≤ B) (Total : ℝ → ℝ)
    (Kl : ℕ → ℝ) (κ : ℝ) (packets : Finset CoeffVars)
    (hfrozen : FrozenV9Bank)
    (hZ : ZhengKloostermanInput Kl κ)
    (hI : SmoothTypeIInput P E Kl κ)
    (hII : RestoredTypeIIInput P E Kl κ packets)
    (hBV : OrdinaryBVInput P E)
    (hSW : SiegelWalfiszSeedInput Δseed)
    (hcond : PacketCoprime packets)
    (hHB : HBDecompositionBound boxes E Δseed aSeed B Total) :
    MTSpecificAsymptotic P Total ∧ (78 / 145 < P.lam ↔ 3 * P.θ₀ + P.ε₀ < 1 / 1885) := by
  refine ⟨?_, level_gate_iff hfrozen P⟩
  have hbox : ∀ b ∈ boxes, LogPowerSaving (fun X => |E b X|) := by
    intro b _
    apply logPowerSaving_abs
    rcases every_box_routed P b with h | h | h
    · exact hBV.bound b h
    · exact hI.reduction hZ typeICombinatorialFacts_holds b h
    · exact hII.reduction hZ compatibleCellFacts_holds (reciprocalPhaseFacts_of_coprime hcond) b h
  have hsum := logPowerSaving_sum boxes (fun b X => |E b X|) hbox
  have hseed := seed_aggregate_of_SW hSW aSeed hB
  exact logPowerSaving_of_abs_le (logPowerSaving_add hsum hseed) hHB

/-- The repaired parameters `θ₀ = 1/25000 + 1/625000000`, `ε₀ = 1/100000`. -/
def repairedParams : CoverageParams where
  θ₀ := ExponentGate.theta0
  ε₀ := ExponentGate.eps0
  θ₀_nonneg := ExponentGate.theta0_pos.le
  θ₀_le := ExponentGate.theta0_lt.le
  ε₀_pos := ExponentGate.eps0_pos
  ε₀_le := ExponentGate.eps0_le

theorem repairedParams_lam : repairedParams.lam = ExponentGate.vartheta := rfl

/-- **Specialization at the repaired parameters**: the same conditional conclusion, now with the
exact gate pass `λ > 78/145` and the exact pair-coefficient gap. -/
theorem mtSpecific_at_repaired_parameters (boxes : Finset SupportBox)
    (E : SupportBox → ℝ → ℝ) (Δseed : ℕ → ℤ → ℝ → ℝ) (aSeed : ℕ → ℤ) {B : ℝ} (hB : 0 ≤ B)
    (Total : ℝ → ℝ) (Kl : ℕ → ℝ) (κ : ℝ) (packets : Finset CoeffVars)
    (hfrozen : FrozenV9Bank)
    (hZ : ZhengKloostermanInput Kl κ)
    (hI : SmoothTypeIInput repairedParams E Kl κ)
    (hII : RestoredTypeIIInput repairedParams E Kl κ packets)
    (hBV : OrdinaryBVInput repairedParams E)
    (hSW : SiegelWalfiszSeedInput Δseed)
    (hcond : PacketCoprime packets)
    (hHB : HBDecompositionBound boxes E Δseed aSeed B Total) :
    MTSpecificAsymptotic repairedParams Total ∧ 78 / 145 < repairedParams.lam ∧
      145 / 39 - 2 / repairedParams.lam = 52426455 / 18953756081 := by
  refine ⟨(mtSpecificAsymptotic_of_repairedProviders repairedParams boxes E Δseed aSeed hB Total
    Kl κ packets hfrozen hZ hI hII hBV hSW hcond hHB).1, ?_, ?_⟩
  · exact ExponentGate.vartheta_gt_gate
  · exact ExponentGate.pair_coefficient_gap.1

/-! ## The providers are jointly satisfiable (so the composition is not vacuous) -/

/-- All asymptotic providers are simultaneously inhabited in the zero-error model; hence the
hypotheses of the composition theorem are satisfiable (it is not vacuously true).  This inhabits
nothing about the actual prime-counting errors. -/
theorem providers_jointly_satisfiable (P : CoverageParams) :
    ZhengKloostermanInput (fun _ => 0) 0 ∧ SmoothTypeIInput P (fun _ _ => 0) (fun _ => 0) 0 ∧
    RestoredTypeIIInput P (fun _ _ => 0) (fun _ => 0) 0 ∅ ∧ OrdinaryBVInput P (fun _ _ => 0) ∧
    SiegelWalfiszSeedInput (fun _ _ _ => 0) ∧ PacketCoprime ∅ ∧
    HBDecompositionBound ∅ (fun _ _ => 0) (fun _ _ _ => 0) (fun _ => 0) 0 (fun _ => 0) := by
  refine ⟨zheng_zero 0, typeI_zero P _ 0, typeII_zero P _ 0 ∅, ordinaryBV_zero P,
    ⟨RoughSeedIdentities.roughSeedSW_zero⟩, fun x hx => absurd hx (Finset.notMem_empty x), ?_⟩
  intro X
  simp [seedAggregate]

/-- **Firewall: the composition says nothing about any counterexample predicate.**  Its
hypotheses are jointly satisfiable and do not mention counterexamples, so they cannot imply that
an *arbitrary* predicate on finite sets is empty. -/
theorem composition_does_not_constrain_counterexamples :
    ¬ ∀ bad : Finset ℕ → Prop,
      (∃ P : CoverageParams, ∃ Total : ℝ → ℝ, MTSpecificAsymptotic P Total) →
        ∀ A, ¬ bad A := by
  intro h
  exact h (fun _ => True) ⟨repairedParams, fun _ => 0, logPowerSaving_zero⟩ ∅ trivial

end AsymptoticComposition
end ResearchBankV10
end Erdos287
