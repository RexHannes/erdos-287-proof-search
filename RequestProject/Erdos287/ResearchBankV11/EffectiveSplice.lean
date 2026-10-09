import RequestProject.Erdos287.ResearchBankV11.AnalyticActivation
import RequestProject.Erdos287.ResearchBankV11.FiniteArchitectureFrontier

/-!
# Erdős #287 — Research Bank V11 §U: the effective splice (BLOCKED)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The V9 finite-splice theorem (`ResearchBankV9.Splice.splice`) is re-used.  The refined input
bundle `EffectiveSpliceInput A` visibly requires

* an analytic threshold `M_an` **taken from the current bank** (`current_M_an A = some M_an`);
* a finite architecture **taken from the current bank** (`currentArchitecture = some arch`), which
  supplies the geometric threshold `M_geom` and, through its contract, localization, rigidity and
  prime supply;
* the interval/localization, rigidity and prime-supply thresholds `M_int`, `M_rig`, `M_prime`;
* a verified finite exclusion endpoint `U` with `M₀ = max(M_an, M_geom, M_int, M_rig, M_prime) ≤ U+1`.

Proved:
* `effectiveSplice_sound` — a complete input bundle closes Erdős #287 (so the bundle is the right
  contract);
* `splice_blocked_of_M_an_none` — if `M_an = none` the current effective splice is blocked;
* `splice_blocked_of_no_architecture` — if no finite architecture is recorded, it is blocked;
* `current_effective_splice_blocked` — the current bank has **no** effective splice input;
* `Erdos287ClosedInBank` (= a current effective splice input exists) is false; the asymptotic
  composition does not imply it, nor `FinitePrimeSupplyInBank`;
* fixture 8 (`fixture_analytic_vs_finite`): all asymptotic providers inhabited, finite
  architecture absent, #287 not closed by the bank.

No theorem here infers the full statement `Erdos287Closed` from the asymptotic result.
-/

namespace Erdos287
namespace ResearchBankV11
namespace EffectiveSplice

open AnalyticActivation FiniteArchitectureFrontier EffectiveConstants
  ResearchBankV10.FrozenFrontier ResearchBankV10.AsymptoticComposition ResearchBankV10.Providers

/-- **The refined effective-splice input bundle** (target log exponent `A`). -/
structure EffectiveSpliceInput (A : ℝ) where
  M_an : ℕ
  M_an_current : current_M_an A = some M_an
  arch : ArchitectureRecord
  arch_current : currentArchitecture = some arch
  M_int : ℕ
  M_rig : ℕ
  M_prime : ℕ
  U : ℕ
  finite : ResearchBankV9.Splice.FiniteVerifiedThrough U
  covers : max M_an (max arch.M_geom (max M_int (max M_rig M_prime))) ≤ U + 1

/-- **Soundness**: a complete bundle closes Erdős #287 (via the frozen V9 splice). -/
theorem effectiveSplice_sound {A : ℝ} (I : EffectiveSpliceInput A) : Erdos287Closed := by
  have hev := eventual_exclusion_of_architecture I.arch.provider
  have hle : I.arch.M_geom ≤ I.U + 1 :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) I.covers
  exact ResearchBankV9.Splice.splice I.finite hle hev

/-- **If `M_an = none`, the effective splice is blocked.** -/
theorem splice_blocked_of_M_an_none {A : ℝ} (h : current_M_an A = none) :
    IsEmpty (EffectiveSpliceInput A) :=
  ⟨fun I => by have := I.M_an_current; rw [h] at this; cases this⟩

/-- **If no finite architecture is recorded, the effective splice is blocked.** -/
theorem splice_blocked_of_no_architecture {A : ℝ} (h : currentArchitecture = none) :
    IsEmpty (EffectiveSpliceInput A) :=
  ⟨fun I => by have := I.arch_current; rw [h] at this; cases this⟩

/-- **The current effective splice is BLOCKED** (for every target exponent). -/
theorem current_effective_splice_blocked (A : ℝ) : IsEmpty (EffectiveSpliceInput A) :=
  splice_blocked_of_M_an_none (current_M_an_eq_none A)

/-- Closure *in the bank*: a current effective splice input exists. -/
def Erdos287ClosedInBank : Prop := ∃ A : ℝ, Nonempty (EffectiveSpliceInput A)

theorem erdos287ClosedInBank_false : ¬ Erdos287ClosedInBank :=
  fun ⟨A, ⟨I⟩⟩ => (current_effective_splice_blocked A).false I

/-- Finite prime supply in the bank: a recorded architecture (whose contract carries the prime
supply). -/
def FinitePrimeSupplyInBank : Prop := ∃ r, currentArchitecture = some r

theorem finitePrimeSupplyInBank_false : ¬ FinitePrimeSupplyInBank :=
  fun ⟨_, h⟩ => by cases h

/-- **The asymptotic composition does not imply closure in the bank.** -/
theorem asymptotic_does_not_imply_closed :
    ¬ (AsymptoticCompositionHolds → Erdos287ClosedInBank) :=
  fun h => erdos287ClosedInBank_false (h asymptoticCompositionHolds_in_zero_model)

/-- **The asymptotic composition does not imply finite prime supply.** -/
theorem asymptotic_does_not_imply_finitePrimeSupply :
    ¬ (AsymptoticCompositionHolds → FinitePrimeSupplyInBank) :=
  fun h => finitePrimeSupplyInBank_false (h asymptoticCompositionHolds_in_zero_model)

/-- **Fixture 8 (analytic vs finite)**: all asymptotic providers inhabited (zero-error model), no
finite architecture recorded, and the bank cannot close #287. -/
theorem fixture_analytic_vs_finite :
    AsymptoticCompositionHolds ∧
    (ZhengKloostermanInput (fun _ => 0) 0 ∧
      SmoothTypeIInput repairedParams (fun _ _ => 0) (fun _ => 0) 0 ∧
      RestoredTypeIIInput repairedParams (fun _ _ => 0) (fun _ => 0) 0 ∅ ∧
      OrdinaryBVInput repairedParams (fun _ _ => 0) ∧
      SiegelWalfiszSeedInput (fun _ _ _ => 0)) ∧
    currentArchitecture = none ∧ ¬ Erdos287ClosedInBank := by
  obtain ⟨h, -, -⟩ := fixture_asymptotic_vs_effective
  exact ⟨asymptoticCompositionHolds_in_zero_model, h, rfl, erdos287ClosedInBank_false⟩

end EffectiveSplice
end ResearchBankV11
end Erdos287
