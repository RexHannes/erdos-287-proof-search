import RequestProject.Erdos287.ResearchBankV24.FinalFirewalls
import RequestProject.Erdos287.ResearchBankV25.Ledger
import RequestProject.Erdos287.ResearchBankV25.Counterfixtures
import RequestProject.Erdos287.ResearchBankV27.OuterInnerSeparation
import RequestProject.Erdos287.ResearchBankV27.CRTColourOrbit
import RequestProject.Erdos287.ResearchBankV27.DISpectralProvider

/-!
# Erdős #287 — Research Bank V28 §14–15: effectivity and historical-overclaim firewalls

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

## §14 Effectivity ledger (OPEN items, recorded as data)

`EffectivityItem` lists `noExplicitM0Yet`, `finiteSpliceOpen`, `exceptionalZeroEffectivityOpen`;
every item has status `OPEN` (`effectivity_all_open`).  The pre-effectivity theorem is an
`∃ M₀` statement that may rest on ineffective analytic constants; it is never converted into a
computable `M₀`.

## §15 Historical overclaim firewalls (FINITE REGRESSION / LEAN BANK)

1. `fw1_small_cost_not_SW` — a fixed-modulus discrepancy of size `1` (small cost) coexists with
   failure of the balance (SW-type) statement;
2. `fw2_residue_restriction_not_SW` — residue restriction does not preserve global balance;
3. `fw3_raw_density_ne_weighted` — raw density `≠` conditioned weighted density;
4. `fw4_support_not_coefficient_factorization` — product support does not force a product
   coefficient;
5. `fw5_no_kloosterman_decoration` — a decoration depending on a final Kloosterman variable is not
   an inner decoration;
6. `fw6_labels_cost_sqrt` — separate labels cost `√L` (not `L`) on the linear sum via the common
   Cauchy; `√2 < 2`;
7. `fw7_character_free_not_DI` — the character-free colour route does not prove DI: the DI
   conclusion fails for some admissible form;
8. `fw8_finite_verifier_not_spectral` — no finite check yields the spectral provider: the
   unrestricted provider is false although it holds vacuously on the empty list;
9. `fw9_asymptotic_not_explicit` — `∃ M₀` does not give an explicit `M₀`;
10. `fw10_explicit_needs_splice` — even an explicit `M₀` needs the finite splice for global #287.
-/

namespace Erdos287
namespace ResearchBankV28
namespace EffectivityFirewall

open ResearchBankV25.Ledger

/-- The open effectivity items. -/
inductive EffectivityItem
  | noExplicitM0Yet
  | finiteSpliceOpen
  | exceptionalZeroEffectivityOpen
  deriving DecidableEq, Repr

open EffectivityItem

/-- Status of the effectivity items. -/
def effectivityStatus : EffectivityItem → StatusClass
  | noExplicitM0Yet => .openProblem
  | finiteSpliceOpen => .openProblem
  | exceptionalZeroEffectivityOpen => .openProblem

theorem effectivity_all_open : ∀ i, effectivityStatus i = .openProblem := by
  intro i; cases i <;> rfl

/-- `NoExplicitM0Yet`: an `∃ M₀` statement never fixes a numerical bound (LEAN BANK). -/
def NoExplicitM0Yet : Prop :=
  ∀ B : ℕ, ∃ Q : ℕ → Prop, (∃ M₀ : ℕ, ∀ M ≥ M₀, Q M) ∧ ¬ ∀ M ≥ B, Q M

theorem noExplicitM0Yet_holds : NoExplicitM0Yet :=
  ResearchBankV24.FinalFirewalls.fw8_conditional_asymptotic_no_explicit_M0

/-- `FiniteSpliceOpen`: asymptotic + a bounded range check does not give all `M` (LEAN BANK). -/
def FiniteSpliceOpen : Prop :=
  ∀ U : ℕ, ¬ ∀ bad : ℕ → Prop, (∃ M₀, ∀ M ≥ M₀, ¬ bad M) → (∀ M ≤ U, ¬ bad M) → ∀ M, ¬ bad M

theorem finiteSpliceOpen_holds : FiniteSpliceOpen :=
  ResearchBankV24.FinalFirewalls.fw9_explicit_M0_required_for_splice

/-- `ExceptionalZeroEffectivityOpen`: recorded as an OPEN ledger item (no mathematical content is
claimed; the exceptional-zero effectivity programme is separate). -/
def ExceptionalZeroEffectivityOpen : Prop :=
  effectivityStatus exceptionalZeroEffectivityOpen = .openProblem

theorem exceptionalZeroEffectivityOpen_recorded : ExceptionalZeroEffectivityOpen := rfl

/-- 1. Small fixed-modulus cost does NOT imply an unchanged SW contract. -/
theorem fw1_small_cost_not_SW :
    ResearchBankV25.FixedResidueEnergy.Disc 3 (Finset.Icc 1 6)
        (ResearchBankV25.FixedResidueEnergy.alphaLoc (f := 3) (fun _ => 1) 1)
        ((1 : (ZMod 3)ˣ) : ZMod 3) = 1 ∧
      ¬ ResearchBankV25.Counterfixtures.Balanced 3 (Finset.Icc 1 6)
        (ResearchBankV25.FixedResidueEnergy.alphaLoc (f := 3) (fun _ => 1) 1) :=
  ⟨ResearchBankV25.Counterfixtures.restricted_sequence_unbalanced,
    ResearchBankV25.Counterfixtures.residue_restriction_breaks_SW.2⟩

/-- 2. Residue restriction does NOT preserve global SW automatically. -/
theorem fw2_residue_restriction_not_SW :
    ResearchBankV25.Counterfixtures.Balanced 3 (Finset.Icc 1 6) (fun _ => 1) ∧
      ¬ ResearchBankV25.Counterfixtures.Balanced 3 (Finset.Icc 1 6)
        (ResearchBankV25.FixedResidueEnergy.alphaLoc (f := 3) (fun _ => 1) 1) :=
  ResearchBankV25.Counterfixtures.residue_restriction_breaks_SW

/-- 3. Raw density does NOT equal the conditioned weighted density. -/
theorem fw3_raw_density_ne_weighted :
    ResearchBankV21.DensityCounterfixture.weightedDensity ≠
      ResearchBankV21.DensityCounterfixture.rawDensity :=
  ResearchBankV24.FinalFirewalls.fw1_spectator_square_not_raw_density.2.2

/-- 4. Support factorization does NOT imply coefficient factorization. -/
theorem fw4_support_not_coefficient_factorization :
    ¬ ∃ a b : ℤ → ℂ, ∀ v h, (if v = h then (1 : ℂ) else 0) = a v * b h :=
  ResearchBankV27.OuterInnerSeparation.joint_dependence_allowed.2

/-- 5. Arbitrary bounded decorations may NOT depend on the final Kloosterman variables. -/
theorem fw5_no_kloosterman_decoration :
    ∃ Φ : (ℤ × ℤ) × Bool → ℂ, ∀ Ψ : ResearchBankV27.OuterInnerSeparation.InnerCoeff,
      ∃ i b, Φ (i, b) ≠ Ψ i :=
  ResearchBankV27.OuterInnerSeparation.decoration_firewall

/-- 6. Separate colour labels cost `√L` (not `L`) with the common Cauchy. -/
theorem fw6_labels_cost_sqrt {O I J : Type*} [Fintype O] [Fintype I] [Fintype J]
    (A : O → ℂ) (w : O → ℝ) (hA : ∀ o, ‖A o‖ ^ 2 ≤ w o) (K : O → I → ℂ) (Ψ : J → I → ℂ)
    (κ : O → J) {B : ℝ} (hB : 0 ≤ B)
    (hsingle : ∀ j, (∑ o, w o) * ResearchBankV27.CommonCauchy.energy K (Ψ j) ≤ B ^ 2) :
    ‖ResearchBankV27.FiniteLabelEnergy.labelSum A K Ψ κ‖ ≤ Real.sqrt (Fintype.card J) * B ∧
      Real.sqrt 2 < 2 := by
  refine ⟨ResearchBankV27.FiniteLabelEnergy.labelled_sqrt_cost A w hA K Ψ κ hB hsingle, ?_⟩
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- 7. The character-free route does NOT prove DI itself. -/
theorem fw7_character_free_not_DI :
    ¬ ∀ K : ResearchBankV27.DISpectral.KloostermanData, ResearchBankV27.DISpectral.DIConclusion K :=
  ResearchBankV27.DISpectral.DI_not_automatic

/-- 8. A finite verifier does NOT prove the spectral theorem. -/
theorem fw8_finite_verifier_not_spectral (η : ℝ) :
    (∀ K ∈ ([] : List ResearchBankV27.DISpectral.KloostermanData),
        ResearchBankV27.DISpectral.DIConclusion K) ∧
      ¬ ResearchBankV27.DISpectral.DISpectralProvider η (fun _ => True) :=
  ⟨fun _ h => absurd h List.not_mem_nil, ResearchBankV27.DISpectral.unrestricted_provider_false η⟩

/-- 9. An asymptotic `M₀` does NOT imply an explicit `M₀`. -/
theorem fw9_asymptotic_not_explicit : NoExplicitM0Yet := noExplicitM0Yet_holds

/-- 10. Even an explicit asymptotic `M₀` still requires the finite splice for global #287. -/
theorem fw10_explicit_needs_splice : FiniteSpliceOpen := finiteSpliceOpen_holds

end EffectivityFirewall
end ResearchBankV28
end Erdos287
