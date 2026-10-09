import RequestProject.Erdos287.ResearchBankV11.EffectiveConstants
import RequestProject.Erdos287.ResearchBankV11.PowerToLog
import RequestProject.Erdos287.ResearchBankV11.ExceptionalFactor
import RequestProject.Erdos287.ResearchBankV10.AsymptoticComposition

/-!
# Erdős #287 — Research Bank V11 §R: effective `M_an` and the activation firewall

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* `analyticActivation c A : Option ℕ` — for a numerical constant bundle `c` and a target log
  exponent `A`, the threshold `⌈exp(T)⌉` where `T` is the maximum of the explicit power-to-log
  thresholds of the six power terms (and `1`);
* `analyticActivation_sufficient` — **the computed threshold is sufficient**: for `0 < A ≤ A₀` and
  `X ≥ M`, `symbolicError c X ≤ (K_log + 6) · X · (log X)^{-A}`;
* `current_M_an A = currentConstants.bind (analyticActivation · A)`, and **`current_M_an_eq_none`**:
  no numerical `M_an` is available (no constant bundle is instantiated; no fake number is
  hard-coded);
* `effective_composition` — the effective error bound, which **requires** the
  exceptional-safe full-modulus input (`ExceptionalModulusInput`);
* status firewall: `EffectiveActivation` is false in the current bank and needs numerical
  constants (`effectiveActivation_needs_constants`); the asymptotic composition does **not** imply
  it (`asymptotic_does_not_imply_effective`); fixture 7 (`fixture_asymptotic_vs_effective`): all
  asymptotic providers inhabited, numerical constants absent, `M_an` still `none`.
-/

namespace Erdos287
namespace ResearchBankV11
namespace AnalyticActivation

open EffectiveConstants PowerToLog ExceptionalFactor ResearchBankV10.AsymptoticComposition
  ResearchBankV10.Providers ResearchBankV10.HBSupportCoverage

theorem le_foldr_max_real (b : ℝ) : ∀ (l : List ℝ), ∀ x ∈ l, x ≤ l.foldr max b
  | [], _, h => by simp at h
  | a :: l, x, h => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (le_foldr_max_real b l x h).trans (le_max_right _ _)

theorem base_le_foldr_max (b : ℝ) : ∀ (l : List ℝ), b ≤ l.foldr max b
  | [] => le_rfl
  | _ :: l => (base_le_foldr_max b l).trans (le_max_right _ _)

theorem sum_map_le {α : Type*} (f : α → ℝ) (B : ℝ) :
    ∀ l : List α, (∀ x ∈ l, f x ≤ B) → (l.map f).sum ≤ l.length * B
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := sum_map_le f B l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have ha := h a List.mem_cons_self
    push_cast; linarith

/-- The log degree `n = ⌈C + A + 1⌉`. -/
noncomputable def logDegree (c : NumericalExternalConstants) (A : ℝ) : ℕ := ⌈c.C + A + 1⌉₊

/-- The log threshold `T = max(1, max_i K_i n!/η_i^n)`. -/
noncomputable def logThreshold (c : NumericalExternalConstants) (A : ℝ) : ℝ :=
  (c.powerTerms.map fun Kη => powerToLogThreshold Kη.1 Kη.2 (logDegree c A)).foldr max 1

/-- **The analytic activation threshold** of a numerical constant bundle. -/
noncomputable def analyticActivation (c : NumericalExternalConstants) (A : ℝ) : Option ℕ :=
  some ⌈Real.exp (logThreshold c A)⌉₊

/-- **The computed threshold is sufficient.** -/
theorem analyticActivation_sufficient (c : NumericalExternalConstants) {A : ℝ} (hA : 0 < A)
    (hAA₀ : A ≤ c.A₀) {M : ℕ} (hM : analyticActivation c A = some M) {X : ℝ} (hX : (M : ℝ) ≤ X) :
    c.symbolicError X ≤ (c.K_log + 6) * X * Real.log X ^ (-A) := by
  simp only [analyticActivation, Option.some.injEq] at hM
  set T := logThreshold c A
  have hT1 : 1 ≤ T := base_le_foldr_max 1 _
  have hexpX : Real.exp T ≤ X := le_trans (Nat.le_ceil _) (hM ▸ hX)
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos T) hexpX
  have hlogT : T ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]; exact hexpX
  have hlog1 : 1 ≤ Real.log X := hT1.trans hlogT
  have hn : c.C + A + 1 ≤ (logDegree c A : ℝ) := Nat.le_ceil _
  -- power terms
  have hterm : ∀ Kη ∈ c.powerTerms,
      Kη.1 * X ^ (1 - Kη.2) * Real.log X ^ c.C ≤ X * Real.log X ^ (-A) := by
    intro Kη hKη
    obtain ⟨hK, hη⟩ := c.powerTerms_pos Kη hKη
    refine power_to_log_of_threshold hK hη hA c.C_nonneg hn hX0 (le_trans ?_ hlogT)
    exact le_foldr_max_real 1 _ _ (List.mem_map.2 ⟨Kη, hKη, rfl⟩)
  have hsum := sum_map_le (fun Kη : ℝ × ℝ => Kη.1 * X ^ (1 - Kη.2) * Real.log X ^ c.C)
    (X * Real.log X ^ (-A)) c.powerTerms hterm
  rw [c.powerTerms_length] at hsum
  -- log term
  have hlogterm : c.K_log * X * Real.log X ^ (-c.A₀) ≤ c.K_log * X * Real.log X ^ (-A) := by
    have hKl := c.K_pos.2.2.2.2.2.2
    have h1 := Real.rpow_le_rpow_of_exponent_le hlog1 (show -c.A₀ ≤ -A by linarith)
    have hXK : 0 ≤ c.K_log * X := by positivity
    exact mul_le_mul_of_nonneg_left h1 hXK
  unfold NumericalExternalConstants.symbolicError
  push_cast at hsum
  linarith

/-- **The current `M_an`**: computed from the current constants (of which there are none). -/
noncomputable def current_M_an (A : ℝ) : Option ℕ :=
  currentConstants.bind fun c => analyticActivation c A

/-- **No numerical `M_an` is available in the current bank.** -/
theorem current_M_an_eq_none (A : ℝ) : current_M_an A = none := rfl

/-! ## Effective composition requires the exceptional-safe full modulus -/

/-- **External effective provider bundle**: once the full moduli are exceptional-safe, the total
error is bounded by the symbolic error with the numerical constants `c`. -/
structure EffectiveProviderBundle (c : NumericalExternalConstants) (pExc : Option ℕ) (Sep : Prop)
    (Q : Finset ℕ) (Total : ℝ → ℝ) : Prop where
  rep : ExceptionalModulusInput pExc Sep Q → ∀ X : ℝ, 2 ≤ X → |Total X| ≤ c.symbolicError X

/-- **Effective composition** (depends on `ExceptionalModulusInput`). -/
theorem effective_composition (c : NumericalExternalConstants) {A : ℝ} (hA : 0 < A)
    (hAA₀ : A ≤ c.A₀) {M : ℕ} (hM : analyticActivation c A = some M) {pExc : Option ℕ}
    {Sep : Prop} {Q : Finset ℕ} {Total : ℝ → ℝ} (hB : EffectiveProviderBundle c pExc Sep Q Total)
    (hexc : ExceptionalModulusInput pExc Sep Q) :
    ∀ X : ℝ, max (M : ℝ) 2 ≤ X → |Total X| ≤ (c.K_log + 6) * X * Real.log X ^ (-A) :=
  fun X hX => (hB.rep hexc X (le_of_max_le_right hX)).trans
    (analyticActivation_sufficient c hA hAA₀ hM (le_of_max_le_left hX))

/-! ## Status firewall -/

/-- Effective activation in the current bank: some `M_an` is available. -/
def EffectiveActivation : Prop := ∃ A : ℝ, ∃ M : ℕ, current_M_an A = some M

/-- **`EffectiveActivation` does not exist without numerical constants.** -/
theorem effectiveActivation_needs_constants :
    EffectiveActivation → ∃ c : NumericalExternalConstants, currentConstants = some c := by
  rintro ⟨A, M, h⟩
  simp [current_M_an, currentConstants] at h

theorem effectiveActivation_false : ¬ EffectiveActivation := by
  rintro ⟨A, M, h⟩
  rw [current_M_an_eq_none] at h
  cases h

/-- The asymptotic composition, as a proposition. -/
def AsymptoticCompositionHolds : Prop :=
  ∃ P : CoverageParams, ∃ Total : ℝ → ℝ, MTSpecificAsymptotic P Total

theorem asymptoticCompositionHolds_in_zero_model : AsymptoticCompositionHolds :=
  ⟨repairedParams, fun _ => 0, logPowerSaving_zero⟩

/-- **The asymptotic composition does NOT imply effective activation.** -/
theorem asymptotic_does_not_imply_effective :
    ¬ (AsymptoticCompositionHolds → EffectiveActivation) :=
  fun h => effectiveActivation_false (h asymptoticCompositionHolds_in_zero_model)

/-- **Fixture 7 (asymptotic vs effective)**: all asymptotic providers are inhabited (zero-error
model), the numerical constants are absent, and `M_an` remains `none`. -/
theorem fixture_asymptotic_vs_effective :
    (ZhengKloostermanInput (fun _ => 0) 0 ∧
      SmoothTypeIInput repairedParams (fun _ _ => 0) (fun _ => 0) 0 ∧
      RestoredTypeIIInput repairedParams (fun _ _ => 0) (fun _ => 0) 0 ∅ ∧
      OrdinaryBVInput repairedParams (fun _ _ => 0) ∧
      SiegelWalfiszSeedInput (fun _ _ _ => 0)) ∧
    currentConstants = none ∧ ∀ A, current_M_an A = none := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := providers_jointly_satisfiable repairedParams
  exact ⟨⟨h1, h2, h3, h4, h5⟩, rfl, current_M_an_eq_none⟩

end AnalyticActivation
end ResearchBankV11
end Erdos287
