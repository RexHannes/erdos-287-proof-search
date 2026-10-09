import RequestProject.Erdos287.ResearchBankV20.NoEffectivization
import RequestProject.Erdos287.ResearchBankV19.NegativeControls
import RequestProject.Erdos287.ResearchBankV17.ThinSupportLedger

/-!
# Erdős #287 — Research Bank V20 §3: required non-implications

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Machine-checked countermodels:

1. `omega_zero_not_compatibility` — `Ω(0) = 1` does NOT imply the zero-mode count is `1`.
2. `residue_restriction_breaks_balance` — a one-bounded residue restriction does NOT preserve a
   (toy, mod-2) Siegel–Walfisz-type balance: the constant sequence `1` is balanced, its
   restriction to even `n` is not.
3. `support_below_threshold_no_provider` — support exponent `< 3/5` does NOT construct the prime
   provider.
4. `local_transport_not_branch_match` — local transport bounds hold for a branch list for which
   the composition provider fails (a joint-dependence branch).
5. `local_margins_not_global_control` — the positive local E1/E2 margins coexist with a branch
   list whose outer conductor/root sum is NOT globally controlled.
6. `finite_verifier_not_analytic` — an error function vanishing on the whole finite range
   `x ≤ 100` still violates the analytic prime-distribution provider.
7. `conditional_asymptotic_no_explicit_M0` — an eventual conclusion gives no explicit `M₀`.
8. `explicit_M0_required_for_splice` — without an explicit threshold the splice fails.

`v20_scope_firewalls` bundles all eight.
-/

namespace Erdos287
namespace ResearchBankV20
namespace ScopeFirewalls

open ResearchBankV19 ResearchBankV19.BranchData
open ResearchBankV19.ActualCenteredCompositionProvider
open ResearchBankV17.ThinSupportLedger

/-- 1. `Ω(0) = 1` does NOT imply zero-mode compatibility (count `1`). -/
theorem omega_zero_not_compatibility :
    ¬ ∀ (q₁ q₂ : ℕ) (n₁ n₂ a₁ a₂ Δ : ℤ),
      ResearchBankV18.ColourConductor.e (Nat.lcm q₁ q₂) (0 * Δ) = 1 →
        (ZeroFrequencyCompatibility.solutions q₁ q₂ n₁ n₂ a₁ a₂).card = 1 :=
  ZeroFrequencyCompatibility.omega_zero_does_not_fix_main_term

/-- Toy mod-2 Siegel–Walfisz balance: even and odd partial sums agree on every even prefix
(up to `1`). -/
def BalancedMod2 (a : ℕ → ℝ) : Prop :=
  ∀ x : ℕ, |∑ n ∈ Finset.range (2 * x), (-1 : ℝ) ^ n * a n| ≤ 1

theorem const_one_balanced : BalancedMod2 (fun _ => 1) := by
  intro x
  have : ∑ n ∈ Finset.range (2 * x), (-1 : ℝ) ^ n * 1 = 0 := by
    induction x with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, ih, pow_succ, pow_mul]
      norm_num
  rw [this]; norm_num

/-- 2. A one-bounded residue restriction does NOT preserve the balance. -/
theorem residue_restriction_breaks_balance :
    ∃ (a c : ℕ → ℝ), (∀ n, |c n| ≤ 1) ∧ BalancedMod2 a ∧ ¬ BalancedMod2 (fun n => c n * a n) := by
  refine ⟨fun _ => 1, fun n => if n % 2 = 0 then 1 else 0, fun n => ?_, const_one_balanced,
    fun h => ?_⟩
  · show |(if n % 2 = 0 then (1 : ℝ) else 0)| ≤ 1
    split_ifs <;> norm_num
  · have := h 2
    simp [Finset.sum_range_succ] at this
    norm_num at this

/-- 3. Support exponent below `3/5` does NOT construct the prime provider. -/
theorem support_below_threshold_no_provider :
    ¬ ((273 / 500 : ℚ) < 3 / 5 → ∀ err : ℝ → ℝ, PrimeDistributionProvider (273 / 500) err) :=
  level_below_threshold_does_not_construct_provider (by norm_num)

/-- 4. Local transport bounds do NOT imply that all actual branches match. -/
theorem local_transport_not_branch_match :
    ∃ bs : List ActualBranchData, LocalTransportBounds bs ∧
      ∀ (N : ℕ → ℝ) (c : ℝ), ¬ ActualCenteredSourceCompositionProvider bs N c :=
  ⟨[jointSample], ⟨fun b hb M => by simp at hb; subst hb; simp [jointSample]⟩,
    provider_falsifiable⟩

/-- An in-scope branch with uncontrolled (linearly growing) outer weight. -/
def growingOuter : ActualBranchData :=
  { jointSample with e2Dependency := .outerOnly, outerWeight := fun M => M }

/-- 5. Positive local E1/E2 margins do NOT imply global outer control. -/
theorem local_margins_not_global_control :
    (0 < OuterCostLedger.conservativeExponent (1 / 1000) (1 / 40000) 1 ∧
      0 < OuterCostLedger.conservativeExponent (1 / 1000) (1 / 40000) (2 / 3)) ∧
    ¬ (∀ η > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀,
        ([growingOuter].map fun b => b.outerWeight M).sum ≤ η * (fun _ => (1 : ℝ)) M) := by
  refine ⟨⟨by rw [OuterCostLedger.E1_margin.1]; norm_num,
    by rw [OuterCostLedger.E2_margin.1]; norm_num⟩, fun h => ?_⟩
  obtain ⟨M₀, hM⟩ := h 1 one_pos
  have := hM (M₀ + 2) (by omega)
  simp [growingOuter] at this
  linarith

/-- The finite-verifier error model: zero on `x ≤ 100`, linear beyond. -/
noncomputable def finiteErr (x : ℝ) : ℝ := if x ≤ 100 then 0 else 2 * x

/-- 6. A finite verifier does NOT imply the analytic prime-distribution provider. -/
theorem finite_verifier_not_analytic (θ : ℚ) :
    (∀ x : ℝ, x ≤ 100 → finiteErr x = 0) ∧ ¬ PrimeDistributionProvider θ finiteErr := by
  refine ⟨fun x hx => by simp [finiteErr, hx], fun h => ?_⟩
  obtain ⟨x₀, hx⟩ := h.saving 0
  have h1 := hx (max x₀ 101) (le_max_left _ _)
  have h2 : (101 : ℝ) ≤ max x₀ 101 := le_max_right _ _
  have h3 : ¬ max x₀ 101 ≤ 100 := by linarith
  simp only [finiteErr, h3, if_false, pow_zero, div_one] at h1
  rw [abs_of_pos (by linarith)] at h1
  linarith

/-- 7. The conditional asymptotic theorem does NOT imply an explicit `M₀`. -/
theorem conditional_asymptotic_no_explicit_M0 (B : ℕ) :
    ∃ Q : ℕ → Prop, (∃ M₀ : ℕ, ∀ M ≥ M₀, Q M) ∧ ¬ ∀ M ≥ B, Q M :=
  NoEffectivization.conditional_asymptotic_gives_no_explicit_M0 B

/-- 8. An explicit `M₀` is required before the finite splice can close #287. -/
theorem explicit_M0_required_for_splice (U : ℕ) :
    ¬ ∀ bad : ℕ → Prop, (∃ M₀, ∀ M ≥ M₀, ¬ bad M) → (∀ M ≤ U, ¬ bad M) → ∀ M, ¬ bad M :=
  (NoEffectivization.splice_needs_explicit_M0 U).2

/-- **All eight V20 non-implications.** -/
theorem v20_scope_firewalls :
    (¬ ∀ (q₁ q₂ : ℕ) (n₁ n₂ a₁ a₂ Δ : ℤ),
      ResearchBankV18.ColourConductor.e (Nat.lcm q₁ q₂) (0 * Δ) = 1 →
        (ZeroFrequencyCompatibility.solutions q₁ q₂ n₁ n₂ a₁ a₂).card = 1) ∧
    (∃ (a c : ℕ → ℝ), (∀ n, |c n| ≤ 1) ∧ BalancedMod2 a ∧ ¬ BalancedMod2 (fun n => c n * a n)) ∧
    (¬ ((273 / 500 : ℚ) < 3 / 5 → ∀ err : ℝ → ℝ, PrimeDistributionProvider (273 / 500) err)) ∧
    (∃ bs : List ActualBranchData, LocalTransportBounds bs ∧
      ∀ (N : ℕ → ℝ) (c : ℝ), ¬ ActualCenteredSourceCompositionProvider bs N c) ∧
    (¬ (∀ η > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀,
        ([growingOuter].map fun b => b.outerWeight M).sum ≤ η * (fun _ => (1 : ℝ)) M)) ∧
    (¬ PrimeDistributionProvider 0 finiteErr) ∧
    (∃ Q : ℕ → Prop, (∃ M₀ : ℕ, ∀ M ≥ M₀, Q M) ∧ ¬ ∀ M ≥ 0, Q M) ∧
    (¬ ∀ bad : ℕ → Prop, (∃ M₀, ∀ M ≥ M₀, ¬ bad M) → (∀ M ≤ 0, ¬ bad M) → ∀ M, ¬ bad M) :=
  ⟨omega_zero_not_compatibility, residue_restriction_breaks_balance,
   support_below_threshold_no_provider, local_transport_not_branch_match,
   local_margins_not_global_control.2, (finite_verifier_not_analytic 0).2,
   conditional_asymptotic_no_explicit_M0 0, explicit_M0_required_for_splice 0⟩

end ScopeFirewalls
end ResearchBankV20
end Erdos287
