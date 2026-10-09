import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Erdős #287 — Research Bank V23 §7: the hat-reference approximation provider

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

## EXTERNAL PROVIDER (interface only; never constructed)

`HatReferenceApproximationProvider K EAB` — the tensor/reference approximation

    E_ij |A - B|² ≤ C (log x)^{-(K+26)}   eventually,   C ≥ 0 fixed.

## Consequences

* `hat_approximation_eventually_small` (LEAN CONDITIONAL) — the provider makes `E_ij|A - B|²`
  eventually `≤ ε` for every `ε > 0` (`log x → ∞`), i.e. it is an `o(1)` error in explicit form.

## Firewall (LEAN BANK)

The piecewise-linear hat interpolant `hat x = max 0 (1 - |x|)` is NOT a smooth cutoff:
* **`hat_not_differentiableAt_zero`** — `hat` is not differentiable at `0`;
* `hat_ne_differentiable` — no everywhere-differentiable function equals `hat`, so the hat
  reference must never be identified with a smooth cutoff.
-/

namespace Erdos287
namespace ResearchBankV23
namespace HatApproximationProvider

open Filter

/-- **Hat-reference approximation provider** (EXTERNAL PROVIDER; never constructed):
`EAB M = E_ij |A - B|²` at scale `M`. -/
structure HatReferenceApproximationProvider (K : ℕ) (EAB : ℕ → ℝ) : Prop where
  nonneg : ∀ M, 0 ≤ EAB M
  bound : ∃ C : ℝ, 0 ≤ C ∧ ∃ M₀ : ℕ, ∀ M ≥ M₀, EAB M ≤ C / Real.log M ^ (K + 26)

/-- **The hat approximation error is eventually `≤ ε`** (LEAN CONDITIONAL). -/
theorem hat_approximation_eventually_small {K : ℕ} {EAB : ℕ → ℝ}
    (P : HatReferenceApproximationProvider K EAB) :
    ∀ ε > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀, |EAB M| ≤ ε := by
  intro ε hε
  obtain ⟨C, hC, M1, hM1⟩ := P.bound
  set T : ℝ := max 1 (C / ε)
  refine ⟨max M1 ⌈Real.exp T⌉₊, fun M hM => ?_⟩
  have hM1' : M1 ≤ M := le_trans (le_max_left _ _) hM
  have hceil : ⌈Real.exp T⌉₊ ≤ M := le_trans (le_max_right _ _) hM
  have hMe : Real.exp T ≤ M := le_trans (Nat.le_ceil _) (by exact_mod_cast hceil)
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le (Real.exp_pos _) hMe
  have hlogT : T ≤ Real.log M := by
    rw [← Real.log_exp T]; exact Real.log_le_log (Real.exp_pos _) hMe
  have hT1 : 1 ≤ T := le_max_left _ _
  have hlog1 : 1 ≤ Real.log M := le_trans hT1 hlogT
  have hpow : Real.log M ≤ Real.log M ^ (K + 26) := by
    calc Real.log M = Real.log M ^ 1 := (pow_one _).symm
      _ ≤ Real.log M ^ (K + 26) := pow_le_pow_right₀ hlog1 (by omega)
  have hlogpos : 0 < Real.log M := by linarith
  rw [abs_of_nonneg (P.nonneg M)]
  calc EAB M ≤ C / Real.log M ^ (K + 26) := hM1 M hM1'
    _ ≤ C / Real.log M := div_le_div_of_nonneg_left hC hlogpos hpow
    _ ≤ ε := by
      rw [div_le_iff₀ hlogpos]
      have : C / ε ≤ Real.log M := le_trans (le_max_right _ _) hlogT
      rw [div_le_iff₀ hε] at this
      linarith

/-- The piecewise-linear hat interpolant. -/
noncomputable def hat (x : ℝ) : ℝ := max 0 (1 - |x|)

/-- **The hat interpolant is not differentiable at `0`** (LEAN BANK). -/
theorem hat_not_differentiableAt_zero : ¬ DifferentiableAt ℝ hat 0 := by
  intro hd
  have heq : (fun x : ℝ => 1 - hat x) =ᶠ[nhds 0] fun x => |x| := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with x hx
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
    unfold hat
    rw [max_eq_right (by linarith)]
    ring
  exact not_differentiableAt_abs_zero
    (((differentiableAt_const (1 : ℝ)).sub hd).congr_of_eventuallyEq heq.symm)

/-- **Firewall**: no everywhere-differentiable (in particular no smooth) cutoff equals `hat`. -/
theorem hat_ne_differentiable (f : ℝ → ℝ) (hf : Differentiable ℝ f) : f ≠ hat := by
  rintro rfl
  exact hat_not_differentiableAt_zero (hf 0)

end HatApproximationProvider
end ResearchBankV23
end Erdos287
