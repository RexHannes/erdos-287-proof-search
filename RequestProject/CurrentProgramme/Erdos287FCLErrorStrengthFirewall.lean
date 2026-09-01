import RequestProject.CurrentProgramme.Erdos287FCLAlgebraicBridge

/-!
# The FCL error-strength firewall: fixed relative saving versus arbitrary log saving

`FCL ERROR-STRENGTH FIREWALL : KERNEL-PROVED (finite / elementary)`

This module is **append-only**.

Two very different error-strength notions are kept apart.

```
ArbitraryLogSaving E B  :  ∀ A : ℕ, ∃ X₀, ∀ X ≥ X₀,  E X ≤ B X / (log X)^A
FixedRelativeSaving δ E B :  E ≤ δ · B                (one fixed δ, one scale)
```

The banked finite FCL compiler `fixedCertificate_prime_mass_pos` consumes only
the *numerical relative smallness* `E ≤ δ·B` together with `3δ < 1 + C_c`
(and, in the two-error form, the exact multi-error analogue).
`finiteCompiler_consumes_only_fixed_relative_saving` re-exports the compiler with
exactly these hypotheses, which shows that the finite compiler **does not
syntactically require an all-`A` hypothesis**.

`fixedRelativeSaving_not_arbitraryLogSaving` shows the two notions really differ:
a constant relative saving is not an arbitrary-power saving.

**Firewall.**  The analytic relative-smallness premise is *not* constructed here.
Nothing in this module proves `E ≤ δ·B` for the actual FCL error.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace FCLErrorStrength

open Erdos287.FixedCertificate

/-! ## §1.  The two error-strength notions -/

/-- **`ArbitraryLogSaving`** — the strong, all-`A` error hypothesis. -/
def ArbitraryLogSaving (E B : ℝ → ℝ) : Prop :=
  ∀ A : ℕ, ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → E X ≤ B X / (Real.log X) ^ A

/-- **`FixedRelativeSaving`** — the weak, numerical hypothesis actually consumed by the
finite compiler: one fixed `δ`, at one scale. -/
def FixedRelativeSaving (delta E B : ℝ) : Prop := E ≤ delta * B

/-- **`fixedRelativeSaving_not_arbitraryLogSaving`.**  `KERNEL-PROVED`.

A constant relative saving is strictly weaker: `E ≡ 1/2`, `B ≡ 1` satisfies
`FixedRelativeSaving (1/2)` but not `ArbitraryLogSaving`. -/
theorem fixedRelativeSaving_not_arbitraryLogSaving :
    ∃ E B : ℝ → ℝ, (∀ X : ℝ, FixedRelativeSaving (1 / 2) (E X) (B X)) ∧
      ¬ ArbitraryLogSaving E B := by
  refine ⟨fun _ => 1 / 2, fun _ => 1, fun _ => by norm_num [FixedRelativeSaving], ?_⟩
  intro h
  obtain ⟨X₀, hX₀⟩ := h 1
  set X : ℝ := max X₀ (Real.exp 3) with hXdef
  have hX1 : X₀ ≤ X := le_max_left _ _
  have hX2 : Real.exp 3 ≤ X := le_max_right _ _
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 3) hX2
  have hlog : (3 : ℝ) ≤ Real.log X := by
    have := Real.log_le_log (Real.exp_pos 3) hX2
    rwa [Real.log_exp] at this
  have hb := hX₀ X hX1
  rw [pow_one] at hb
  have hle : (1 : ℝ) / Real.log X ≤ 1 / 3 := by
    apply one_div_le_one_div_of_le (by norm_num) hlog
  linarith

/-- **`arbitraryLogSaving_not_constructed_here`.**  `KERNEL-PROVED`.

The all-`A` hypothesis is a genuine restriction and is nowhere established. -/
theorem arbitraryLogSaving_not_constructed_here :
    ∃ E B : ℝ → ℝ, ¬ ArbitraryLogSaving E B := by
  obtain ⟨E, B, -, h⟩ := fixedRelativeSaving_not_arbitraryLogSaving
  exact ⟨E, B, h⟩

/-! ## §2.  The finite compiler consumes only the fixed relative saving -/

/-- **`finiteCompiler_consumes_only_fixed_relative_saving`.**  `KERNEL-PROVED`.

The banked finite FCL compiler, re-exported with its hypotheses written in the
`FixedRelativeSaving` form.  There is **no** all-`A` hypothesis anywhere in the statement:
the only error input is the numerical relative smallness `E ≤ δ·B`, together with the
numerical margin condition `3δ < 1 + C_c`. -/
theorem finiteCompiler_consumes_only_fixed_relative_saving
    (d : FixedCertificateData) (Cc E delta : ℝ)
    (hLeak : LeakageBound d E)
    (hTotal : TotalCorrelationBound d E)
    (hMargin : ComparisonMargin d Cc E)
    (hBpos : 0 < d.B)
    (hRel : FixedRelativeSaving delta E d.B)
    (hdelta : 3 * delta < 1 + Cc) :
    0 < ∑ p ∈ d.P, d.a p :=
  fixedCertificate_prime_mass_pos d Cc E delta hLeak hTotal hMargin hBpos hRel hdelta

/-- **`fixedRelativeSaving_premise_not_supplied`.**  `KERNEL-PROVED`.

The relative-smallness premise is a genuine hypothesis: it fails for explicit data, so it
is never available for free. -/
theorem fixedRelativeSaving_premise_not_supplied :
    ∃ delta E B : ℝ, ¬ FixedRelativeSaving delta E B := by
  refine ⟨0, 1, 1, ?_⟩
  simp [FixedRelativeSaving]

end FCLErrorStrength
end Erdos287
