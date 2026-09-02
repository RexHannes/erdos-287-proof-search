import Mathlib

/-!
# The repaired fixed certificate: `c₂ = +1` and the indicator-truncated perturbation

```
REPAIRED CERTIFICATE DATA (finite/definitional part) : KERNEL-PROVED
ANALYTIC COMPARISON STATEMENTS                       : NOT PROVED HERE
```

This module is **append-only** and records, as *finite definitional data*, two facts
about the fixed certificate used by the endgame layer.

**§1 — the sign.**  The repaired certificate coefficient is

```
    c₂ = +1
```

recorded as an explicit rational constant, together with the counterguard that this
is a genuine choice (`c₂ ≠ −1`, `c₂ ≠ 0`).

**§2 — the perturbation is an indicator truncation, not a scalar shrink.**  The
perturbed certificate is

```
    g_ε(x) = g₀(x) · 1_{|x| ≤ 1/2 − 2ε}
```

`gPerturb` implements exactly that.  The kernel-proved separation theorem
`gPerturb_is_not_a_scalar_shrink` shows that this operation is **not** of the form
`g ↦ c·g` for any scalar `c`, so the two repairs are genuinely different objects.

No analytic property of `g₀`, and no published comparison inequality, is proved or
assumed here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace FixedCertificateRepair

/-! ## §1  The repaired coefficient `c₂ = +1` -/

/-- **`repairedC2`** — the repaired fixed-certificate coefficient.  Its value is `+1`. -/
def repairedC2 : ℚ := 1

/-- **`repairedC2_eq_one`.**  `KERNEL-PROVED`.  The recorded value is literally `+1`. -/
theorem repairedC2_eq_one : repairedC2 = 1 := rfl

/-- **`repairedC2_is_a_choice`.**  `KERNEL-PROVED`.  The recorded sign is a genuine datum:
it is neither `0` nor `−1`. -/
theorem repairedC2_is_a_choice : repairedC2 ≠ 0 ∧ repairedC2 ≠ -1 := by
  constructor <;> decide

/-! ## §2  The perturbed certificate is an indicator truncation -/

/-- **`gPerturb g₀ ε`** — the perturbed certificate

```
    g_ε(x) = g₀(x) · 1_{|x| ≤ 1/2 − 2ε}.
```

This is a *support truncation*: the value on the retained core is unchanged. -/
noncomputable def gPerturb (g0 : ℝ → ℝ) (eps : ℝ) : ℝ → ℝ :=
  fun x => if |x| ≤ 1 / 2 - 2 * eps then g0 x else 0

/-- **`gPerturb_eq_on_core`.**  `KERNEL-PROVED`.  Inside the retained window the perturbed
certificate agrees with `g₀` exactly — no scalar factor appears. -/
theorem gPerturb_eq_on_core (g0 : ℝ → ℝ) (eps x : ℝ) (hx : |x| ≤ 1 / 2 - 2 * eps) :
    gPerturb g0 eps x = g0 x := if_pos hx

/-- **`gPerturb_eq_zero_outside`.**  `KERNEL-PROVED`.  Outside the retained window the
perturbed certificate vanishes identically. -/
theorem gPerturb_eq_zero_outside (g0 : ℝ → ℝ) (eps x : ℝ) (hx : ¬ |x| ≤ 1 / 2 - 2 * eps) :
    gPerturb g0 eps x = 0 := if_neg hx

/-- **`gPerturb_zero_eps`.**  `KERNEL-PROVED`.  At `ε = 0` the truncation is the plain
window `|x| ≤ 1/2`. -/
theorem gPerturb_zero_eps (g0 : ℝ → ℝ) (x : ℝ) :
    gPerturb g0 0 x = if |x| ≤ 1 / 2 then g0 x else 0 := by
  simp [gPerturb]

/-- **`gPerturb_window_antitone`.**  `KERNEL-PROVED`.  Increasing `ε` can only remove
points: whatever the larger `ε` retains, the smaller one retains too. -/
theorem gPerturb_window_antitone (g0 : ℝ → ℝ) {eps₁ eps₂ x : ℝ} (h : eps₁ ≤ eps₂)
    (hx : gPerturb g0 eps₂ x ≠ 0) : gPerturb g0 eps₁ x = g0 x := by
  by_cases hc : |x| ≤ 1 / 2 - 2 * eps₂
  · exact gPerturb_eq_on_core g0 eps₁ x (by linarith)
  · exact absurd (gPerturb_eq_zero_outside g0 eps₂ x hc) hx

/-- **`gPerturb_is_not_a_scalar_shrink`.**  `KERNEL-PROVED`.

The repair is genuinely an indicator truncation: for explicit data there is **no** scalar
`c` with `g_ε = c · g₀`.  Hence the certificate perturbation may not be replaced by, or
confused with, a scalar shrink of `g₀`. -/
theorem gPerturb_is_not_a_scalar_shrink :
    ∃ (g0 : ℝ → ℝ) (eps : ℝ), ¬ ∃ c : ℝ, ∀ x : ℝ, gPerturb g0 eps x = c * g0 x := by
  refine ⟨fun _ => 1, 1 / 8, ?_⟩
  rintro ⟨c, hc⟩
  have h0 := hc 0
  have h1 := hc 1
  rw [gPerturb_eq_on_core _ _ _ (by norm_num)] at h0
  rw [gPerturb_eq_zero_outside _ _ _ (by norm_num)] at h1
  rw [← h0] at h1
  norm_num at h1

/-- **`gPerturb_agrees_with_scalar_shrink_only_trivially`.**  `KERNEL-PROVED`.

If the truncation *does* coincide with the scalar multiple `c · g₀` at a retained point
where `g₀ ≠ 0`, then `c = 1`; the two repairs can only agree where nothing is scaled. -/
theorem gPerturb_agrees_with_scalar_shrink_only_trivially
    {g0 : ℝ → ℝ} {eps c x : ℝ} (hx : |x| ≤ 1 / 2 - 2 * eps) (hg : g0 x ≠ 0)
    (h : gPerturb g0 eps x = c * g0 x) : c = 1 := by
  rw [gPerturb_eq_on_core g0 eps x hx] at h
  have h1 : c * g0 x = 1 * g0 x := by rw [← h, one_mul]
  exact mul_right_cancel₀ hg h1

end FixedCertificateRepair
end Erdos287
