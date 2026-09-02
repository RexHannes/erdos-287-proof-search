import RequestProject.CurrentProgramme.Erdos287PhysicalSupportPartition
import RequestProject.CurrentProgramme.Erdos287FCLAlgebraicBridge

/-!
# The four-region transference algebra, and the positive-margin firewall

```
FOUR-ERROR TRANSFERENCE ALGEBRA : KERNEL-PROVED (finite algebra)
POSITIVE MARGIN SUPPLY          : OPEN / UNINHABITED (reused, never inhabited)
```

This module is **append-only**.

**§1 — the transference theorem.**  Over the literal four-class support partition
`I_X = P_X ⊎ N1_X ⊎ N2_X ⊎ U_X`, with the certificate kernel equal to `1` on `P_X`, and
with the four channel hypotheses

```
    Cc·Bmass − E_T ≤ totalCorr,    corr(N1_X) ≤ E_M,
    corr(N2_X)  ≤ E_2,             corr(U_X)  ≤ E_L,
```

the prime mass obeys

```
    primeMass ≥ (1 + Cc)·Bmass − E_T − E_L − E_2 − E_M .
```

**There is no factor `3`.**  The proof is exact finite algebra: the partition identity
plus four linear inequalities.  Each channel is attached to its own literal support class
and no analytic theorem is used or implied.

**§2 — positivity.**  If moreover `E_T + E_L + E_2 + E_M < (1 + Cc)·Bmass` (and
`0 < Bmass`), then `0 < primeMass`.

**§3 — the margin firewall.**  `PositiveMarginSupply` is *reused* from the banked bridge
and remains uninhabited.  The published limiting margin `≥ 6·10⁻⁶` and the research-level
statement "the perturbed margin stays positive for all sufficiently small `ε`" are recorded
as **metadata only**: no explicit `ε₀` is manufactured.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace FourErrorTransference

open Erdos287.PhysicalSupport

/-! ## §1  The four channel hypotheses and the transference theorem -/

/-- **`FourChannelBudget`** — the four typed error channels of the endgame, together with
the comparison constant `Cc`.  The channels are plain real numbers: no analytic content is
built in. -/
structure FourChannelBudget where
  /-- The comparison constant `C_c`. -/
  Cc : ℝ
  /-- `E_T`: the total / transverse channel. -/
  E_T : ℝ
  /-- `E_L`: the leakage channel of the class `U_X`. -/
  E_L : ℝ
  /-- `E_2`: the `N2_X` (λ-collar) channel. -/
  E_2 : ℝ
  /-- `E_M`: the `N1_X` (main comparison) channel. -/
  E_M : ℝ

namespace FourChannelBudget

variable (c : FourChannelBudget)

/-- The total error of the four channels. -/
def totalError : ℝ := c.E_T + c.E_L + c.E_2 + c.E_M

/-- **`totalError_identity`.**  `KERNEL-PROVED`.  The exact combination of the channels. -/
theorem totalError_identity : c.totalError = c.E_T + c.E_L + c.E_2 + c.E_M := rfl

end FourChannelBudget

/-- **`ChannelDomination`** — the four literal channel hypotheses, each attached to its own
support class.  Every field is an explicit hypothesis; none is proved here. -/
structure ChannelDomination (d : PhysicalSupportData) (w : PhysicalWeightData)
    (c : FourChannelBudget) : Prop where
  /-- The certificate kernel is `1` on the certificate-positive class `P_X`. -/
  kernel_on_P : ∀ n ∈ d.PX, w.HX n = 1
  /-- The total-correlation channel: `E_T` dominates the deficit `Cc·Bmass − totalCorr`. -/
  total_channel : c.Cc * Bmass d w - totalCorr d w ≤ c.E_T
  /-- The `N1_X` channel. -/
  main_channel : E_M_exact d w ≤ c.E_M
  /-- The `N2_X` channel. -/
  collar_channel : E_2_exact d w ≤ c.E_2
  /-- The `U_X` leakage channel. -/
  leakage_channel : E_L_exact d w ≤ c.E_L

/-- **`fourRegion_transference`.**  `KERNEL-PROVED` (pure finite algebra).

The four-region transference inequality

```
    primeMass ≥ (1 + Cc)·Bmass − E_T − E_L − E_2 − E_M .
```

No factor `3` occurs.  The proof uses only the exact support partition and the four
channel hypotheses. -/
theorem fourRegion_transference {d : PhysicalSupportData} {w : PhysicalWeightData}
    {c : FourChannelBudget} (h : ChannelDomination d w c) :
    primeMass d w ≥ (1 + c.Cc) * Bmass d w - c.E_T - c.E_L - c.E_2 - c.E_M := by
  have hsplit := channels_decompose_totalCorr d w
  have hP := P_correlation_eq_mass_difference d w h.kernel_on_P
  have hT := h.total_channel
  have hM := h.main_channel
  have h2 := h.collar_channel
  have hL := h.leakage_channel
  rw [hP] at hsplit
  nlinarith [hsplit, hT, hM, h2, hL]

/-! ## §2  Positivity of the prime mass -/

/-- **`primeMass_pos_of_channel_budget`.**  `KERNEL-PROVED` (pure finite algebra).

If the four channels together stay strictly below `(1 + Cc)·Bmass`, the certificate-positive
class carries strictly positive prime mass.

The hypothesis `0 < Bmass` is stated because the endgame specification requires it; the
finite algebra does not consume it (it is implied in the intended regime by the strict
channel budget together with nonnegative errors). -/
theorem primeMass_pos_of_channel_budget {d : PhysicalSupportData} {w : PhysicalWeightData}
    {c : FourChannelBudget} (h : ChannelDomination d w c)
    (hbudget : c.E_T + c.E_L + c.E_2 + c.E_M < (1 + c.Cc) * Bmass d w)
    (_hB : 0 < Bmass d w) :
    0 < primeMass d w := by
  have := fourRegion_transference h
  linarith

/-- **`transference_has_no_factor_three`.**  `KERNEL-PROVED`.

The banked inequality is genuinely the coefficient-one form.  Whenever the total error is
positive, the factor-`3` right-hand side is *strictly weaker* than the banked one, so the
two statements are different and no factor `3` has been silently inserted. -/
theorem transference_has_no_factor_three {Cc B E_T E_L E_2 E_M : ℝ}
    (h : 0 < E_T + E_L + E_2 + E_M) :
    (1 + Cc) * B - 3 * (E_T + E_L + E_2 + E_M)
      < (1 + Cc) * B - (E_T + E_L + E_2 + E_M) := by
  linarith

/-- **`channel_budget_is_an_input`.**  `KERNEL-PROVED`.

The strict channel budget is an *input*, not a theorem: explicit data refute it. -/
theorem channel_budget_is_an_input :
    ∃ (c : FourChannelBudget) (B : ℝ), 0 < B ∧
      ¬ (c.E_T + c.E_L + c.E_2 + c.E_M < (1 + c.Cc) * B) := by
  refine ⟨⟨0, 1, 1, 1, 1⟩, 1, by norm_num, ?_⟩
  show ¬ ((1 : ℝ) + 1 + 1 + 1 < (1 + 0) * 1)
  norm_num

/-! ## §3  The positive-margin firewall (metadata only) -/

/-- **`publishedLimitingMargin`** — the published limiting margin `6·10⁻⁶`, recorded as an
explicit rational constant.  This is **metadata**: no Lean theorem asserts that the
physical margin attains it. -/
def publishedLimitingMargin : ℚ := 6 / 1000000

/-- **`publishedLimitingMargin_pos`.**  `KERNEL-PROVED`.  The recorded constant is positive
(a fact about the *number*, not about the physical certificate). -/
theorem publishedLimitingMargin_pos : 0 < publishedLimitingMargin := by
  unfold publishedLimitingMargin; norm_num

/-- **`PerturbedMarginPositiveForSmallEps`** — the research-level statement that the
perturbed margin is positive for all sufficiently small `ε`, as a *typed proposition about
a supplied margin function*.  It is **not** proved and **not** inhabited here, and it is
deliberately kept in the non-effective `∃ ε₀ ∀ ε` shape: no explicit `ε₀` is manufactured. -/
def PerturbedMarginPositiveForSmallEps (margin : ℝ → ℝ) : Prop :=
  ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ eps : ℝ, 0 < eps → eps < eps0 → 0 < margin eps

/-- **`smallEps_margin_gives_no_explicit_eps0`.**  `KERNEL-PROVED`.

The firewall: the small-`ε` statement is a bare existential and does not deliver any
*named* threshold.  Concretely, for every candidate constant there is a margin function
satisfying the small-`ε` statement while failing at that constant. -/
theorem smallEps_margin_gives_no_explicit_eps0 (candidate : ℝ) (hc : 0 < candidate) :
    ∃ margin : ℝ → ℝ,
      PerturbedMarginPositiveForSmallEps margin ∧ ¬ (0 < margin candidate) := by
  refine ⟨fun eps => if eps < candidate then 1 else 0, ⟨candidate, hc, ?_⟩, ?_⟩
  · intro eps _ hlt
    simp [hlt]
  · simp

/-- **`positiveMarginSupply_still_uninhabited`.**  `KERNEL-PROVED`.

The banked margin wrapper is *reused*, never inhabited: it is refutable at explicit data. -/
theorem positiveMarginSupply_still_uninhabited :
    ∃ Cc : ℝ, ¬ Erdos287.FCLBridge.PositiveMarginSupply Cc :=
  Erdos287.FCLBridge.positiveMargin_not_automatic

/-- **`transference_with_supplied_margin`.**  `KERNEL-PROVED CONDITIONAL`.

Conditionally on a supplied positive margin `0 < 1 + Cc` and on the four channel
hypotheses, a channel total that is at most a *sixth* of `(1 + Cc)·Bmass` — the canonical
banked margin choice — gives strictly positive prime mass. -/
theorem transference_with_supplied_margin {d : PhysicalSupportData} {w : PhysicalWeightData}
    {c : FourChannelBudget} (hmargin : Erdos287.FCLBridge.PositiveMarginSupply c.Cc)
    (h : ChannelDomination d w c) (hB : 0 < Bmass d w)
    (hbudget : c.totalError ≤ (1 + c.Cc) / 6 * Bmass d w) :
    0 < primeMass d w := by
  have hCc : 0 < 1 + c.Cc := hmargin.margin
  have hstrict : c.E_T + c.E_L + c.E_2 + c.E_M < (1 + c.Cc) * Bmass d w := by
    have h1 : c.totalError = c.E_T + c.E_L + c.E_2 + c.E_M := rfl
    nlinarith [hbudget, hB, hCc]
  exact primeMass_pos_of_channel_budget h hstrict hB

end FourErrorTransference
end Erdos287
