import RequestProject.Erdos287.CurrentTail.E2Interface

/-!
# Erdős #287 — current tail consolidation: the exponent ledger and the order of choice

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.  Exact rational arithmetic, no floats.**

Ledger (all exponents of `X`, in `ℚ`):

* `fourierLoss = σ` — Fourier enlargement by the tiny base `f ≤ X^σ`;
* `thLoss = (7/128) · c_H σ` — the V97 quantitative `T_H` loss with `T_H = X^{c_H σ}`;
* `populationLoss = 2σ` — packet population `X^{2σ}`;
* `grossSaving = δ_crit - fourierLoss - thLoss - populationLoss`;
* `netSaving = grossSaving / 2` — Cauchy square root;
* fixed `K`-dependent logarithmic costs `(log X)^{C_K}` are absorbed last.

**Caveat (template).**  The loss coefficients `1`, `2` and the linear `T_H` dependence are the
bookkeeping shape listed in the request; only `7/128` is a paper value.  The specific numerical
`δ_crit`, `c_H` of the V97/V100 papers are not in the repository and are parameters here.

Kernel-proved:

* `chooseSigma`, `chooseSigma_pos`, `netSaving_chooseSigma` — choosing
  `σ = δ_crit / (2(3 + 7c_H/128))` leaves net saving exactly `δ_crit / 4 > 0`;
* `ledger_instance` — the instance `δ_crit = 1/100`, `c_H = 1`: `σ = 16/9775`, net `1/400`;
* `order_of_choice` — `δ_crit → σ → K → X`: for every `δ_crit > 0` there is `σ > 0` such that
  for every `K` and every `K`-dependent log cost `C_K` there is `X₀` with
  `(log X)^{C_K} ≤ X^{netSaving}` for all `X ≥ X₀`.
-/

open scoped BigOperators
open Filter

namespace Erdos287.CurrentTail

/-- Exponent data: critical reserve, support exponent, `T_H` exponent coefficient. -/
structure ExponentData where
  δcrit : ℚ
  σ : ℚ
  cTH : ℚ

namespace ExponentData

variable (d : ExponentData)

def fourierLoss : ℚ := d.σ
def thLoss : ℚ := THLossExponent * (d.cTH * d.σ)
def populationLoss : ℚ := 2 * d.σ
def grossSaving : ℚ := d.δcrit - d.fourierLoss - d.thLoss - d.populationLoss
def netSaving : ℚ := d.grossSaving / 2

end ExponentData

/-- The support exponent chosen after `δ_crit` (and `c_H`). -/
def chooseSigma (δ cTH : ℚ) : ℚ := δ / (2 * (3 + 7 / 128 * cTH))

theorem chooseSigma_pos {δ cTH : ℚ} (hδ : 0 < δ) (hc : 0 ≤ cTH) : 0 < chooseSigma δ cTH := by
  unfold chooseSigma; positivity

theorem netSaving_chooseSigma {δ cTH : ℚ} (hc : 0 ≤ cTH) :
    (ExponentData.mk δ (chooseSigma δ cTH) cTH).netSaving = δ / 4 := by
  have h : (3 + 7 / 128 * cTH) ≠ 0 := by positivity
  simp only [ExponentData.netSaving, ExponentData.grossSaving, ExponentData.fourierLoss,
    ExponentData.thLoss, ExponentData.populationLoss, chooseSigma, THLossExponent]
  field_simp
  ring

/-- Kernel-checked instance: `δ_crit = 1/100`, `c_H = 1` gives `σ = 16/9775`, net `1/400`. -/
theorem ledger_instance :
    chooseSigma (1 / 100) 1 = 16 / 9775 ∧
      (ExponentData.mk (1 / 100) (chooseSigma (1 / 100) 1) 1).netSaving = 1 / 400 := by
  refine ⟨by unfold chooseSigma; norm_num, ?_⟩
  rw [netSaving_chooseSigma (by norm_num)]; norm_num

/-- Fixed logarithmic costs are absorbed by any positive power saving. -/
theorem logCost_absorbed {s : ℝ} (hs : 0 < s) (C : ℝ) :
    ∃ X0 : ℝ, ∀ X ≥ X0, Real.log X ^ C ≤ X ^ s := by
  have h := (isLittleO_log_rpow_rpow_atTop C hs).bound one_pos
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.1 (h.and (Filter.eventually_gt_atTop 1))
  refine ⟨X0, fun X hX => ?_⟩
  obtain ⟨hb, hX1⟩ := hX0 X hX
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX1.le
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), one_mul] at hb
  exact hb

/-- **Order of choice `δ_crit → σ → K → X`.** -/
theorem order_of_choice {cTH : ℚ} (hc : 0 ≤ cTH) :
    ∀ δ : ℚ, 0 < δ → ∃ σ : ℚ, 0 < σ ∧ ∀ (K : ℕ) (CK : ℕ → ℝ), ∃ X0 : ℝ, ∀ X ≥ X0,
      Real.log X ^ (CK K) ≤ X ^ (((ExponentData.mk δ σ cTH).netSaving : ℚ) : ℝ) := by
  intro δ hδ
  refine ⟨chooseSigma δ cTH, chooseSigma_pos hδ hc, fun K CK => ?_⟩
  rw [netSaving_chooseSigma hc]
  exact logCost_absorbed (by have : (0 : ℚ) < δ / 4 := by positivity
                             exact_mod_cast this) (CK K)

end Erdos287.CurrentTail
