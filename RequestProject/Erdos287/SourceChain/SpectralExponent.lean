import RequestProject.Erdos287.CurrentTail.ExponentLedger

/-!
# Erdős #287 — source chain: quantitative `T_H^{7/128}` and the final `391/256` ledger

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**  Source level: `MESSAGE_LEVEL_SOURCE`
(request §9–§10; source pack §17 (TH.1)–(TH.3)).

## §9 — `7/128` is *derived*, not inserted

* `PascadiSpectralY θQ θR θH δ θexc` — the **narrow spectral provider**: for every input of
  the `E₂` shape there are `Y, Z ≥ 0` with `|𝒦|² ≤ Y Z` (Proposition-3.4 placement of `T_H`
  into `Y`), `Y ≤ T_H^{θexc/2} Y₀` (Proposition 3.8 with exceptional exponent `θexc`), and
  `Y₀ Z ≤ C² (x^{-δ} · trivial)²`.  It mentions no #287 object.
* `exc_exponent_chain` — `(7/32)/2 = 7/64`, `(7/64)/2 = 7/128`.
* `th_exponent_propagation` — `θexc ≤ 7/32`, `T_H ≥ 1`, `|𝒦|² ≤ YZ`, `Y ≤ T_H^{θexc/2} Y₀`
  give `|𝒦| ≤ √(Y₀ Z) · T_H^{7/128}`.
* `QuantitativeTH_of_spectralY` — `PascadiSpectralY … θexc` with `θexc ≤ 7/32` **implies** the
  previous provider `QuantitativeTH` (whose `7/128` was a parameter).  So `QuantitativeTH`
  is no longer an independent provider.
* `TH_le_f1_power` — `T_H ≤ f₁ ≤ x^σ` gives `T_H^{7/128} ≤ x^{7σ/128}`.

## §10 — the final exponent ledger

* `FinalLedger` — the six named costs (Fourier enlargement, phase cost, colour separation,
  packet norm, spectator exponent) and the Cauchy square root.
* `messageLedger` — the instantiation consistent with the supplied total: Fourier `1`,
  phase `0`, colour `7/128` (via `T_H ≤ f₁ ≤ x^σ`), packet norm `2`, spectator `0` (only
  logarithms, paid by the reciprocal-density norm).  Only the total `391/256` is supplied;
  the split is the one already used by the `CurrentTail` ledger.
* `messageLedger_coefficient` — after the Cauchy square root the coefficient is `391/256`.
* `ledger_391_iff` — `391/256 · σ < ε/2 ⟺` the `CurrentTail` net saving with `c_H = 1` is
  positive.
* `TH3_of_sigma_lt` — explicit threshold: `σ < 128 ε / 391` gives `391/256 · σ < ε/2`.
-/

open scoped BigOperators

namespace Erdos287.SourceChain

open Erdos287.CurrentTail

/-! ### §9 exponent propagation -/

theorem exc_exponent_chain : ((7 : ℚ) / 32) / 2 = 7 / 64 ∧ ((7 : ℚ) / 64) / 2 = 7 / 128 := by
  constructor <;> norm_num

/-- **Exponent propagation.**  `θexc ≤ 7/32`, `T_H ≥ 1`, `|𝒦|² ≤ YZ`, `Y ≤ T_H^{θexc/2} Y₀`,
`Y₀, Z ≥ 0` ⟹ `|𝒦| ≤ √(Y₀ Z) · T_H^{7/128}`. -/
theorem th_exponent_propagation {K Y Y0 Z TH θexc : ℝ} (hθ : θexc ≤ 7 / 32) (hTH : 1 ≤ TH)
    (hY0 : 0 ≤ Y0) (hZ : 0 ≤ Z) (hKY : K ^ 2 ≤ Y * Z) (hY : Y ≤ TH ^ (θexc / 2) * Y0) :
    |K| ≤ Real.sqrt (Y0 * Z) * TH ^ ((7 : ℝ) / 128) := by
  have hTH0 : 0 < TH := by linarith
  have h1 : K ^ 2 ≤ TH ^ (θexc / 2) * (Y0 * Z) := by
    calc K ^ 2 ≤ Y * Z := hKY
      _ ≤ TH ^ (θexc / 2) * Y0 * Z := mul_le_mul_of_nonneg_right hY hZ
      _ = _ := by ring
  have h2 : TH ^ (θexc / 2) ≤ (TH ^ ((7 : ℝ) / 128)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hTH0.le]
    exact Real.rpow_le_rpow_of_exponent_le hTH (by push_cast; linarith)
  have h3 : K ^ 2 ≤ (Real.sqrt (Y0 * Z) * TH ^ ((7 : ℝ) / 128)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hY0 hZ)]
    calc K ^ 2 ≤ TH ^ (θexc / 2) * (Y0 * Z) := h1
      _ ≤ (TH ^ ((7 : ℝ) / 128)) ^ 2 * (Y0 * Z) :=
          mul_le_mul_of_nonneg_right h2 (mul_nonneg hY0 hZ)
      _ = _ := by ring
  exact abs_le_of_sq_le_sq' h3 (by positivity) |> fun h => abs_le.2 h

/-- **Narrow spectral provider (Pascadi Prop. 3.4 + 3.8 shape, exceptional exponent `θexc`).**
Statement only about the bilinear Kloosterman form of arbitrary bounded coefficients. -/
def PascadiSpectralY (θQ θR θH δ θexc : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (Qset Rset Hset : Finset ℕ) (α β γ : ℕ → ℝ) (TH : ℝ),
    E2Hypotheses x Qset Rset Hset α β γ θQ θR θH TH →
      ∃ Y Y0 Z : ℝ, 0 ≤ Y0 ∧ 0 ≤ Z ∧
        (kloostermanForm Qset Rset Hset α β γ) ^ 2 ≤ Y * Z ∧
        Y ≤ TH ^ (θexc / 2) * Y0 ∧
        Y0 * Z ≤ (C * x ^ (-δ) * trivialSize Qset Rset Hset α β γ) ^ 2

theorem trivialSize_nonneg (Qset Rset Hset : Finset ℕ) (α β γ : ℕ → ℝ) :
    0 ≤ trivialSize Qset Rset Hset α β γ := by
  unfold trivialSize
  have h1 : 0 ≤ ∑ q ∈ Qset, |α q| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h2 : 0 ≤ ∑ r ∈ Rset, |β r| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h3 : 0 ≤ ∑ h ∈ Hset, |γ h| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  positivity

/-- **`QuantitativeTH` is derived** from the narrow spectral provider with `θexc ≤ 7/32`. -/
theorem QuantitativeTH_of_spectralY {θQ θR θH δ θexc : ℝ} (hθ : θexc ≤ 7 / 32)
    (h : PascadiSpectralY θQ θR θH δ θexc) : QuantitativeTH θQ θR θH δ := by
  obtain ⟨C, hC, x0, hx0⟩ := h
  refine ⟨C, hC, max x0 1, fun x hx Qset Rset Hset α β γ TH hE => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨Y, Y0, Z, hY0, hZ, hKY, hY, hYZ⟩ := hx0 x (le_trans (le_max_left _ _) hx) Qset Rset
    Hset α β γ TH hE
  have hprop := th_exponent_propagation hθ hE.TH_ge_one hY0 hZ hKY hY
  have hT := trivialSize_nonneg Qset Rset Hset α β γ
  have hxpos : 0 < x ^ (-δ) := Real.rpow_pos_of_pos (by linarith) _
  have hsq : Real.sqrt (Y0 * Z) ≤ C * x ^ (-δ) * trivialSize Qset Rset Hset α β γ := by
    rw [Real.sqrt_le_left (by positivity)]
    exact hYZ
  have hTHpos : 0 ≤ TH ^ ((7 : ℝ) / 128) := Real.rpow_nonneg (by linarith [hE.TH_ge_one]) _
  calc |kloostermanForm Qset Rset Hset α β γ|
      ≤ Real.sqrt (Y0 * Z) * TH ^ ((7 : ℝ) / 128) := hprop
    _ ≤ C * x ^ (-δ) * trivialSize Qset Rset Hset α β γ * TH ^ ((7 : ℝ) / 128) :=
        mul_le_mul_of_nonneg_right hsq hTHpos
    _ = C * TH ^ (((THLossExponent : ℚ) : ℝ)) * x ^ (-δ) *
          trivialSize Qset Rset Hset α β γ := by
        rw [THLossExponent]; push_cast; ring

/-- `T_H ≤ f₁ ≤ x^σ` ⟹ `T_H^{7/128} ≤ x^{7σ/128}`. -/
theorem TH_le_f1_power {TH f1 x σ : ℝ} (hTH : 0 ≤ TH) (h1 : TH ≤ f1) (h2 : f1 ≤ x ^ σ)
    (hx : 0 < x) : TH ^ ((7 : ℝ) / 128) ≤ x ^ (7 * σ / 128) := by
  calc TH ^ ((7 : ℝ) / 128) ≤ (x ^ σ) ^ ((7 : ℝ) / 128) :=
        Real.rpow_le_rpow hTH (h1.trans h2) (by norm_num)
    _ = x ^ (7 * σ / 128) := by rw [← Real.rpow_mul hx.le]; ring_nf

/-! ### §10 final ledger -/

/-- The six named costs (coefficients of `σ` in the exponent of `x`). -/
structure FinalLedger where
  fourier : ℚ
  phase : ℚ
  colour : ℚ
  packetNorm : ℚ
  spectator : ℚ

/-- Total loss before the Cauchy square root. -/
def FinalLedger.total (L : FinalLedger) : ℚ :=
  L.fourier + L.phase + L.colour + L.packetNorm + L.spectator

/-- Coefficient after the Cauchy square root. -/
def FinalLedger.afterCauchy (L : FinalLedger) : ℚ := L.total / 2

/-- The message-level instantiation (see the module docstring for provenance). -/
def messageLedger : FinalLedger where
  fourier := 1
  phase := 0
  colour := 7 / 128
  packetNorm := 2
  spectator := 0

/-- **The supplied coefficient `391/256`.** -/
theorem messageLedger_coefficient : messageLedger.afterCauchy = 391 / 256 := by
  unfold FinalLedger.afterCauchy FinalLedger.total messageLedger; norm_num

/-- The colour cost is exactly the `T_H` exponent `7/128` (with `T_H ≤ f₁ ≤ x^σ`). -/
theorem messageLedger_colour : messageLedger.colour = THLossExponent := rfl

/-- **`391/256 · σ < ε/2` ⟺ positive net saving** in the `CurrentTail` ledger with `c_H = 1`. -/
theorem ledger_391_iff (ε σ : ℚ) :
    (391 / 256) * σ < ε / 2 ↔ 0 < (ExponentData.mk ε σ 1).netSaving := by
  simp only [ExponentData.netSaving, ExponentData.grossSaving, ExponentData.fourierLoss,
    ExponentData.thLoss, ExponentData.populationLoss, THLossExponent]
  constructor <;> intro h <;> linarith

/-- **(TH.3) from an explicit threshold**: `σ < 128 ε / 391` ⟹ `391/256 · σ < ε/2`. -/
theorem TH3_of_sigma_lt {ε σ : ℚ} (h : σ < 128 * ε / 391) : (391 / 256) * σ < ε / 2 := by
  linarith

/-- A concrete admissible choice: `σ = 64 ε / 391` leaves the margin `ε/4`. -/
theorem TH3_margin (ε : ℚ) : ε / 2 - (391 / 256) * (64 * ε / 391) = ε / 4 := by ring

end Erdos287.SourceChain
