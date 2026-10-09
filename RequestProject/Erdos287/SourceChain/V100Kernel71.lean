import RequestProject.Erdos287.SourceChain.W4SourceBound

/-!
# Erdős #287 — V100R4S §7: from (4.9) and (6.8) to the kernel bounds (7.1), (1.8), (1.9)

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.  NO SPECTRAL ESTIMATE IS PROVED HERE.**

V100R4S §7 combines the first-Cauchy bound (4.9)

  `|𝒦_H| ≤ D · (Af) · Λ_c · N/(√f Q R S^{3/2}) · √𝒲₄`

with the uniform W₄ bound (6.8) `𝒲₄ ≤ K Λ² T^{7/64} N²R²S³ x^{-6ε}`, `T ≤ Af`,
`Λ = C_A f x^{ρ₀}`.  Both inputs are **hypotheses** here: (4.9) is the (unformalized) source
inequality of §4, and (6.8) is available in Lean only conditionally on the three narrow W₄
estimates (`W4_uniform_bound_6eps`).  This file verifies the exponent bookkeeping of §7:

* `kernel_7_1` — the combination gives `|𝒦_H| ≤ K' f^{199/128} N²/Q · x^{ρ₀-3ε}`,
  with the explicit constant `K' = D A^{1+7/128} Λ_c √K C_A`; the `f`-exponent is
  `1 (colour) - 1/2 (Cauchy count) + 1 (Λ) + 7/128 (T^{7/128}) = 199/128`.
* `kernel_1_8` — with `ρ₀ ≤ ε/100` and the remaining `x^{o(1)}` costs `Λ_c ≤ x^{ε/4}`:
  `|𝒦_H| ≤ K'' f^{199/128} N²/(Q x^{2ε})`, the shape of (1.8).
* `kernel_1_9_of_narrow` — the end-to-end chain: (4.9) + the three narrow W₄ estimates
  + the range/scale data ⟹ the (1.9)-shape bound with constant `D A^{1+7/128} √(8c³) C_A`.
* `kernel_1_9` — for `f ≥ 1` this implies `|𝒦_H| ≤ K'' f^{263/128} N²/(Q x^{ε})`, the shape of
  (1.9) (the consumer's target in `AstraAtomBound`).
-/

open Real

namespace Erdos287.SourceChain

/-- `(a^r)^2 = a^{2r}` for `a ≥ 0`. -/
lemma rpow_sq_eq {a r : ℝ} (ha : 0 ≤ a) : (a ^ r) ^ 2 = a ^ (2 * r) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]; ring_nf

/-- The square root of the (6.8) right-hand side. -/
lemma sqrt_W4_rhs {K Λ T N R S x ε : ℝ} (hK : 0 ≤ K) (hΛ : 0 ≤ Λ) (hT : 0 ≤ T) (hN : 0 ≤ N)
    (hR : 0 ≤ R) (hS : 0 ≤ S) (hx : 0 < x) :
    Real.sqrt (K * Λ ^ 2 * T ^ ((7 : ℝ) / 64) * (N ^ 2 * R ^ 2 * S ^ 3) * x ^ (-6 * ε)) =
      Real.sqrt K * Λ * T ^ ((7 : ℝ) / 128) * (N * R * S ^ ((3 : ℝ) / 2)) * x ^ (-3 * ε) := by
  have hY : 0 ≤ Real.sqrt K * Λ * T ^ ((7 : ℝ) / 128) * (N * R * S ^ ((3 : ℝ) / 2)) *
      x ^ (-3 * ε) := by positivity
  rw [← Real.sqrt_sq hY]
  congr 1
  rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hK, rpow_sq_eq hT,
    rpow_sq_eq hS, rpow_sq_eq hx.le]
  have e3 : S ^ (2 * ((3 : ℝ) / 2)) = S ^ 3 := by
    rw [show (2 : ℝ) * (3 / 2) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e3]; ring_nf

/-- The `f`-ledger of (7.1): `(f · f · f^{7/128}) / √f = f^{199/128}`. -/
lemma f_ledger_199 {f : ℝ} (hf : 0 < f) :
    f * f * f ^ ((7 : ℝ) / 128) / Real.sqrt f = f ^ ((199 : ℝ) / 128) := by
  rw [Real.sqrt_eq_rpow, div_eq_iff (by positivity), ← Real.rpow_add hf]
  have e : f * f * f ^ ((7 : ℝ) / 128) = f ^ ((1 : ℝ) + 1 + 7 / 128) := by
    rw [Real.rpow_add hf, Real.rpow_add hf, Real.rpow_one]
  rw [e]; norm_num

/-- **(7.1), conditional on (4.9) and (6.8).**  With `T ≤ Af` and `Λ = C_A f x^{ρ₀}`:
`|𝒦_H| ≤ (D A^{1+7/128} Λ_c √K C_A) · f^{199/128} · N²/Q · x^{ρ₀-3ε}`. -/
theorem kernel_7_1 {KH D A f Λc N Q R S W K Λ T x ε CA ρ0 : ℝ} (hD : 0 ≤ D) (hA : 0 < A)
    (hf : 0 < f) (hΛc : 0 ≤ Λc) (hN : 0 < N) (hQ : 0 < Q) (hR : 0 < R) (hS : 0 < S)
    (hK : 0 ≤ K) (hCA : 0 ≤ CA) (hx : 0 < x) (hT : 0 ≤ T) (hTA : T ≤ A * f)
    (hΛ : Λ = CA * f * x ^ ρ0)
    (h49 : |KH| ≤ D * (A * f) * Λc * (N / (Real.sqrt f * Q * R * S ^ ((3 : ℝ) / 2))) *
      Real.sqrt W)
    (h68 : W ≤ K * Λ ^ 2 * T ^ ((7 : ℝ) / 64) * (N ^ 2 * R ^ 2 * S ^ 3) * x ^ (-6 * ε)) :
    |KH| ≤ D * A ^ (1 + (7 : ℝ) / 128) * Λc * Real.sqrt K * CA * f ^ ((199 : ℝ) / 128) *
      (N ^ 2 / Q) * x ^ (ρ0 - 3 * ε) := by
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; positivity
  have hsW : Real.sqrt W ≤
      Real.sqrt K * Λ * (A * f) ^ ((7 : ℝ) / 128) * (N * R * S ^ ((3 : ℝ) / 2)) *
        x ^ (-3 * ε) := by
    calc Real.sqrt W ≤ Real.sqrt (K * Λ ^ 2 * T ^ ((7 : ℝ) / 64) * (N ^ 2 * R ^ 2 * S ^ 3) *
          x ^ (-6 * ε)) := Real.sqrt_le_sqrt h68
      _ = Real.sqrt K * Λ * T ^ ((7 : ℝ) / 128) * (N * R * S ^ ((3 : ℝ) / 2)) *
          x ^ (-3 * ε) := sqrt_W4_rhs hK hΛ0 hT hN.le hR.le hS.le hx
      _ ≤ _ := by gcongr
  have hpre : 0 ≤ D * (A * f) * Λc * (N / (Real.sqrt f * Q * R * S ^ ((3 : ℝ) / 2))) := by
    positivity
  have hsf : 0 < Real.sqrt f := Real.sqrt_pos.mpr hf
  have hS32 : 0 < S ^ ((3 : ℝ) / 2) := by positivity
  have hAf : (A * f) ^ ((7 : ℝ) / 128) = A ^ ((7 : ℝ) / 128) * f ^ ((7 : ℝ) / 128) :=
    Real.mul_rpow hA.le hf.le
  have hAA : A * A ^ ((7 : ℝ) / 128) = A ^ (1 + (7 : ℝ) / 128) := by
    rw [Real.rpow_add hA, Real.rpow_one]
  have hxx : x ^ ρ0 * x ^ (-3 * ε) = x ^ (ρ0 - 3 * ε) := by
    rw [← Real.rpow_add hx]; ring_nf
  calc |KH| ≤ D * (A * f) * Λc * (N / (Real.sqrt f * Q * R * S ^ ((3 : ℝ) / 2))) *
        (Real.sqrt K * Λ * (A * f) ^ ((7 : ℝ) / 128) * (N * R * S ^ ((3 : ℝ) / 2)) *
          x ^ (-3 * ε)) := h49.trans (mul_le_mul_of_nonneg_left hsW hpre)
    _ = D * (A * A ^ ((7 : ℝ) / 128)) * Λc * Real.sqrt K * CA *
        (f * f * f ^ ((7 : ℝ) / 128) / Real.sqrt f) * (N ^ 2 / Q) *
        (x ^ ρ0 * x ^ (-3 * ε)) := by
        rw [hΛ, hAf]; field_simp
    _ = _ := by rw [hAA, f_ledger_199 hf, hxx]

/-- **(1.8)-shape kernel bound, conditional on (4.9) and (6.8).**  With `ρ₀ ≤ ε/100` and the
remaining `x^{o(1)}` costs bounded by `Λ_c ≤ x^{ε/4}` (as allowed in §7 for large `x`):
`|𝒦_H| ≤ (D A^{1+7/128} √K C_A) f^{199/128} N²/Q · x^{-2ε}`. -/
theorem kernel_1_8 {KH D A f Λc N Q R S W K Λ T x ε CA ρ0 : ℝ} (hD : 0 ≤ D) (hA : 0 < A)
    (hf : 0 < f) (hΛc : 0 ≤ Λc) (hN : 0 < N) (hQ : 0 < Q) (hR : 0 < R) (hS : 0 < S)
    (hK : 0 ≤ K) (hCA : 0 ≤ CA) (hx : 1 ≤ x) (hε : 0 ≤ ε) (hT : 0 ≤ T) (hTA : T ≤ A * f)
    (hΛ : Λ = CA * f * x ^ ρ0) (hρ : ρ0 ≤ ε / 100) (hΛcx : Λc ≤ x ^ (ε / 4))
    (h49 : |KH| ≤ D * (A * f) * Λc * (N / (Real.sqrt f * Q * R * S ^ ((3 : ℝ) / 2))) *
      Real.sqrt W)
    (h68 : W ≤ K * Λ ^ 2 * T ^ ((7 : ℝ) / 64) * (N ^ 2 * R ^ 2 * S ^ 3) * x ^ (-6 * ε)) :
    |KH| ≤ D * A ^ (1 + (7 : ℝ) / 128) * Real.sqrt K * CA * f ^ ((199 : ℝ) / 128) *
      (N ^ 2 / Q) * x ^ (-2 * ε) := by
  have hx0 : 0 < x := by linarith
  have h := kernel_7_1 hD hA hf hΛc hN hQ hR hS hK hCA hx0 hT hTA hΛ h49 h68
  have hxe : Λc * x ^ (ρ0 - 3 * ε) ≤ x ^ (-2 * ε) := by
    calc Λc * x ^ (ρ0 - 3 * ε) ≤ x ^ (ε / 4) * x ^ (ρ0 - 3 * ε) := by gcongr
      _ = x ^ (ε / 4 + (ρ0 - 3 * ε)) := by rw [Real.rpow_add hx0]
      _ ≤ x ^ (-2 * ε) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hk : 0 ≤ D * A ^ (1 + (7 : ℝ) / 128) * Real.sqrt K * CA * f ^ ((199 : ℝ) / 128) *
      (N ^ 2 / Q) := by positivity
  calc |KH| ≤ D * A ^ (1 + (7 : ℝ) / 128) * Λc * Real.sqrt K * CA * f ^ ((199 : ℝ) / 128) *
        (N ^ 2 / Q) * x ^ (ρ0 - 3 * ε) := h
    _ = (D * A ^ (1 + (7 : ℝ) / 128) * Real.sqrt K * CA * f ^ ((199 : ℝ) / 128) * (N ^ 2 / Q)) *
        (Λc * x ^ (ρ0 - 3 * ε)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hxe hk

/-- **(1.9)-shape kernel bound** (the target exponent `263/128` of `AstraAtomBound`), for `f ≥ 1`,
conditional on (4.9) and (6.8). -/
theorem kernel_1_9 {KH D A f Λc N Q R S W K Λ T x ε CA ρ0 : ℝ} (hD : 0 ≤ D) (hA : 0 < A)
    (hf : 1 ≤ f) (hΛc : 0 ≤ Λc) (hN : 0 < N) (hQ : 0 < Q) (hR : 0 < R) (hS : 0 < S)
    (hK : 0 ≤ K) (hCA : 0 ≤ CA) (hx : 1 ≤ x) (hε : 0 ≤ ε) (hT : 0 ≤ T) (hTA : T ≤ A * f)
    (hΛ : Λ = CA * f * x ^ ρ0) (hρ : ρ0 ≤ ε / 100) (hΛcx : Λc ≤ x ^ (ε / 4))
    (h49 : |KH| ≤ D * (A * f) * Λc * (N / (Real.sqrt f * Q * R * S ^ ((3 : ℝ) / 2))) *
      Real.sqrt W)
    (h68 : W ≤ K * Λ ^ 2 * T ^ ((7 : ℝ) / 64) * (N ^ 2 * R ^ 2 * S ^ 3) * x ^ (-6 * ε)) :
    |KH| ≤ D * A ^ (1 + (7 : ℝ) / 128) * Real.sqrt K * CA * f ^ ((263 : ℝ) / 128) * N ^ 2 / Q *
      x ^ (-ε) := by
  have hf0 : 0 < f := by linarith
  have h := kernel_1_8 hD hA hf0 hΛc hN hQ hR hS hK hCA hx hε hT hTA hΛ hρ hΛcx h49 h68
  have h1 : f ^ ((199 : ℝ) / 128) ≤ f ^ ((263 : ℝ) / 128) :=
    Real.rpow_le_rpow_of_exponent_le hf (by norm_num)
  have h2 : x ^ (-2 * ε) ≤ x ^ (-ε) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hc : 0 ≤ D * A ^ (1 + (7 : ℝ) / 128) * Real.sqrt K * CA := by positivity
  calc |KH| ≤ D * A ^ (1 + (7 : ℝ) / 128) * Real.sqrt K * CA * f ^ ((199 : ℝ) / 128) *
        (N ^ 2 / Q) * x ^ (-2 * ε) := h
    _ ≤ D * A ^ (1 + (7 : ℝ) / 128) * Real.sqrt K * CA * f ^ ((263 : ℝ) / 128) *
        (N ^ 2 / Q) * x ^ (-ε) := by gcongr
    _ = _ := by ring

/-- **End-to-end conditional chain (4.9) + narrow W₄ estimates ⟹ (1.9)-shape.**  The only
analytic inputs are the first-Cauchy inequality (4.9) (`h49`) and the three narrow W₄ estimates
(`hd`, `hr`, `hs`) with the structural split; everything else is the range data (1.1)–(1.3),
the source scales of §6 and the parameter choices of §7. -/
theorem kernel_1_9_of_narrow {KH D A f Λc N Q R S x ε c F C B0 H Λ Λp T W Wd Wr Ws CA ρ0 : ℝ}
    (h : V100Range x N Q R S ε) (hε : 0 ≤ ε) (hc : 1 ≤ c) (hD : 0 ≤ D) (hA : 0 < A)
    (hf : 1 ≤ f) (hΛc : 0 ≤ Λc) (hCA : 0 ≤ CA)
    (hF : 0 ≤ F) (hFle : F ≤ c * N / Q) (hC : 0 ≤ C) (hCle : C ≤ c * N * R * S)
    (hB0 : 0 ≤ B0) (hB0le : B0 ≤ c * N * R)
    (hH : 0 < H) (hHle : H ≤ Λ * (N * Q * R ^ 2 * S ^ 2 / x)) (hΛ1 : 1 ≤ Λ)
    (hΛ : Λ = CA * f * x ^ ρ0) (hρ : ρ0 ≤ ε / 100)
    (hΛp : 0 ≤ Λp) (hΛpx : Λp ≤ x ^ (2 * ε)) (hΛcx : Λc ≤ x ^ (ε / 4))
    (hT : 1 ≤ T) (hTA : T ≤ A * f)
    (hsplit : W ≤ Wd + Wr + Ws)
    (hd : W4DiagEstimate Wd Λp S H F C B0) (hr : W4RamEstimate Wr Λp S H F B0)
    (hs : W4SpecEstimate Ws Λp T F C B0 S H)
    (h49 : |KH| ≤ D * (A * f) * Λc * (N / (Real.sqrt f * Q * R * S ^ ((3 : ℝ) / 2))) *
      Real.sqrt W) :
    |KH| ≤ D * A ^ (1 + (7 : ℝ) / 128) * Real.sqrt (8 * c ^ 3) * CA * f ^ ((263 : ℝ) / 128) *
      N ^ 2 / Q * x ^ (-ε) := by
  have h68 := W4_uniform_bound_6eps h hε hc hF hFle hC hCle hB0 hB0le hH hHle hΛ1 hΛp hΛpx hT
    hsplit hd hr hs
  have h68' : W ≤ (8 * c ^ 3) * Λ ^ 2 * T ^ ((7 : ℝ) / 64) * (N ^ 2 * R ^ 2 * S ^ 3) *
      x ^ (-6 * ε) := by
    refine h68.trans (le_of_eq ?_)
    ring
  have hc00 : 0 ≤ c := by linarith
  have hc0 : 0 ≤ 8 * c ^ 3 := by positivity
  exact kernel_1_9 hD hA hf hΛc h.N_pos h.Q_pos h.R_pos h.S_pos hc0 hCA h.hx.le hε
    (by linarith) hTA hΛ hρ hΛcx h49 h68'

end Erdos287.SourceChain
