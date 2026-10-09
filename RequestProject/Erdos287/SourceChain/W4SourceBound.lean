import RequestProject.Erdos287.SourceChain.W4RatioLedger

/-!
# Erdős #287 — V100R4S §6.3–§6.4: the three narrow W₄ estimates at the source scales

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.  NO SPECTRAL ESTIMATE IS PROVED HERE.**

The narrow W₄ estimates `W4DiagEstimate`, `W4RamEstimate`, `W4SpecEstimate` of `W4Route.lean`
remain **hypotheses** (they are the analytic content of V100R4S (6.2), (6.4), (6.5)).  This file
proves only what follows from them by algebra, at the actual source scales of §6:

* `F ≤ c·N/Q`, `C ≤ c·NRS`, `B₀ ≤ c·NR` (`c ≥ 1` a fixed constant),
* the actual `H` with `0 < H ≤ Λ·H₀`, `H₀ = NQR²S²/x`, `Λ ≥ 1`,
* the range hypotheses `V100Range` ((1.1)–(1.3), `Q ≤ N`, `Q, R, S ≥ 1`) and `ε ≥ 0`.

Main results:

* `bracket_H_le` — `H(1 + w/H)^{7/32} ≤ Λ(H₀ + H₀^{25/32} w^{7/32})` (the `H`-scaling of §6.3).
* `pascadiInner_H_scale` — the corrected inner term (with `FCHS`) grows at most by `Λ`.
* `sqrt_three_le` — `√(a+b+c) ≤ √a + √b + √c`.
* `spec_mono_1` … `spec_mono_6` — the six monomials of the expanded spectral term are each
  `≤ c³ N²R²S³ x^{-8ε}`; four of them are the ratios (6.6a–d) (`1 ↔ a`, `2 ↔ c`, `4 ↔ b`,
  `5 ↔ d`), two (`3`, `6`) come from the retained `FCHS` term.
* `spec_source_bound` — `specRHS Λ_p T F C B₀ S H ≤ 6c³ Λ_p Λ^{3/2} T^{7/64} N²R²S³ x^{-8ε}`.
* `diag_source_bound`, `ram_source_bound` — the diagonal and Ramanujan right-hand sides.
* `W4_uniform_bound` — **(6.8)-shape, conditional**: the structural split and the three
  narrow estimates give `𝒲₄ ≤ 8c³ Λ_p Λ² T^{7/64} N²R²S³ x^{-8ε}` (for `T ≥ 1`).
* `W4_uniform_bound_6eps` — with `Λ_p ≤ x^{2ε}` (the "full `2ε` for the `x^{o(1)}` costs"
  of §6.4) this is `8c³ Λ² T^{7/64} N²R²S³ x^{-6ε}`, i.e. (6.8).
-/

open Real

namespace Erdos287.SourceChain

/-! ### Generic algebra -/

/-- `√(a+b+c) ≤ √a + √b + √c` for non-negative `a, b, c`. -/
theorem sqrt_three_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt (a + b + c) ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c := by
  rw [Real.sqrt_le_left (by positivity)]
  have h1 := Real.sq_sqrt ha; have h2 := Real.sq_sqrt hb; have h3 := Real.sq_sqrt hc
  have := Real.sqrt_nonneg a; have := Real.sqrt_nonneg b; have := Real.sqrt_nonneg c
  nlinarith [mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b),
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg c),
    mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c)]

/-- **`H`-scaling of the spectral bracket** (§6.3): for `0 < H ≤ ΛH₀`, `Λ ≥ 1`, `w ≥ 0`,
`H (1 + w/H)^{7/32} ≤ Λ (H₀ + H₀^{25/32} w^{7/32})`.  (Subadditivity of `t ↦ t^{7/32}` is used,
so no monotonicity in `H` is needed.) -/
theorem bracket_H_le {H H0 Λ w : ℝ} (hH : 0 < H) (hHle : H ≤ Λ * H0) (hΛ : 1 ≤ Λ)
    (hw : 0 ≤ w) :
    H * (1 + w / H) ^ ((7 : ℝ) / 32) ≤
      Λ * (H0 + H0 ^ (1 - (7 : ℝ) / 32) * w ^ ((7 : ℝ) / 32)) := by
  have hH0 : 0 < H0 := by
    by_contra hc; push_neg at hc; nlinarith
  have hsub : (1 + w / H) ^ ((7 : ℝ) / 32) ≤ 1 + (w / H) ^ ((7 : ℝ) / 32) := by
    simpa using Real.rpow_add_le_add_rpow zero_le_one (div_nonneg hw hH.le)
      (by norm_num : (0 : ℝ) ≤ 7 / 32) (by norm_num : (7 : ℝ) / 32 ≤ 1)
  have hsplit : H * (w / H) ^ ((7 : ℝ) / 32) = H ^ (1 - (7 : ℝ) / 32) * w ^ ((7 : ℝ) / 32) := by
    rw [Real.div_rpow hw hH.le, Real.rpow_sub hH, Real.rpow_one]; field_simp
  have hpow : H ^ (1 - (7 : ℝ) / 32) ≤ Λ * H0 ^ (1 - (7 : ℝ) / 32) := by
    have hΛ0 : 0 ≤ Λ := by linarith
    calc H ^ (1 - (7 : ℝ) / 32) ≤ (Λ * H0) ^ (1 - (7 : ℝ) / 32) :=
          Real.rpow_le_rpow hH.le hHle (by norm_num)
      _ = Λ ^ (1 - (7 : ℝ) / 32) * H0 ^ (1 - (7 : ℝ) / 32) := Real.mul_rpow hΛ0 hH0.le
      _ ≤ Λ ^ (1 : ℝ) * H0 ^ (1 - (7 : ℝ) / 32) := by
          gcongr
          · exact hΛ
          · norm_num
      _ = Λ * H0 ^ (1 - (7 : ℝ) / 32) := by rw [Real.rpow_one]
  have hw7 : 0 ≤ w ^ ((7 : ℝ) / 32) := Real.rpow_nonneg hw _
  calc H * (1 + w / H) ^ ((7 : ℝ) / 32) ≤ H * (1 + (w / H) ^ ((7 : ℝ) / 32)) :=
        mul_le_mul_of_nonneg_left hsub hH.le
    _ = H + H ^ (1 - (7 : ℝ) / 32) * w ^ ((7 : ℝ) / 32) := by rw [mul_add, mul_one, hsplit]
    _ ≤ Λ * H0 + Λ * H0 ^ (1 - (7 : ℝ) / 32) * w ^ ((7 : ℝ) / 32) := by
        gcongr
    _ = _ := by ring

/-- The corrected inner term (with the `FCHS` summand) grows at most by `Λ ≥ 1` when `H ≤ ΛH₀`. -/
theorem pascadiInner_H_scale {F C B0 S H H0 Λ : ℝ} (hF : 0 ≤ F) (hC : 0 ≤ C) (hB0 : 0 ≤ B0)
    (hS : 0 ≤ S) (hHle : H ≤ Λ * H0) (hΛ : 1 ≤ Λ) :
    pascadiInner F C B0 S H ≤ Λ * pascadiInner F C B0 S H0 := by
  unfold pascadiInner
  have hFC : 0 ≤ F * C * S := by positivity
  have h1 : F * C * H * S ≤ Λ * (F * C * H0 * S) := by
    have := mul_le_mul_of_nonneg_left hHle hFC; nlinarith
  have h2 : F * C ^ 2 ≤ Λ * (F * C ^ 2) := le_mul_of_one_le_left (by positivity) hΛ
  have h3 : B0 * C * S ^ 2 ≤ Λ * (B0 * C * S ^ 2) := le_mul_of_one_le_left (by positivity) hΛ
  nlinarith

/-- Monotonicity of the corrected inner term in `F, C, B₀`. -/
theorem pascadiInner_mono {F C B0 F' C' B0' S H : ℝ} (hF : 0 ≤ F) (hC : 0 ≤ C) (hB0 : 0 ≤ B0)
    (hS : 0 ≤ S) (hH : 0 ≤ H) (hFF : F ≤ F') (hCC : C ≤ C') (hBB : B0 ≤ B0') :
    pascadiInner F C B0 S H ≤ pascadiInner F' C' B0' S H := by
  unfold pascadiInner
  have hC2 : C ^ 2 ≤ C' ^ 2 := pow_le_pow_left₀ hC hCC 2
  have hF' : 0 ≤ F' := hF.trans hFF
  have hC' : 0 ≤ C' := hC.trans hCC
  have hB' : 0 ≤ B0' := hB0.trans hBB
  gcongr

/-! ### The six monomials of the expanded spectral term -/

section Monomials

variable {x N Q R S ε c : ℝ} (h : V100Range x N Q R S ε) (hε : 0 ≤ ε) (hc : 1 ≤ c)
include h hε hc

/-- Shared log-linear closing step: positivity data and the logarithmic range conditions. -/
private lemma mono_logs :
    0 < x ∧ 0 < N ∧ 0 < Q ∧ 0 < R ∧ 0 < S ∧ 0 < c ∧ 0 ≤ Real.log c ∧
    0 < Real.log x ∧ 0 ≤ Real.log N ∧ 0 ≤ Real.log Q ∧ 0 ≤ Real.log R ∧ 0 ≤ Real.log S ∧
    Real.log Q ≤ Real.log N ∧
    2 * Real.log N + 2 * Real.log R + Real.log S ≤ (1 - 8 * ε) * Real.log x ∧
    71 / 50 * Real.log N + Real.log R + 93 / 50 * Real.log S ≤ (1 - 16 * ε) * Real.log x ∧
    39 / 25 * Real.log N + 11 / 25 * Real.log Q + 2 * Real.log R + 5 * Real.log S ≤
      (2 - 32 * ε) * Real.log x ∧ 0 ≤ ε * Real.log x := by
  obtain ⟨lx, lN, lQ, lR, lS, lQN, l1, l2, l3⟩ := h.logs
  exact ⟨h.x_pos, h.N_pos, h.Q_pos, h.R_pos, h.S_pos, by linarith, Real.log_nonneg hc,
    lx, lN, lQ, lR, lS, lQN, l1, l2, l3, mul_nonneg hε lx.le⟩

/-! The six monomials of the expanded spectral term, each `≤ c³ N²R²S³ x^{-8ε}`.
Notation: `H₀ = NQR²S²/x`, `F = cN/Q`, `C = cNRS`, `B₀ = cNR`, `w = C√F/S^{3/2}`. -/

/-- Spectral monomial ↔ (6.6a). -/
theorem spec_mono_1 :
    (N * Q * R ^ 2 * S ^ 2 / x) * S ^ 2 * Real.sqrt (c * N / Q) * (Real.sqrt (c * N / Q) * (c * N * R * S)) ≤
      c ^ 3 * (N ^ 2 * R ^ 2 * S ^ 3) * x ^ (-8 * ε) := by
  obtain ⟨hx0, hN0, hQ0, hR0, hS0, hc0, lc, lx, lN, lQ, lR, lS, lQN, l1, l2, l3, hεx⟩ :=
    mono_logs h hε hc
  apply le_of_log_le_log' (by positivity) (by positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div, Real.log_pow,
    Real.log_sqrt]
  push_cast
  nlinarith

/-- Spectral monomial ↔ (6.6c). -/
theorem spec_mono_2 :
    (N * Q * R ^ 2 * S ^ 2 / x) * S ^ 2 * Real.sqrt (c * N / Q) * (Real.sqrt ((c * N * R) * (c * N * R * S)) * S) ≤
      c ^ 3 * (N ^ 2 * R ^ 2 * S ^ 3) * x ^ (-8 * ε) := by
  obtain ⟨hx0, hN0, hQ0, hR0, hS0, hc0, lc, lx, lN, lQ, lR, lS, lQN, l1, l2, l3, hεx⟩ :=
    mono_logs h hε hc
  apply le_of_log_le_log' (by positivity) (by positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div, Real.log_pow,
    Real.log_sqrt]
  push_cast
  nlinarith

/-- Spectral monomial ↔ retained `FCHS`, first bracket term. -/
theorem spec_mono_3 :
    (N * Q * R ^ 2 * S ^ 2 / x) * S ^ 2 * Real.sqrt (c * N / Q) * Real.sqrt ((c * N / Q) * (c * N * R * S) * (N * Q * R ^ 2 * S ^ 2 / x) * S) ≤
      c ^ 3 * (N ^ 2 * R ^ 2 * S ^ 3) * x ^ (-8 * ε) := by
  obtain ⟨hx0, hN0, hQ0, hR0, hS0, hc0, lc, lx, lN, lQ, lR, lS, lQN, l1, l2, l3, hεx⟩ :=
    mono_logs h hε hc
  apply le_of_log_le_log' (by positivity) (by positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div, Real.log_pow,
    Real.log_sqrt]
  push_cast
  nlinarith

/-- Spectral monomial ↔ (6.6b). -/
theorem spec_mono_4 :
    (N * Q * R ^ 2 * S ^ 2 / x) ^ (1 - (7 : ℝ) / 32) * ((c * N * R * S) * Real.sqrt (c * N / Q) / S ^ ((3 : ℝ) / 2)) ^ ((7 : ℝ) / 32) * S ^ 2 * Real.sqrt (c * N / Q) * (Real.sqrt (c * N / Q) * (c * N * R * S)) ≤
      c ^ 3 * (N ^ 2 * R ^ 2 * S ^ 3) * x ^ (-8 * ε) := by
  obtain ⟨hx0, hN0, hQ0, hR0, hS0, hc0, lc, lx, lN, lQ, lR, lS, lQN, l1, l2, l3, hεx⟩ :=
    mono_logs h hε hc
  apply le_of_log_le_log' (by positivity) (by positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div, Real.log_pow,
    Real.log_sqrt]
  push_cast
  nlinarith

/-- Spectral monomial ↔ (6.6d). -/
theorem spec_mono_5 :
    (N * Q * R ^ 2 * S ^ 2 / x) ^ (1 - (7 : ℝ) / 32) * ((c * N * R * S) * Real.sqrt (c * N / Q) / S ^ ((3 : ℝ) / 2)) ^ ((7 : ℝ) / 32) * S ^ 2 * Real.sqrt (c * N / Q) * (Real.sqrt ((c * N * R) * (c * N * R * S)) * S) ≤
      c ^ 3 * (N ^ 2 * R ^ 2 * S ^ 3) * x ^ (-8 * ε) := by
  obtain ⟨hx0, hN0, hQ0, hR0, hS0, hc0, lc, lx, lN, lQ, lR, lS, lQN, l1, l2, l3, hεx⟩ :=
    mono_logs h hε hc
  apply le_of_log_le_log' (by positivity) (by positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div, Real.log_pow,
    Real.log_sqrt]
  push_cast
  nlinarith

/-- Spectral monomial ↔ retained `FCHS`, second bracket term. -/
theorem spec_mono_6 :
    (N * Q * R ^ 2 * S ^ 2 / x) ^ (1 - (7 : ℝ) / 32) * ((c * N * R * S) * Real.sqrt (c * N / Q) / S ^ ((3 : ℝ) / 2)) ^ ((7 : ℝ) / 32) * S ^ 2 * Real.sqrt (c * N / Q) * Real.sqrt ((c * N / Q) * (c * N * R * S) * (N * Q * R ^ 2 * S ^ 2 / x) * S) ≤
      c ^ 3 * (N ^ 2 * R ^ 2 * S ^ 3) * x ^ (-8 * ε) := by
  obtain ⟨hx0, hN0, hQ0, hR0, hS0, hc0, lc, lx, lN, lQ, lR, lS, lQN, l1, l2, l3, hεx⟩ :=
    mono_logs h hε hc
  apply le_of_log_le_log' (by positivity) (by positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div, Real.log_pow,
    Real.log_sqrt]
  push_cast
  nlinarith

end Monomials

/-! ### The spectral right-hand side at the source scales -/

/-- **Spectral term at the source scales** (V100R4S §6.3, conditional only in that `specRHS` is
the right-hand side of the *hypothesised* estimate (6.5)):
`specRHS Λ_p T F C B₀ S H ≤ 6 c³ Λ_p Λ^{3/2} T^{7/64} N²R²S³ x^{-8ε}`. -/
theorem spec_source_bound {x N Q R S ε c F C B0 H Λ Λp T : ℝ} (h : V100Range x N Q R S ε)
    (hε : 0 ≤ ε) (hc : 1 ≤ c) (hF : 0 ≤ F) (hFle : F ≤ c * N / Q) (hC : 0 ≤ C)
    (hCle : C ≤ c * N * R * S) (hB0 : 0 ≤ B0) (hB0le : B0 ≤ c * N * R) (hH : 0 < H)
    (hHle : H ≤ Λ * (N * Q * R ^ 2 * S ^ 2 / x)) (hΛ : 1 ≤ Λ) (hΛp : 0 ≤ Λp) (hT : 0 ≤ T) :
    specRHS Λp T F C B0 S H ≤
      6 * c ^ 3 * Λp * Λ ^ ((3 : ℝ) / 2) * T ^ ((7 : ℝ) / 64) * (N ^ 2 * R ^ 2 * S ^ 3) *
        x ^ (-8 * ε) := by
  have hx0 := h.x_pos; have hN0 := h.N_pos; have hQ0 := h.Q_pos
  have hR0 := h.R_pos; have hS0 := h.S_pos
  have hc0 : 0 < c := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have m1 := spec_mono_1 h hε hc
  have m2 := spec_mono_2 h hε hc
  have m3 := spec_mono_3 h hε hc
  have m4 := spec_mono_4 h hε hc
  have m5 := spec_mono_5 h hε hc
  have m6 := spec_mono_6 h hε hc
  set H0 := N * Q * R ^ 2 * S ^ 2 / x with hH0def
  have hH0 : 0 < H0 := by positivity
  set Fm := c * N / Q
  set Cm := c * N * R * S
  set Bm := c * N * R
  set w := C * Real.sqrt F / S ^ ((3 : ℝ) / 2)
  set wm := Cm * Real.sqrt Fm / S ^ ((3 : ℝ) / 2)
  have hS32 : 0 < S ^ ((3 : ℝ) / 2) := by positivity
  have hw : 0 ≤ w := by positivity
  have hsF : Real.sqrt F ≤ Real.sqrt Fm := Real.sqrt_le_sqrt hFle
  have hwle : w ≤ wm := by
    apply div_le_div_of_nonneg_right _ hS32.le
    exact mul_le_mul hCle hsF (Real.sqrt_nonneg _) (by positivity)
  -- bracket
  have hbr : H * (1 + C * Real.sqrt F / (S ^ ((3 : ℝ) / 2) * H)) ^ ((7 : ℝ) / 32) ≤
      Λ * (H0 + H0 ^ (1 - (7 : ℝ) / 32) * wm ^ ((7 : ℝ) / 32)) := by
    have e : C * Real.sqrt F / (S ^ ((3 : ℝ) / 2) * H) = w / H := by
      simp only [w]; field_simp
    rw [e]
    refine (bracket_H_le hH hHle hΛ hw).trans ?_
    gcongr
  -- inner square root
  have hP : Real.sqrt (pascadiInner F C B0 S H) ≤ Real.sqrt Λ *
      (Real.sqrt Fm * Cm + Real.sqrt (Bm * Cm) * S + Real.sqrt (Fm * Cm * H0 * S)) := by
    have h1 := pascadiInner_H_scale hF hC hB0 hS0.le hHle hΛ
    have h2 := pascadiInner_mono hF hC hB0 hS0.le hH0.le hFle hCle hB0le
    have h3 : Real.sqrt (pascadiInner Fm Cm Bm S H0) ≤
        Real.sqrt Fm * Cm + Real.sqrt (Bm * Cm) * S + Real.sqrt (Fm * Cm * H0 * S) := by
      unfold pascadiInner
      refine (sqrt_three_le (by positivity) (by positivity) (by positivity)).trans (le_of_eq ?_)
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
        show Bm * Cm * S ^ 2 = (Bm * Cm) * S ^ 2 by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq hS0.le]
    calc Real.sqrt (pascadiInner F C B0 S H) ≤ Real.sqrt (Λ * pascadiInner Fm Cm Bm S H0) :=
          Real.sqrt_le_sqrt (h1.trans (mul_le_mul_of_nonneg_left h2 hΛ0.le))
      _ = Real.sqrt Λ * Real.sqrt (pascadiInner Fm Cm Bm S H0) := Real.sqrt_mul hΛ0.le _
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
  set V := c ^ 3 * (N ^ 2 * R ^ 2 * S ^ 3) * x ^ (-8 * ε)
  have hsum : (H0 + H0 ^ (1 - (7 : ℝ) / 32) * wm ^ ((7 : ℝ) / 32)) * S ^ 2 * Real.sqrt Fm *
      (Real.sqrt Fm * Cm + Real.sqrt (Bm * Cm) * S + Real.sqrt (Fm * Cm * H0 * S)) ≤ 6 * V := by
    have e : (H0 + H0 ^ (1 - (7 : ℝ) / 32) * wm ^ ((7 : ℝ) / 32)) * S ^ 2 * Real.sqrt Fm *
        (Real.sqrt Fm * Cm + Real.sqrt (Bm * Cm) * S + Real.sqrt (Fm * Cm * H0 * S)) =
        H0 * S ^ 2 * Real.sqrt Fm * (Real.sqrt Fm * Cm) +
        H0 * S ^ 2 * Real.sqrt Fm * (Real.sqrt (Bm * Cm) * S) +
        H0 * S ^ 2 * Real.sqrt Fm * Real.sqrt (Fm * Cm * H0 * S) +
        H0 ^ (1 - (7 : ℝ) / 32) * wm ^ ((7 : ℝ) / 32) * S ^ 2 * Real.sqrt Fm *
          (Real.sqrt Fm * Cm) +
        H0 ^ (1 - (7 : ℝ) / 32) * wm ^ ((7 : ℝ) / 32) * S ^ 2 * Real.sqrt Fm *
          (Real.sqrt (Bm * Cm) * S) +
        H0 ^ (1 - (7 : ℝ) / 32) * wm ^ ((7 : ℝ) / 32) * S ^ 2 * Real.sqrt Fm *
          Real.sqrt (Fm * Cm * H0 * S) := by ring
    rw [e]; linarith
  -- assemble
  have hT7 : 0 ≤ T ^ ((7 : ℝ) / 64) := Real.rpow_nonneg hT _
  have hΛ32 : Λ ^ ((3 : ℝ) / 2) = Λ * Real.sqrt Λ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hΛ0.le (by norm_num)]; norm_num
  have hbr0 : 0 ≤ (1 + C * Real.sqrt F / (S ^ ((3 : ℝ) / 2) * H)) ^ ((7 : ℝ) / 32) :=
    Real.rpow_nonneg (by positivity) _
  unfold specRHS
  calc Λp * T ^ ((7 : ℝ) / 64) * (1 + C * Real.sqrt F / (S ^ ((3 : ℝ) / 2) * H)) ^ ((7 : ℝ) / 32) *
        (H * S ^ 2 * Real.sqrt F * Real.sqrt (pascadiInner F C B0 S H))
      = Λp * T ^ ((7 : ℝ) / 64) *
        ((H * (1 + C * Real.sqrt F / (S ^ ((3 : ℝ) / 2) * H)) ^ ((7 : ℝ) / 32)) * S ^ 2 *
          Real.sqrt F * Real.sqrt (pascadiInner F C B0 S H)) := by ring
    _ ≤ Λp * T ^ ((7 : ℝ) / 64) *
        ((Λ * (H0 + H0 ^ (1 - (7 : ℝ) / 32) * wm ^ ((7 : ℝ) / 32))) * S ^ 2 * Real.sqrt Fm *
          (Real.sqrt Λ * (Real.sqrt Fm * Cm + Real.sqrt (Bm * Cm) * S +
            Real.sqrt (Fm * Cm * H0 * S)))) := by
        gcongr
    _ = Λp * T ^ ((7 : ℝ) / 64) * (Λ * Real.sqrt Λ) *
        ((H0 + H0 ^ (1 - (7 : ℝ) / 32) * wm ^ ((7 : ℝ) / 32)) * S ^ 2 * Real.sqrt Fm *
          (Real.sqrt Fm * Cm + Real.sqrt (Bm * Cm) * S + Real.sqrt (Fm * Cm * H0 * S))) := by
        ring
    _ ≤ Λp * T ^ ((7 : ℝ) / 64) * (Λ * Real.sqrt Λ) * (6 * V) := by gcongr
    _ = _ := by rw [hΛ32]; ring

/-! ### Diagonal and Ramanujan terms at the source scales -/

/-- **Diagonal term** (V100R4S (6.2)–(6.3)): `Λ_p · S H F C B₀ ≤ c³ Λ_p Λ N²R²S³ x^{-8ε}`. -/
theorem diag_source_bound {x N Q R S ε c F C B0 H Λ Λp : ℝ} (h : V100Range x N Q R S ε)
    (hε : 0 ≤ ε) (hc : 1 ≤ c) (hF : 0 ≤ F) (hFle : F ≤ c * N / Q) (hC : 0 ≤ C)
    (hCle : C ≤ c * N * R * S) (hB0 : 0 ≤ B0) (hB0le : B0 ≤ c * N * R) (hH : 0 ≤ H)
    (hHle : H ≤ Λ * (N * Q * R ^ 2 * S ^ 2 / x)) (hΛp : 0 ≤ Λp) :
    Λp * (S * H * F * C * B0) ≤
      c ^ 3 * Λp * Λ * (N ^ 2 * R ^ 2 * S ^ 3) * x ^ (-8 * ε) := by
  obtain ⟨hx0, hN0, hQ0, hR0, hS0, hc0, lc, lx, lN, lQ, lR, lS, lQN, l1, l2, l3, hεx⟩ :=
    mono_logs h hε hc
  have key : S * (N * Q * R ^ 2 * S ^ 2 / x) * (c * N / Q) * (c * N * R * S) * (c * N * R) ≤
      c ^ 3 * (N ^ 2 * R ^ 2 * S ^ 3) * x ^ (-8 * ε) := by
    apply le_of_log_le_log' (by positivity) (by positivity)
    simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div, Real.log_pow]
    push_cast
    nlinarith
  have step : S * H * F * C * B0 ≤
      Λ * (S * (N * Q * R ^ 2 * S ^ 2 / x) * (c * N / Q) * (c * N * R * S) * (c * N * R)) := by
    have hΛ0 : 0 ≤ Λ * (N * Q * R ^ 2 * S ^ 2 / x) := hH.trans hHle
    calc S * H * F * C * B0
        ≤ S * (Λ * (N * Q * R ^ 2 * S ^ 2 / x)) * (c * N / Q) * (c * N * R * S) * (c * N * R) := by
          gcongr
      _ = _ := by ring
  have hΛnn : 0 ≤ Λ := by
    by_contra hc'; push_neg at hc'
    have : Λ * (N * Q * R ^ 2 * S ^ 2 / x) < 0 := mul_neg_of_neg_of_pos hc' (by positivity)
    linarith
  calc Λp * (S * H * F * C * B0)
      ≤ Λp * (Λ * (c ^ 3 * (N ^ 2 * R ^ 2 * S ^ 3) * x ^ (-8 * ε))) := by
        exact mul_le_mul_of_nonneg_left (step.trans (mul_le_mul_of_nonneg_left key hΛnn)) hΛp
    _ = _ := by ring

/-- **Ramanujan term** (V100R4S (6.4), §6.2): `Λ_p · S² H² F B₀ ≤ c² Λ_p Λ² N²R²S³ x^{-8ε}`. -/
theorem ram_source_bound {x N Q R S ε c F B0 H Λ Λp : ℝ} (h : V100Range x N Q R S ε)
    (hε : 0 ≤ ε) (hc : 1 ≤ c) (hF : 0 ≤ F) (hFle : F ≤ c * N / Q)
    (hB0 : 0 ≤ B0) (hB0le : B0 ≤ c * N * R) (hH : 0 ≤ H)
    (hHle : H ≤ Λ * (N * Q * R ^ 2 * S ^ 2 / x)) (hΛp : 0 ≤ Λp) :
    Λp * (S ^ 2 * H ^ 2 * F * B0) ≤
      c ^ 2 * Λp * Λ ^ 2 * (N ^ 2 * R ^ 2 * S ^ 3) * x ^ (-8 * ε) := by
  obtain ⟨hx0, hN0, hQ0, hR0, hS0, hc0, lc, lx, lN, lQ, lR, lS, lQN, l1, l2, l3, hεx⟩ :=
    mono_logs h hε hc
  have key : S ^ 2 * (N * Q * R ^ 2 * S ^ 2 / x) ^ 2 * (c * N / Q) * (c * N * R) ≤
      c ^ 2 * (N ^ 2 * R ^ 2 * S ^ 3) * x ^ (-8 * ε) := by
    apply le_of_log_le_log' (by positivity) (by positivity)
    simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div, Real.log_pow]
    push_cast
    nlinarith
  have hH2 : H ^ 2 ≤ Λ ^ 2 * (N * Q * R ^ 2 * S ^ 2 / x) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hH hHle 2
  calc Λp * (S ^ 2 * H ^ 2 * F * B0)
      ≤ Λp * (S ^ 2 * (Λ ^ 2 * (N * Q * R ^ 2 * S ^ 2 / x) ^ 2) * (c * N / Q) * (c * N * R)) := by
        gcongr
    _ = Λp * Λ ^ 2 * (S ^ 2 * (N * Q * R ^ 2 * S ^ 2 / x) ^ 2 * (c * N / Q) * (c * N * R)) := by
        ring
    _ ≤ Λp * Λ ^ 2 * (c ^ 2 * (N ^ 2 * R ^ 2 * S ^ 3) * x ^ (-8 * ε)) := by gcongr
    _ = _ := by ring

/-! ### The uniform W₄ bound (6.8), conditional on the three narrow estimates -/

/-- **(6.8)-shape uniform W₄ bound, conditional.**  The structural split `𝒲₄ ≤ W_d + W_r + W_s`
and the three *hypothesised* narrow estimates, evaluated at the actual source scales, give
`𝒲₄ ≤ 8 c³ Λ_p Λ² T^{7/64} N²R²S³ x^{-8ε}` (for `T ≥ 1`). -/
theorem W4_uniform_bound {x N Q R S ε c F C B0 H Λ Λp T W Wd Wr Ws : ℝ}
    (h : V100Range x N Q R S ε) (hε : 0 ≤ ε) (hc : 1 ≤ c) (hF : 0 ≤ F) (hFle : F ≤ c * N / Q)
    (hC : 0 ≤ C) (hCle : C ≤ c * N * R * S) (hB0 : 0 ≤ B0) (hB0le : B0 ≤ c * N * R)
    (hH : 0 < H) (hHle : H ≤ Λ * (N * Q * R ^ 2 * S ^ 2 / x)) (hΛ : 1 ≤ Λ) (hΛp : 0 ≤ Λp)
    (hT : 1 ≤ T) (hsplit : W ≤ Wd + Wr + Ws)
    (hd : W4DiagEstimate Wd Λp S H F C B0) (hr : W4RamEstimate Wr Λp S H F B0)
    (hs : W4SpecEstimate Ws Λp T F C B0 S H) :
    W ≤ 8 * c ^ 3 * Λp * Λ ^ 2 * T ^ ((7 : ℝ) / 64) * (N ^ 2 * R ^ 2 * S ^ 3) *
      x ^ (-8 * ε) := by
  have hW := W4_bound_of_pieces hsplit hd hr hs
  have b1 := diag_source_bound h hε hc hF hFle hC hCle hB0 hB0le hH.le hHle hΛp
  have b2 := ram_source_bound h hε hc hF hFle hB0 hB0le hH.le hHle hΛp
  have b3 := spec_source_bound h hε hc hF hFle hC hCle hB0 hB0le hH hHle hΛ hΛp
    (by linarith : (0 : ℝ) ≤ T)
  have hx0 := h.x_pos
  set V := (N ^ 2 * R ^ 2 * S ^ 3) * x ^ (-8 * ε) with hV
  have hV0 : 0 ≤ V := by have := h.N_pos; have := h.R_pos; have := h.S_pos; positivity
  have hT1 : 1 ≤ T ^ ((7 : ℝ) / 64) := Real.one_le_rpow hT (by norm_num)
  have hc3 : c ^ 2 ≤ c ^ 3 := pow_le_pow_right₀ hc (by norm_num)
  have hc1 : 0 ≤ c ^ 2 := by positivity
  have hΛ1 : Λ ≤ Λ ^ 2 := by nlinarith
  have hΛ32 : Λ ^ ((3 : ℝ) / 2) ≤ Λ ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hΛ (by norm_num : (3 : ℝ) / 2 ≤ 2)
    simpa using this
  have e1 : c ^ 3 * Λp * Λ * (N ^ 2 * R ^ 2 * S ^ 3) * x ^ (-8 * ε) = c ^ 3 * Λp * Λ * V := by
    rw [hV]; ring
  have e2 : c ^ 2 * Λp * Λ ^ 2 * (N ^ 2 * R ^ 2 * S ^ 3) * x ^ (-8 * ε) =
      c ^ 2 * Λp * Λ ^ 2 * V := by rw [hV]; ring
  have e3 : 6 * c ^ 3 * Λp * Λ ^ ((3 : ℝ) / 2) * T ^ ((7 : ℝ) / 64) *
      (N ^ 2 * R ^ 2 * S ^ 3) * x ^ (-8 * ε) =
      6 * c ^ 3 * Λp * Λ ^ ((3 : ℝ) / 2) * T ^ ((7 : ℝ) / 64) * V := by rw [hV]; ring
  rw [e1] at b1; rw [e2] at b2; rw [e3] at b3
  have hgoal : 8 * c ^ 3 * Λp * Λ ^ 2 * T ^ ((7 : ℝ) / 64) * (N ^ 2 * R ^ 2 * S ^ 3) *
      x ^ (-8 * ε) = 8 * c ^ 3 * Λp * Λ ^ 2 * T ^ ((7 : ℝ) / 64) * V := by rw [hV]; ring
  rw [hgoal]
  have hT0 : 0 ≤ T ^ ((7 : ℝ) / 64) := by linarith
  have hc30 : 0 ≤ c ^ 3 := by linarith
  have k : 0 ≤ Λp * V := mul_nonneg hΛp hV0
  set K := c ^ 3 * Λ ^ 2 * T ^ ((7 : ℝ) / 64) with hK
  have q1 : c ^ 3 * Λ ≤ K := by
    calc c ^ 3 * Λ = c ^ 3 * Λ * 1 := by ring
      _ ≤ c ^ 3 * Λ ^ 2 * T ^ ((7 : ℝ) / 64) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hΛ1 hc30) hT1 zero_le_one (by positivity)
  have q2 : c ^ 2 * Λ ^ 2 ≤ K := by
    calc c ^ 2 * Λ ^ 2 = c ^ 2 * Λ ^ 2 * 1 := by ring
      _ ≤ c ^ 3 * Λ ^ 2 * T ^ ((7 : ℝ) / 64) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hc3 (by positivity)) hT1 zero_le_one
            (by positivity)
  have q3 : c ^ 3 * Λ ^ ((3 : ℝ) / 2) * T ^ ((7 : ℝ) / 64) ≤ K := by
    rw [hK]; gcongr
  have p1 : c ^ 3 * Λp * Λ * V ≤ K * (Λp * V) := by
    calc c ^ 3 * Λp * Λ * V = (c ^ 3 * Λ) * (Λp * V) := by ring
      _ ≤ K * (Λp * V) := mul_le_mul_of_nonneg_right q1 k
  have p2 : c ^ 2 * Λp * Λ ^ 2 * V ≤ K * (Λp * V) := by
    calc c ^ 2 * Λp * Λ ^ 2 * V = (c ^ 2 * Λ ^ 2) * (Λp * V) := by ring
      _ ≤ K * (Λp * V) := mul_le_mul_of_nonneg_right q2 k
  have p3 : 6 * c ^ 3 * Λp * Λ ^ ((3 : ℝ) / 2) * T ^ ((7 : ℝ) / 64) * V ≤ 6 * (K * (Λp * V)) := by
    calc 6 * c ^ 3 * Λp * Λ ^ ((3 : ℝ) / 2) * T ^ ((7 : ℝ) / 64) * V
        = 6 * ((c ^ 3 * Λ ^ ((3 : ℝ) / 2) * T ^ ((7 : ℝ) / 64)) * (Λp * V)) := by ring
      _ ≤ 6 * (K * (Λp * V)) := by gcongr
  have e4 : 8 * c ^ 3 * Λp * Λ ^ 2 * T ^ ((7 : ℝ) / 64) * V = 8 * (K * (Λp * V)) := by
    rw [hK]; ring
  rw [e4]
  linarith

/-- **(6.8)** with the full `2ε` reserve for the `x^{o(1)}` costs: if `Λ_p ≤ x^{2ε}` then
`𝒲₄ ≤ 8 c³ Λ² T^{7/64} N²R²S³ x^{-6ε}`.  Conditional on the three narrow estimates. -/
theorem W4_uniform_bound_6eps {x N Q R S ε c F C B0 H Λ Λp T W Wd Wr Ws : ℝ}
    (h : V100Range x N Q R S ε) (hε : 0 ≤ ε) (hc : 1 ≤ c) (hF : 0 ≤ F) (hFle : F ≤ c * N / Q)
    (hC : 0 ≤ C) (hCle : C ≤ c * N * R * S) (hB0 : 0 ≤ B0) (hB0le : B0 ≤ c * N * R)
    (hH : 0 < H) (hHle : H ≤ Λ * (N * Q * R ^ 2 * S ^ 2 / x)) (hΛ : 1 ≤ Λ) (hΛp : 0 ≤ Λp)
    (hΛpx : Λp ≤ x ^ (2 * ε)) (hT : 1 ≤ T) (hsplit : W ≤ Wd + Wr + Ws)
    (hd : W4DiagEstimate Wd Λp S H F C B0) (hr : W4RamEstimate Wr Λp S H F B0)
    (hs : W4SpecEstimate Ws Λp T F C B0 S H) :
    W ≤ 8 * c ^ 3 * Λ ^ 2 * T ^ ((7 : ℝ) / 64) * (N ^ 2 * R ^ 2 * S ^ 3) * x ^ (-6 * ε) := by
  have hW := W4_uniform_bound h hε hc hF hFle hC hCle hB0 hB0le hH hHle hΛ hΛp hT hsplit hd hr hs
  have hx0 := h.x_pos
  have hN0 := h.N_pos; have hR0 := h.R_pos; have hS0 := h.S_pos
  have hT0 : 0 ≤ T ^ ((7 : ℝ) / 64) := Real.rpow_nonneg (by linarith) _
  have hk : 0 ≤ 8 * c ^ 3 * Λ ^ 2 * T ^ ((7 : ℝ) / 64) * (N ^ 2 * R ^ 2 * S ^ 3) := by
    have : 0 ≤ c := by linarith
    positivity
  have hxx : x ^ (2 * ε) * x ^ (-8 * ε) = x ^ (-6 * ε) := by
    rw [← Real.rpow_add hx0]; ring_nf
  calc W ≤ 8 * c ^ 3 * Λp * Λ ^ 2 * T ^ ((7 : ℝ) / 64) * (N ^ 2 * R ^ 2 * S ^ 3) *
        x ^ (-8 * ε) := hW
    _ = (8 * c ^ 3 * Λ ^ 2 * T ^ ((7 : ℝ) / 64) * (N ^ 2 * R ^ 2 * S ^ 3)) *
        (Λp * x ^ (-8 * ε)) := by ring
    _ ≤ (8 * c ^ 3 * Λ ^ 2 * T ^ ((7 : ℝ) / 64) * (N ^ 2 * R ^ 2 * S ^ 3)) *
        (x ^ (2 * ε) * x ^ (-8 * ε)) := by gcongr
    _ = _ := by rw [hxx]

end Erdos287.SourceChain
