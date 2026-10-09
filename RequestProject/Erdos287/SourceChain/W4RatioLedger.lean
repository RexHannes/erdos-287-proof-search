import RequestProject.Erdos287.SourceChain.FCHSPropagation

/-!
# Erdős #287 — V100R4S §6: the W₄ ratio ledger (exponent algebra only)

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.  NO SPECTRAL ESTIMATE IS PROVED HERE.**

This file checks, in Lean, the *elementary exponent bookkeeping* of §6 of the V100R4S author proof
(`PROOFS/actual_atom_proof_FCHS.md`): starting from the three range conditions (1.1)–(1.3),
`Q ≤ N` and `Q, R, S ≥ 1`, every ratio displayed in (6.3), §6.2 and (6.6a–d) has the saving
claimed in (6.3)/(6.7).  It then shows that the three *narrow* W₄ estimates of `W4Route.lean`
(`W4DiagEstimate`, `W4RamEstimate`, `W4SpecEstimate`, each still an unproved hypothesis), evaluated
at the actual source scales `F ≤ c N/Q`, `C ≤ c N R S`, `B₀ ≤ c N R`, `0 < H ≤ Λ H₀` with
`H₀ = N Q R² S²/x`, imply the uniform W₄ bound of the shape (6.8).

The corrected `FCHS` term is kept throughout (it is **not** replaced by `FHS`); its contribution
is checked directly at the source scales, without assuming `H ≤ S` separately.

* `V100Range` — the hypotheses (1.1)–(1.3), `Q ≤ N`, `1 ≤ N, Q, R, S`, `1 < x`.
* `diag_ratio` (6.3), `ram_ratio` (§6.2), `ratio_6_6a` … `ratio_6_6d` (6.6a–d with the savings
  (6.7)), `H0_div_S_ratio` (the `H₀/S` comparison used for the FCHS domination).

The consequences for the W₄ right-hand sides (`spec_source_bound`, `W4_uniform_bound`,
`W4_uniform_bound_6eps`) are in `W4SourceBound.lean`.
-/

open Real

namespace Erdos287.SourceChain

/-- The V100R4S range hypotheses: (1.1)–(1.3), `Q ≤ N`, and `N, Q, R, S ≥ 1`, `x > 1`.
(The source assumes `N ≥ x^ε`; only `N ≥ 1` is used here.) -/
structure V100Range (x N Q R S ε : ℝ) : Prop where
  hx : 1 < x
  hN : 1 ≤ N
  hQ : 1 ≤ Q
  hR : 1 ≤ R
  hS : 1 ≤ S
  hQN : Q ≤ N
  h11 : N ^ 2 * R ^ 2 * S ≤ x ^ (1 - 8 * ε)
  h12 : N ^ ((71 : ℝ) / 50) * R * S ^ ((93 : ℝ) / 50) ≤ x ^ (1 - 16 * ε)
  h13 : N ^ ((39 : ℝ) / 25) * Q ^ ((11 : ℝ) / 25) * R ^ 2 * S ^ 5 ≤ x ^ (2 - 32 * ε)

namespace V100Range

variable {x N Q R S ε : ℝ}

lemma x_pos (h : V100Range x N Q R S ε) : 0 < x := by linarith [h.hx]
lemma N_pos (h : V100Range x N Q R S ε) : 0 < N := by linarith [h.hN]
lemma Q_pos (h : V100Range x N Q R S ε) : 0 < Q := by linarith [h.hQ]
lemma R_pos (h : V100Range x N Q R S ε) : 0 < R := by linarith [h.hR]
lemma S_pos (h : V100Range x N Q R S ε) : 0 < S := by linarith [h.hS]

/-- The three range conditions and the side conditions in logarithmic (linear) form. -/
lemma logs (h : V100Range x N Q R S ε) :
    0 < Real.log x ∧ 0 ≤ Real.log N ∧ 0 ≤ Real.log Q ∧ 0 ≤ Real.log R ∧ 0 ≤ Real.log S ∧
    Real.log Q ≤ Real.log N ∧
    2 * Real.log N + 2 * Real.log R + Real.log S ≤ (1 - 8 * ε) * Real.log x ∧
    71 / 50 * Real.log N + Real.log R + 93 / 50 * Real.log S ≤ (1 - 16 * ε) * Real.log x ∧
    39 / 25 * Real.log N + 11 / 25 * Real.log Q + 2 * Real.log R + 5 * Real.log S ≤
      (2 - 32 * ε) * Real.log x := by
  have hx0 := h.x_pos; have hN0 := h.N_pos; have hQ0 := h.Q_pos
  have hR0 := h.R_pos; have hS0 := h.S_pos
  have l1 := Real.log_le_log (by positivity) h.h11
  have l2 := Real.log_le_log (by positivity) h.h12
  have l3 := Real.log_le_log (by positivity) h.h13
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_pow] at l1 l2 l3
  push_cast at l1 l2 l3
  refine ⟨Real.log_pos h.hx, Real.log_nonneg h.hN, Real.log_nonneg h.hQ, Real.log_nonneg h.hR,
    Real.log_nonneg h.hS, Real.log_le_log hQ0 h.hQN, by linarith, by linarith, by linarith⟩

end V100Range

/-- Positivity-to-logarithm transfer used for every monomial comparison below. -/
lemma le_of_log_le_log' {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : Real.log a ≤ Real.log b) :
    a ≤ b := (Real.log_le_log_iff ha hb).mp h

/-- `x^{-s} ≤ x^{-8ε}` once `s ≥ 8ε`. -/
lemma rpow_saving_le {x s ε : ℝ} (hx : 1 < x) (hs : 8 * ε ≤ s) : x ^ (-s) ≤ x ^ (-8 * ε) :=
  Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)

/-! ### The ratios of (6.3), §6.2, (6.6a–d), with the savings (6.7) -/

section Ratios

variable {x N Q R S ε : ℝ} (h : V100Range x N Q R S ε)
include h

/-- **(6.3)** Diagonal ratio: `N²R²S/x ≤ x^{-8ε}`. -/
theorem diag_ratio : N ^ 2 * R ^ 2 * S / x ≤ x ^ (-8 * ε) := by
  have hx0 := h.x_pos; have hN0 := h.N_pos; have hQ0 := h.Q_pos
  have hR0 := h.R_pos; have hS0 := h.S_pos
  obtain ⟨lx, lN, lQ, lR, lS, lQN, l1, l2, l3⟩ := h.logs
  apply le_of_log_le_log' (by positivity) (by positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div, Real.log_pow]
  push_cast; nlinarith

/-- **§6.2** Ramanujan ratio: `N²QR³S³/x² ≤ x^{-64ε/3}`. -/
theorem ram_ratio : N ^ 2 * Q * R ^ 3 * S ^ 3 / x ^ 2 ≤ x ^ (-(64 * ε / 3)) := by
  have hx0 := h.x_pos; have hN0 := h.N_pos; have hQ0 := h.Q_pos
  have hR0 := h.R_pos; have hS0 := h.S_pos
  obtain ⟨lx, lN, lQ, lR, lS, lQN, l1, l2, l3⟩ := h.logs
  apply le_of_log_le_log' (by positivity) (by positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div, Real.log_pow]
  push_cast; nlinarith

/-- **(6.6a)** `NRS²/x ≤ x^{-40ε/3}`. -/
theorem ratio_6_6a : N * R * S ^ 2 / x ≤ x ^ (-(40 * ε / 3)) := by
  have hx0 := h.x_pos; have hN0 := h.N_pos; have hQ0 := h.Q_pos
  have hR0 := h.R_pos; have hS0 := h.S_pos
  obtain ⟨lx, lN, lQ, lR, lS, lQN, l1, l2, l3⟩ := h.logs
  apply le_of_log_le_log' (by positivity) (by positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div, Real.log_pow]
  push_cast; nlinarith

/-- **(6.6b)** `x^{θ-1} N^{1+θ/2} R^{1-θ} S^{2-5θ/2} ≤ x^{-25ε/2}` with `θ = 7/32`. -/
theorem ratio_6_6b :
    x ^ ((7 : ℝ) / 32 - 1) * N ^ (1 + (7 : ℝ) / 32 / 2) * R ^ (1 - (7 : ℝ) / 32) *
      S ^ (2 - 5 * ((7 : ℝ) / 32) / 2) ≤ x ^ (-(25 * ε / 2)) := by
  have hx0 := h.x_pos; have hN0 := h.N_pos; have hQ0 := h.Q_pos
  have hR0 := h.R_pos; have hS0 := h.S_pos
  obtain ⟨lx, lN, lQ, lR, lS, lQN, l1, l2, l3⟩ := h.logs
  apply le_of_log_le_log' (by positivity) (by positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow]
  nlinarith

/-- **(6.6c)** `(NQR²S⁵/x²)^{1/2} ≤ x^{-16ε}`. -/
theorem ratio_6_6c : (N * Q * R ^ 2 * S ^ 5 / x ^ 2) ^ ((1 : ℝ) / 2) ≤ x ^ (-(16 * ε)) := by
  have hx0 := h.x_pos; have hN0 := h.N_pos; have hQ0 := h.Q_pos
  have hR0 := h.R_pos; have hS0 := h.S_pos
  obtain ⟨lx, lN, lQ, lR, lS, lQN, l1, l2, l3⟩ := h.logs
  apply le_of_log_le_log' (by positivity) (by positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div, Real.log_pow]
  push_cast; nlinarith

/-- **(6.6d)** `x^{θ-1} N^{(1+θ)/2} Q^{(1-3θ)/2} R^{1-θ} S^{(5-5θ)/2} ≤ x^{-25ε/2}`, `θ = 7/32`. -/
theorem ratio_6_6d :
    x ^ ((7 : ℝ) / 32 - 1) * N ^ ((1 + (7 : ℝ) / 32) / 2) * Q ^ ((1 - 3 * ((7 : ℝ) / 32)) / 2) *
      R ^ (1 - (7 : ℝ) / 32) * S ^ ((5 - 5 * ((7 : ℝ) / 32)) / 2) ≤ x ^ (-(25 * ε / 2)) := by
  have hx0 := h.x_pos; have hN0 := h.N_pos; have hQ0 := h.Q_pos
  have hR0 := h.R_pos; have hS0 := h.S_pos
  obtain ⟨lx, lN, lQ, lR, lS, lQN, l1, l2, l3⟩ := h.logs
  apply le_of_log_le_log' (by positivity) (by positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow]
  nlinarith

/-- The `H₀/S` comparison behind the FCHS domination (landing note §3):
`H₀/S = NQR²S/x ≤ x^{-8ε}`. -/
theorem H0_div_S_ratio : N * Q * R ^ 2 * S ^ 2 / x / S ≤ x ^ (-8 * ε) := by
  have hx0 := h.x_pos; have hN0 := h.N_pos; have hQ0 := h.Q_pos
  have hR0 := h.R_pos; have hS0 := h.S_pos
  obtain ⟨lx, lN, lQ, lR, lS, lQN, l1, l2, l3⟩ := h.logs
  apply le_of_log_le_log' (by positivity) (by positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div, Real.log_pow]
  push_cast; nlinarith

end Ratios

end Erdos287.SourceChain
