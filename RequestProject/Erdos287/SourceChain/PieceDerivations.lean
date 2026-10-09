import RequestProject.Erdos287.SourceChain.PaymentCalculus
import RequestProject.Erdos287.SourceChain.SpectralExponent
import RequestProject.Erdos287.SourceChain.Separation

/-!
# Erdős #287 — source chain: per-cell derivations of the piece payments

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

Each named cell piece is reduced (kernel-proved) to its genuinely analytic input:

* **`F_AA^♯` (critical, spectral):** `sharp_cell_bound` and `sharp_powerSaving` —
  clean-AA kernel membership (`SharpMembership`: `|F^♯_ξ| ≤ P |𝒦|`, `𝒦` of `E₂` shape with
  `T_H ≤ x^σ`, normalisation `𝓑_ξ · trivial ≤ (x/f)² x^{3σ}`) + `QuantitativeTH` (itself
  derived from the narrow `PascadiSpectralY` with `θexc ≤ 7/32`) + a sub-power partition count
  `P ≤ C_P x^η` + the ledger `391/256 · σ + η/2 < δ/2` give a fixed power saving
  `x^{-(δ/2 - 391σ/256 - η/2)}`.
* **`F_AB^{k>1}`:** `fabKgt1_cell_bound` — the scale-free bound
  `|𝒫_T(q,a)| ≤ V`, the `τ/φ` moment `∑_{r₂} τ(r₂)/φ(r₂) ≤ T`, the harmonic factor
  `∑_l (N/(fl)+1) ≤ NH/f + L`, the support/coefficient facts, and the exponent inputs
  `fLR/M ≤ x^{σ-7/200}`, `f²L²R/x ≤ x^{σ-7/200-ε}` give `√(ML|F_AB^{k>1}|) ≤
  (x/f) · 2√(VTH) · x^{-(7/200-σ)/2}`.
* **Cleanup sectors (common `r`, common `n`, diagonal, zero mode `g > 1`):**
  `aaShape_cell_bound` — a physical count of shape `W (MN²/(f²Lz₀) + MN/f)` with
  `z₀ ≥ x^{η₀}` and `fL/N ≤ x^{-κ₁}` gives `(x/f) √W (x^{-η₀/2} + x^{-κ₁/2})`.
* **Near diagonal:** `nearDiag_cell_bound` — count `W MN²/(f²LK)` gives `(x/f)√(W/K)`.
-/

open scoped BigOperators
open Finset Filter

namespace Erdos287.SourceChain

open Erdos287.CurrentTail

variable {ι : Type*}

/-! ### `F_AA^♯` -/

theorem rpow_three_eq_sq {x a b c : ℝ} (hx : 0 < x) :
    x ^ a * x ^ b * x ^ c = (x ^ ((a + b + c) / 2)) ^ 2 := by
  rw [← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  congr 1; push_cast; ring

/-- **Single-cell bound for `F_AA^♯`.** -/
theorem sharp_cell_bound {x f Bc Fsh P Cq δ σ TH Triv Kf : ℝ} (hx : 1 ≤ x) (hf : 0 < f)
    (hBc : 0 ≤ Bc) (hP : 0 ≤ P) (hCq : 0 ≤ Cq) (hTH1 : 1 ≤ TH) (hTH : TH ≤ x ^ σ)
    (hTriv : 0 ≤ Triv) (hFs : Fsh ≤ P * |Kf|)
    (hK : |Kf| ≤ Cq * TH ^ ((7 : ℝ) / 128) * x ^ (-δ) * Triv)
    (hnorm : Bc * Triv ≤ (x / f) ^ 2 * x ^ (3 * σ)) :
    Real.sqrt (Bc * Fsh) ≤ x / f * (Real.sqrt (Cq * P) * x ^ (391 / 256 * σ - δ / 2)) := by
  have hx0 : 0 < x := by linarith
  have hTHp : TH ^ ((7 : ℝ) / 128) ≤ x ^ (7 * σ / 128) :=
    TH_le_f1_power (by linarith) hTH le_rfl hx0
  have h1 : Bc * Fsh ≤ (x / f) ^ 2 * (Cq * P) * (x ^ (391 / 256 * σ - δ / 2)) ^ 2 := by
    calc Bc * Fsh ≤ Bc * (P * (Cq * TH ^ ((7 : ℝ) / 128) * x ^ (-δ) * Triv)) :=
          mul_le_mul_of_nonneg_left (hFs.trans (mul_le_mul_of_nonneg_left hK hP)) hBc
      _ = P * Cq * TH ^ ((7 : ℝ) / 128) * x ^ (-δ) * (Bc * Triv) := by ring
      _ ≤ P * Cq * x ^ (7 * σ / 128) * x ^ (-δ) * ((x / f) ^ 2 * x ^ (3 * σ)) := by
          have hxd : 0 ≤ x ^ (-δ) := by positivity
          have hBT : 0 ≤ Bc * Triv := mul_nonneg hBc hTriv
          have hPC : 0 ≤ P * Cq := mul_nonneg hP hCq
          calc P * Cq * TH ^ ((7 : ℝ) / 128) * x ^ (-δ) * (Bc * Triv)
              ≤ P * Cq * x ^ (7 * σ / 128) * x ^ (-δ) * (Bc * Triv) := by gcongr
            _ ≤ _ := by gcongr
      _ = (x / f) ^ 2 * (Cq * P) * (x ^ (7 * σ / 128) * x ^ (-δ) * x ^ (3 * σ)) := by ring
      _ = (x / f) ^ 2 * (Cq * P) * (x ^ (391 / 256 * σ - δ / 2)) ^ 2 := by
          rw [rpow_three_eq_sq hx0]; congr 3; ring
  calc Real.sqrt (Bc * Fsh)
      ≤ Real.sqrt ((x / f) ^ 2 * (Cq * P) * (x ^ (391 / 256 * σ - δ / 2)) ^ 2) :=
        Real.sqrt_le_sqrt h1
    _ = x / f * (Real.sqrt (Cq * P) * x ^ (391 / 256 * σ - δ / 2)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity),
          Real.sqrt_sq (by positivity)]
        ring

/-- **Clean-AA kernel membership** for one packet at scale `x` (`REFEREE_PENDING`: box-stable
clean-AA factorisation export + cross-coprime partition).  Exact source membership: the clean
residual is dominated by `P` copies of a Kloosterman form satisfying every hypothesis of the
`E₂` shape, with `T_H ≤ x^σ` and the Fourier/packet normalisation. -/
def SharpMembership (x f Bc Fsh P σ θQ θR θH : ℝ) : Prop :=
  ∃ (Qset Rset Hset : Finset ℕ) (α β γ : ℕ → ℝ) (TH : ℝ),
    E2Hypotheses x Qset Rset Hset α β γ θQ θR θH TH ∧ TH ≤ x ^ σ ∧
    Fsh ≤ P * |kloostermanForm Qset Rset Hset α β γ| ∧
    Bc * trivialSize Qset Rset Hset α β γ ≤ (x / f) ^ 2 * x ^ (3 * σ)

/-- **`F_AA^♯` is paid with a fixed power saving.** -/
theorem sharp_powerSaving {S : TailSourceFamily ι} (C : OrderingBCells S) (Fs : FamilyScale S)
    {θQ θR θH δ σ η Cp : ℝ} (hQ : QuantitativeTH θQ θR θH δ) (P : ℕ → ℝ)
    (hP0 : ∀ X, 0 ≤ P X) (hCp : 0 ≤ Cp) (hPle : ∀ X, P X ≤ Cp * Fs.x X ^ η)
    (hmem : ∃ X1 : ℕ, ∀ X ≥ X1, ∀ ξ ∈ (S.T X).Xi,
      SharpMembership (Fs.x X) ((S.T X).f ξ) (C.Bc X ξ) (C.piece X ξ .sharp) (P X) σ θQ θR θH)
    (hledger : 391 / 256 * σ + η / 2 < δ / 2) :
    PowerSavingCell S C Fs .sharp := by
  obtain ⟨Cq, hCq, x0, hx0⟩ := hQ
  obtain ⟨X1, hX1⟩ := hmem
  obtain ⟨X2, hX2⟩ := Fs.x_large (max x0 1)
  refine ⟨0, δ / 2 - 391 / 256 * σ - η / 2, Real.sqrt (Cq * Cp), by linarith,
    Real.sqrt_nonneg _, max X1 X2, fun X hX ξ hξ => ?_⟩
  have hxX := hX2 X (le_trans (le_max_right _ _) hX)
  have hx1 : 1 ≤ Fs.x X := le_trans (le_max_right _ _) hxX
  have hxx0 : x0 ≤ Fs.x X := le_trans (le_max_left _ _) hxX
  have hx0' : 0 < Fs.x X := by linarith
  obtain ⟨Qset, Rset, Hset, α, β, γ, TH, hE, hTH, hFs, hnorm⟩ :=
    hX1 X (le_trans (le_max_left _ _) hX) ξ hξ
  have hfpos : (0 : ℝ) < (S.T X).f ξ := by exact_mod_cast (S.T X).f_pos ξ hξ
  have hK := hx0 (Fs.x X) hxx0 Qset Rset Hset α β γ TH hE
  rw [THLossExponent] at hK
  push_cast at hK
  have hcell := sharp_cell_bound hx1 hfpos (C.Bc_nonneg X ξ) (hP0 X) hCq.le hE.TH_ge_one hTH
    (trivialSize_nonneg _ _ _ _ _ _) hFs hK hnorm
  refine hcell.trans ?_
  have hxf : 0 ≤ Fs.x X / ((S.T X).f ξ : ℝ) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hxf
  rw [Real.rpow_zero, mul_one]
  have hsq : Real.sqrt (Cq * P X) ≤ Real.sqrt (Cq * Cp) * Fs.x X ^ (η / 2) := by
    rw [← Real.sqrt_mul_self (Real.rpow_nonneg hx0'.le (η / 2)), ← Real.sqrt_mul
      (by positivity)]
    apply Real.sqrt_le_sqrt
    rw [← Real.rpow_add hx0', show η / 2 + η / 2 = η by ring]
    calc Cq * P X ≤ Cq * (Cp * Fs.x X ^ η) := mul_le_mul_of_nonneg_left (hPle X) hCq.le
      _ = _ := by ring
  calc Real.sqrt (Cq * P X) * Fs.x X ^ (391 / 256 * σ - δ / 2)
      ≤ Real.sqrt (Cq * Cp) * Fs.x X ^ (η / 2) * Fs.x X ^ (391 / 256 * σ - δ / 2) :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = Real.sqrt (Cq * Cp) * Fs.x X ^ (-(δ / 2 - 391 / 256 * σ - η / 2)) := by
        rw [mul_assoc, ← Real.rpow_add hx0']; congr 2; ring

/-! ### `F_AB^{k>1}` -/

/-- **Single-cell bound for `F_AB^{k>1}`** (Opus repair 1, (AB.1) → (AB.2) → exponents). -/
theorem fabKgt1_cell_bound (D : FABData) {V T H M N L R x σ ε : ℝ} {N0 Nn : ℕ}
    (hV : ∀ (T q : ℝ) (a : ℤ), ‖PF D.Ψhat T q a‖ ≤ V)
    (hN : D.Ns ⊆ Finset.Ico N0 (N0 + Nn)) (hNcard : D.Ns.card ≤ Nn) (hNn : (Nn : ℝ) = N)
    (hC1 : ∀ l r1 r2 n1 n2, ‖D.C12 l r1 r2 n1 n2‖ ≤ 1)
    (hsupp : ∀ l r1 r2 n1 n2, ¬ n2 ≡ n1 [MOD D.f * l] → D.C12 l r1 r2 n1 n2 = 0)
    (hR1 : (D.R1.card : ℝ) ≤ R)
    (hT : ∑ r2 ∈ D.R2, (r2.divisors.card : ℝ) / Nat.totient r2 ≤ T)
    (hH : ∑ l ∈ D.Ls, ((Nn : ℝ) / (D.f * l) + 1) ≤ N * H / D.f + L) (hH1 : 1 ≤ H)
    (hM : 0 < M) (hNpos : 0 < N) (hL : 0 < L) (hR : 0 < R) (hf : (0 : ℝ) < D.f)
    (hx : x = M * N) (hx1 : 1 ≤ x)
    (he1 : D.f * L * R / M ≤ x ^ (σ - 7 / 200))
    (he2 : (D.f : ℝ) ^ 2 * L ^ 2 * R / x ≤ x ^ (σ - 7 / 200 - ε)) (hε : 0 ≤ ε) :
    Real.sqrt (M * L * ‖D.FABpart (fun k => k ≠ 1)‖) ≤
      x / D.f * (2 * Real.sqrt (V * T * H) * x ^ (-((7 / 200 - σ) / 2))) := by
  have hV0 : 0 ≤ V := le_trans (norm_nonneg _) (hV 0 0 0)
  have hT0 : 0 ≤ T := le_trans (Finset.sum_nonneg (fun r2 _ => by positivity)) hT
  have hx0 : 0 < x := by linarith
  have hcount := D.FAB_kgt1_count hV hN hNcard hC1 hsupp
  have hS0 : 0 ≤ ∑ r2 ∈ D.R2, (r2.divisors.card : ℝ) / Nat.totient r2 :=
    Finset.sum_nonneg (fun r2 _ => by positivity)
  have hcount' : ‖D.FABpart (fun k => k ≠ 1)‖ ≤
      V * T * H * (R * N ^ 2 / D.f + L * R * N) := by
    refine hcount.trans ?_
    rw [hNn] at *
    have hsumL : 0 ≤ ∑ l ∈ D.Ls, ((N : ℝ) / (D.f * l) + 1) := by
      rw [← hNn]; exact Finset.sum_nonneg (fun l _ => by positivity)
    calc V * ((D.R1.card : ℝ) * (∑ r2 ∈ D.R2, (r2.divisors.card : ℝ) / Nat.totient r2) *
          (N * ∑ l ∈ D.Ls, ((N : ℝ) / (D.f * l) + 1)))
        ≤ V * (R * T * (N * (N * H / D.f + L))) := by
          gcongr
      _ ≤ V * T * H * (R * N ^ 2 / D.f + L * R * N) := by
          have : R * T * (N * (N * H / D.f + L)) ≤ T * H * (R * N ^ 2 / D.f + L * R * N) := by
            have e : T * H * (R * N ^ 2 / D.f + L * R * N) - R * T * (N * (N * H / D.f + L)) =
                T * L * R * N * (H - 1) := by field_simp; ring
            have : 0 ≤ T * L * R * N * (H - 1) := by
              have := sub_nonneg.2 hH1; positivity
            linarith
          calc V * (R * T * (N * (N * H / D.f + L))) ≤
              V * (T * H * (R * N ^ 2 / D.f + L * R * N)) := mul_le_mul_of_nonneg_left this hV0
            _ = _ := by ring
  have hAB := AB2_cauchy (L := L) (R := R) hM hNpos hL hR hf
  rw [← hx] at hAB
  have hs1 : Real.sqrt (D.f * L * R / M) ≤ x ^ ((σ - 7 / 200) / 2) := by
    rw [Real.sqrt_le_left (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    push_cast; ring_nf; ring_nf at he1; exact he1
  have hs2 : (D.f : ℝ) * L * Real.sqrt (R / x) ≤ x ^ ((σ - 7 / 200) / 2) := by
    have e : (D.f : ℝ) * L * Real.sqrt (R / x) = Real.sqrt ((D.f : ℝ) ^ 2 * L ^ 2 * R / x) := by
      rw [show (D.f : ℝ) ^ 2 * L ^ 2 * R / x = (D.f * L) ^ 2 * (R / x) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    have hpow : (x ^ ((σ - 7 / 200) / 2)) ^ 2 = x ^ (σ - 7 / 200) := by
      rw [← Real.rpow_mul_natCast hx0.le]; congr 1; push_cast; ring
    rw [e, Real.sqrt_le_left (by positivity), hpow]
    refine he2.trans (Real.rpow_le_rpow_of_exponent_le hx1 ?_)
    linarith
  have hsum : Real.sqrt (D.f * L * R / M) + D.f * L * Real.sqrt (R / x) ≤
      2 * x ^ (-((7 / 200 - σ) / 2)) := by
    rw [show -((7 / 200 - σ) / 2) = (σ - 7 / 200) / 2 by ring]; linarith
  calc Real.sqrt (M * L * ‖D.FABpart (fun k => k ≠ 1)‖)
      ≤ Real.sqrt (M * L * (V * T * H * (R * N ^ 2 / D.f + L * R * N))) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hcount' (by positivity))
    _ = Real.sqrt (V * T * H) * Real.sqrt (M * L * (R * N ^ 2 / D.f + L * R * N)) := by
        rw [← Real.sqrt_mul (by positivity)]; ring_nf
    _ ≤ Real.sqrt (V * T * H) * (x / D.f * (Real.sqrt (D.f * L * R / M) +
          D.f * L * Real.sqrt (R / x))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        rw [hx] at hAB ⊢; exact hAB
    _ ≤ Real.sqrt (V * T * H) * (x / D.f * (2 * x ^ (-((7 / 200 - σ) / 2)))) := by
        gcongr
    _ = _ := by ring

/-! ### Cleanup-type and near-diagonal cells -/

/-- **(AA.1)-shape cell bound**: a physical count `W (MN²/(f²Lz₀) + MN/f)` with
`z₀ ≥ x^{η₀}`, `fL/N ≤ x^{-κ₁}` gives `√(ML · piece) ≤ (x/f) √W (x^{-η₀/2} + x^{-κ₁/2})`. -/
theorem aaShape_cell_bound {M N L f z0 W piece x η0 κ1 : ℝ} (hM : 0 < M) (hN : 0 < N)
    (hL : 0 < L) (hf : 0 < f) (hz : 0 < z0) (hW : 0 ≤ W) (hx : x = M * N) (hx1 : 1 ≤ x)
    (hcount : piece ≤ W * (M * N ^ 2 / (f ^ 2 * L * z0) + M * N / f))
    (hz0 : x ^ η0 ≤ z0) (hfL : f * L / N ≤ x ^ (-κ1)) :
    Real.sqrt (M * L * piece) ≤
      x / f * (Real.sqrt W * (x ^ (-(η0 / 2)) + x ^ (-(κ1 / 2)))) := by
  have hx0 : 0 < x := by linarith
  have h1 : Real.sqrt (M * L * piece) ≤
      Real.sqrt W * Real.sqrt (M * L * (M * N ^ 2 / (f ^ 2 * L * z0) + M * N / f)) := by
    rw [← Real.sqrt_mul hW]
    exact Real.sqrt_le_sqrt (by nlinarith [mul_pos hM hL])
  have h2 := AA1_cauchy hM hN hL hf hz
  rw [← hx] at h2
  have h3 : 1 / Real.sqrt z0 ≤ x ^ (-(η0 / 2)) := by
    rw [one_div, ← Real.sqrt_inv, Real.sqrt_le_left (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul hx0.le, show -(η0 / 2) * ((2 : ℕ) : ℝ) = -η0 by push_cast; ring,
      Real.rpow_neg hx0.le]
    exact inv_anti₀ (by positivity) hz0
  have h4 : Real.sqrt (f * L / N) ≤ x ^ (-(κ1 / 2)) := by
    rw [Real.sqrt_le_left (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hx0.le,
      show -(κ1 / 2) * ((2 : ℕ) : ℝ) = -κ1 by push_cast; ring]
    exact hfL
  calc Real.sqrt (M * L * piece) ≤ _ := h1
    _ ≤ Real.sqrt W * (x / f * (1 / Real.sqrt z0 + Real.sqrt (f * L / N))) :=
        mul_le_mul_of_nonneg_left (by rw [hx] at h2 ⊢; exact h2) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt W * (x / f * (x ^ (-(η0 / 2)) + x ^ (-(κ1 / 2)))) := by gcongr
    _ = _ := by ring

/-- **Near-diagonal cell bound**: a count `W MN²/(f²LK)` gives `(x/f) √(W/K)`. -/
theorem nearDiag_cell_bound {M N L f K W piece : ℝ} (hM : 0 < M) (hN : 0 < N) (hL : 0 < L)
    (hf : 0 < f) (hK : 0 < K) (hW : 0 ≤ W)
    (hcount : piece ≤ W * (M * N ^ 2 / (f ^ 2 * L * K))) :
    Real.sqrt (M * L * piece) ≤ M * N / f * (Real.sqrt W * (1 / Real.sqrt K)) := by
  have h1 : Real.sqrt (M * L * piece) ≤
      Real.sqrt W * Real.sqrt (M * L * (M * N ^ 2 / (f ^ 2 * L * K))) := by
    rw [← Real.sqrt_mul hW]
    exact Real.sqrt_le_sqrt (by nlinarith [mul_pos hM hL])
  rw [nearDiag_cauchy hM hN hL hf hK] at h1
  calc Real.sqrt (M * L * piece) ≤ _ := h1
    _ = _ := by ring

end Erdos287.SourceChain
