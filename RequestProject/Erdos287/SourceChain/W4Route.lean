import RequestProject.Erdos287.SourceChain.ActualAtom
import RequestProject.Erdos287.SourceChain.SpectralExponent

/-!
# Erdős #287 — actual atom → positive `W₄`: source algebra, narrow providers and ledgers

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**
`AstraActualAtomW4 = PaperCandidate`, `V101ActualAtomW4 = PaperCandidate`,
`IndependentAudit = Pending` (documentation only).

Kernel-proved:

* `source_to_W4` — first Cauchy + representation multiplicity: for one-bounded outer coefficients
  and an inner sum depending on the outer variable only through `π(ω) = (b', z, k)`,
  `|∑_ω a_ω G(π ω)|² ≤ #Ω · m · ∑_{β} |G β|²`, where `m` bounds the fibres of `π`.
* `W4` — the positive square (a weighted sum of squared norms; no bound encoded in it),
  `W4_nonneg`, `fixedA_domination` (the positive-stage map `b' = A₀ b`, injective, only applied
  to the already-formed positive square).
* `cauchy_prefactor`, `cauchy_prefactor_bound` — `(QR²S²)⁻² · N²R²S/f = N²/(fQ²R²S³)`, with the
  regressions `regr_drop_inv_f`, `regr_Q_not_Q2`, `regr_q_independent`.
* `pascadiInner` — the **audited** Pascadi term `FC² + B₀CS² + FCHS`; `regr_old_FHS` shows the
  superseded `FC² + B₀CS² + FHS` is a different function (so it cannot be substituted), and
  `pascadiInner_ge_old` that the audited term dominates it for `C ≥ 1`.
* Three **separate** narrow providers `W4DiagEstimate`, `W4RamEstimate`, `W4SpecEstimate`
  (diagonal, Ramanujan, spectral) and `W4_bound_of_pieces` combining them.
* `packet_exponent` — `|K| ≤ C₀ f^κ N²/(Q x^ε)`, `F^♯ = (M/f)K`, `𝓑 ≤ MQL`, `x = MN` ⟹
  `√(𝓑|F^♯|) ≤ (x/f) f^{(κ+1)/2} x^{-ε/2} √(C₀L)`; instantiated as `astra_packet_391`
  (`κ = 263/128 ⟹ 391/256`) and `v101_packet_775` (`κ = 647/128 ⟹ 775/256`).
* `astra_strong_to_weak` — `f^{199/128} x^{-3ε+ρ₀} ≤ f^{263/128} x^{-ε}` when `ρ₀ ≤ 2ε`.
* `astra_kernel_ledger`, `v101_kernel_ledger` — the exponent decompositions
  `199/128 = 3/2 + 7/128`, `263/128 = 2 + 7/128`, `647/128 = 4 + 1 + 7/128`.
-/

open scoped BigOperators
open Finset

namespace Erdos287.SourceChain

/-! ### Source → positive `W₄` (first Cauchy + multiplicity) -/

/-- **First Cauchy + representation multiplicity.** -/
theorem source_to_W4 {α β : Type*} [DecidableEq β] (Ω : Finset α) (π : α → β) (a : α → ℂ)
    (G : β → ℂ) (m : ℕ) (ha : ∀ ω ∈ Ω, ‖a ω‖ ≤ 1)
    (hm : ∀ b, (Ω.filter (fun ω => π ω = b)).card ≤ m) :
    ‖∑ ω ∈ Ω, a ω * G (π ω)‖ ^ 2 ≤ Ω.card * (m * ∑ b ∈ Ω.image π, ‖G b‖ ^ 2) := by
  have h1 : ‖∑ ω ∈ Ω, a ω * G (π ω)‖ ≤ ∑ ω ∈ Ω, ‖G (π ω)‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun ω hω => ?_))
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (ha ω hω)
  have h2 : (∑ ω ∈ Ω, ‖G (π ω)‖) ^ 2 ≤ Ω.card * ∑ ω ∈ Ω, ‖G (π ω)‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h3 : ∑ ω ∈ Ω, ‖G (π ω)‖ ^ 2 ≤ m * ∑ b ∈ Ω.image π, ‖G b‖ ^ 2 := by
    rw [Finset.sum_comp (fun b => ‖G b‖ ^ 2) π, Finset.mul_sum]
    refine Finset.sum_le_sum (fun b _ => ?_)
    rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm b) (sq_nonneg _)
  calc ‖∑ ω ∈ Ω, a ω * G (π ω)‖ ^ 2 ≤ (∑ ω ∈ Ω, ‖G (π ω)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)

/-- **The positive square** `𝒲₄ = ∑_{β ∈ T} w(β) |inner(β)|²` (definition only). -/
noncomputable def W4 {β : Type*} (T : Finset β) (w : β → ℝ) (inner : β → ℂ) : ℝ :=
  ∑ b ∈ T, w b * ‖inner b‖ ^ 2

theorem W4_nonneg {β : Type*} (T : Finset β) (w : β → ℝ) (inner : β → ℂ)
    (hw : ∀ b ∈ T, 0 ≤ w b) : 0 ≤ W4 T w inner :=
  Finset.sum_nonneg (fun b hb => mul_nonneg (hw b hb) (sq_nonneg _))

/-- `source_to_W4` lands in `𝒲₄` with unit weights. -/
theorem source_to_W4' {α β : Type*} [DecidableEq β] (Ω : Finset α) (π : α → β) (a : α → ℂ)
    (G : β → ℂ) (m : ℕ) (ha : ∀ ω ∈ Ω, ‖a ω‖ ≤ 1)
    (hm : ∀ b, (Ω.filter (fun ω => π ω = b)).card ≤ m) :
    ‖∑ ω ∈ Ω, a ω * G (π ω)‖ ^ 2 ≤ Ω.card * (m * W4 (Ω.image π) (fun _ => 1) G) := by
  simpa [W4] using source_to_W4 Ω π a G m ha hm

/-- **Fixed-`A` positive domination** `W_{A₀}(B₀,C₀,F₀) ≤ W₁(A₀B₀,C₀,F₀)`: an injective
positive-stage map `ι` (e.g. `b ↦ A₀ b`) with `w ≤ w₁ ∘ ι`, `inner = inner₁ ∘ ι` and
`ι(T) ⊆ T₁` gives domination, provided the target weights are non-negative.  It concerns the
already-formed positive square only. -/
theorem fixedA_domination {β γ : Type*} [DecidableEq γ] (T : Finset β) (T1 : Finset γ)
    (ι : β → γ) (hinj : Set.InjOn ι T) (hsub : T.image ι ⊆ T1) (w : β → ℝ) (w1 : γ → ℝ)
    (inner : β → ℂ) (inner1 : γ → ℂ) (hw : ∀ b ∈ T, w b ≤ w1 (ι b))
    (hw1 : ∀ g ∈ T1, 0 ≤ w1 g) (hin : ∀ b ∈ T, inner b = inner1 (ι b)) :
    W4 T w inner ≤ W4 T1 w1 inner1 := by
  unfold W4
  calc ∑ b ∈ T, w b * ‖inner b‖ ^ 2 ≤ ∑ b ∈ T, w1 (ι b) * ‖inner1 (ι b)‖ ^ 2 :=
        Finset.sum_le_sum (fun b hb => by
          rw [hin b hb]; exact mul_le_mul_of_nonneg_right (hw b hb) (sq_nonneg _))
    _ = ∑ g ∈ T.image ι, w1 g * ‖inner1 g‖ ^ 2 := (Finset.sum_image (f := fun g => w1 g * ‖inner1 g‖ ^ 2) hinj).symm
    _ ≤ ∑ g ∈ T1, w1 g * ‖inner1 g‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g hg _ =>
          mul_nonneg (hw1 g hg) (sq_nonneg _))

/-- The multiplication map `b ↦ A₀ b` is injective for `A₀ ≠ 0`. -/
theorem mulLeft_injOn {A0 : ℤ} (hA : A0 ≠ 0) (T : Finset ℤ) :
    Set.InjOn (fun b => A0 * b) T := fun _ _ _ _ h => mul_left_cancel₀ hA h

/-! ### The Cauchy prefactor `N²/(fQ²R²S³)` -/

theorem cauchy_prefactor {N Q R S f : ℝ} (hQ : Q ≠ 0) (hR : R ≠ 0) (hS : S ≠ 0) (hf : f ≠ 0) :
    (1 / (Q * R ^ 2 * S ^ 2)) ^ 2 * (N ^ 2 * R ^ 2 * S / f) = N ^ 2 / (f * Q ^ 2 * R ^ 2 * S ^ 3) := by
  field_simp

/-- **Load-bearing Cauchy prefactor.**  `K = (QR²S²)⁻¹ Σ`, `|Σ|² ≤ #Ω · 𝒲₃`,
`#Ω ≤ N²R²S/f` ⟹ `|K|² ≤ N²/(fQ²R²S³) · 𝒲₃`. -/
theorem cauchy_prefactor_bound {N Q R S f K Sg W3 card : ℝ} (hQ : 0 < Q) (hR : 0 < R)
    (hS : 0 < S) (hf : 0 < f) (hW3 : 0 ≤ W3) (hK : K = 1 / (Q * R ^ 2 * S ^ 2) * Sg)
    (hSg : Sg ^ 2 ≤ card * W3) (hcard : card ≤ N ^ 2 * R ^ 2 * S / f) :
    K ^ 2 ≤ N ^ 2 / (f * Q ^ 2 * R ^ 2 * S ^ 3) * W3 := by
  rw [hK, mul_pow, ← cauchy_prefactor hQ.ne' hR.ne' hS.ne' hf.ne']
  have hc : 0 ≤ (1 / (Q * R ^ 2 * S ^ 2)) ^ 2 := sq_nonneg _
  calc (1 / (Q * R ^ 2 * S ^ 2)) ^ 2 * Sg ^ 2 ≤ (1 / (Q * R ^ 2 * S ^ 2)) ^ 2 * (card * W3) :=
        mul_le_mul_of_nonneg_left hSg hc
    _ ≤ (1 / (Q * R ^ 2 * S ^ 2)) ^ 2 * (N ^ 2 * R ^ 2 * S / f * W3) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hW3) hc
    _ = _ := by ring

/-- Regression: dropping the `1/f` density changes the prefactor (`f = 2`). -/
theorem regr_drop_inv_f :
    (1 : ℝ) ^ 2 / (2 * 1 ^ 2 * 1 ^ 2 * 1 ^ 3) ≠ 1 ^ 2 / (1 ^ 2 * 1 ^ 2 * 1 ^ 3) := by norm_num

/-- Regression: replacing `Q²` by `Q` changes the prefactor (`Q = 2`). -/
theorem regr_Q_not_Q2 :
    (1 : ℝ) ^ 2 / (1 * 2 ^ 2 * 1 ^ 2 * 1 ^ 3) ≠ 1 ^ 2 / (1 * 2 * 1 ^ 2 * 1 ^ 3) := by norm_num

/-- Regression: treating `q` as an independent outer variable multiplies the outer count by `Q`,
which does not give the stated prefactor (`Q = 2`). -/
theorem regr_q_independent :
    (1 / ((2 : ℝ) * 1 ^ 2 * 1 ^ 2)) ^ 2 * (1 ^ 2 * 1 ^ 2 * 1 * 2 / 1) ≠
      1 ^ 2 / (1 * 2 ^ 2 * 1 ^ 2 * 1 ^ 3) := by norm_num

/-! ### The audited Pascadi term and the three narrow `W₄` providers -/

/-- **Audited Pascadi term** `FC² + B₀CS² + FCHS`. -/
def pascadiInner (F C B0 S H : ℝ) : ℝ := F * C ^ 2 + B0 * C * S ^ 2 + F * C * H * S

/-- The superseded transcription `FC² + B₀CS² + FHS` (kept only for the regression). -/
def pascadiInnerOld (F C B0 S H : ℝ) : ℝ := F * C ^ 2 + B0 * C * S ^ 2 + F * H * S

/-- **Regression**: the old `FHS` term is a different function, so it cannot feed the chain. -/
theorem regr_old_FHS : pascadiInner 1 2 0 1 1 ≠ pascadiInnerOld 1 2 0 1 1 := by
  unfold pascadiInner pascadiInnerOld; norm_num

/-- For `C ≥ 1` (and non-negative data) the audited term dominates the old one:
`pascadiInnerOld ≤ pascadiInner`.  Hence a (valid) bound by the smaller old right-hand side
would imply the corresponding bound by the audited one, but **not** conversely; this only orders
the right-hand sides and says nothing about the validity of an estimate with the old term. -/
theorem pascadiInner_ge_old {F C B0 S H : ℝ} (hF : 0 ≤ F) (hC : 1 ≤ C) (hS : 0 ≤ S)
    (hH : 0 ≤ H) : pascadiInnerOld F C B0 S H ≤ pascadiInner F C B0 S H := by
  unfold pascadiInner pascadiInnerOld
  have : F * H * S ≤ F * C * H * S := by
    have h0 : 0 ≤ F * H * S := by positivity
    nlinarith
  linarith

/-- The spectral right-hand side with the audited term. -/
noncomputable def specRHS (Λ T F C B0 S H : ℝ) : ℝ :=
  Λ * T ^ ((7 : ℝ) / 64) * (1 + C * Real.sqrt F / (S ^ ((3 : ℝ) / 2) * H)) ^ ((7 : ℝ) / 32) *
    (H * S ^ 2 * Real.sqrt F * Real.sqrt (pascadiInner F C B0 S H))

/-- **Narrow provider 1 (diagonal)**: `W_diag ≤ Λ · S H F C B₀`. -/
def W4DiagEstimate (Wdiag Λ S H F C B0 : ℝ) : Prop := Wdiag ≤ Λ * (S * H * F * C * B0)

/-- **Narrow provider 2 (Ramanujan)**: `W_Ram ≤ Λ · S² H² F B₀`. -/
def W4RamEstimate (Wram Λ S H F B0 : ℝ) : Prop := Wram ≤ Λ * (S ^ 2 * H ^ 2 * F * B0)

/-- **Narrow provider 3 (spectral)**, with the audited Pascadi term and the `T^{7/64}`
exceptional loss. -/
def W4SpecEstimate (Wspec Λ T F C B0 S H : ℝ) : Prop := Wspec ≤ specRHS Λ T F C B0 S H

/-- The three providers combine (no hidden fourth input beyond the structural split
`𝒲₄ ≤ W_diag + W_Ram + W_spec`). -/
theorem W4_bound_of_pieces {W Wd Wr Ws Λ T F C B0 S H : ℝ} (hsplit : W ≤ Wd + Wr + Ws)
    (hd : W4DiagEstimate Wd Λ S H F C B0) (hr : W4RamEstimate Wr Λ S H F B0)
    (hs : W4SpecEstimate Ws Λ T F C B0 S H) :
    W ≤ Λ * (S * H * F * C * B0) + Λ * (S ^ 2 * H ^ 2 * F * B0) + specRHS Λ T F C B0 S H := by
  unfold W4DiagEstimate W4RamEstimate W4SpecEstimate at *; linarith

/-! ### `T_H` propagation: `T^{7/64}` inside `𝒲₄` becomes `T^{7/128}` after the square root -/

theorem TH_sqrt_propagation {T W0 : ℝ} (hT : 0 ≤ T) :
    Real.sqrt (T ^ ((7 : ℝ) / 64) * W0) = T ^ ((7 : ℝ) / 128) * Real.sqrt W0 := by
  rw [Real.sqrt_mul (Real.rpow_nonneg hT _), Real.sqrt_eq_rpow, ← Real.rpow_mul hT]
  norm_num

/-- `T_H(ω) ≤ Af` gives `T_H^{7/128} ≤ (Af)^{7/128}`. -/
theorem TH_le_Af_power {T A f : ℝ} (hT : 0 ≤ T) (hle : T ≤ A * f) :
    T ^ ((7 : ℝ) / 128) ≤ (A * f) ^ ((7 : ℝ) / 128) :=
  Real.rpow_le_rpow hT hle (by norm_num)

/-! ### Packet exponents -/

/-- **Generic packet exponent.** -/
theorem packet_exponent {M N Q f x K Fsh Bc C0 L κ ε : ℝ} (hM : 0 < M) (hN : 0 < N)
    (hQ : 0 < Q) (hf : 0 < f) (hC0 : 0 ≤ C0) (hL : 0 ≤ L) (hx : x = M * N)
    (hK : |K| ≤ C0 * f ^ κ * N ^ 2 / Q * x ^ (-ε)) (hF : Fsh = M / f * K)
    (hB : Bc ≤ M * Q * L) :
    Real.sqrt (Bc * |Fsh|) ≤
      x / f * (f ^ ((κ + 1) / 2) * x ^ (-(ε / 2)) * Real.sqrt (C0 * L)) := by
  have hx0 : 0 < x := by rw [hx]; positivity
  have hfa : |Fsh| ≤ M / f * (C0 * f ^ κ * N ^ 2 / Q * x ^ (-ε)) := by
    rw [hF, abs_mul, abs_of_pos (by positivity : 0 < M / f)]
    exact mul_le_mul_of_nonneg_left hK (by positivity)
  have hprod : Bc * |Fsh| ≤ (x / f * (f ^ ((κ + 1) / 2) * x ^ (-(ε / 2)) * Real.sqrt (C0 * L))) ^ 2 := by
    calc Bc * |Fsh| ≤ (M * Q * L) * (M / f * (C0 * f ^ κ * N ^ 2 / Q * x ^ (-ε))) :=
          mul_le_mul hB hfa (abs_nonneg _) (by positivity)
      _ = (x / f) ^ 2 * (f * f ^ κ) * x ^ (-ε) * (C0 * L) := by
          rw [hx]; field_simp
      _ = _ := by
          have e1 : f * f ^ κ = (f ^ ((κ + 1) / 2)) ^ 2 := by
            rw [← Real.rpow_mul_natCast hf.le,
              show (κ + 1) / 2 * ((2 : ℕ) : ℝ) = 1 + κ by push_cast; ring,
              Real.rpow_add hf, Real.rpow_one]
          have e2 : x ^ (-ε) = (x ^ (-(ε / 2))) ^ 2 := by
            rw [← Real.rpow_mul_natCast hx0.le]; congr 1; push_cast; ring
          rw [e1, e2, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hC0 hL)]
          ring
  calc Real.sqrt (Bc * |Fsh|) ≤ Real.sqrt ((x / f * (f ^ ((κ + 1) / 2) * x ^ (-(ε / 2)) *
        Real.sqrt (C0 * L))) ^ 2) := Real.sqrt_le_sqrt hprod
    _ = _ := Real.sqrt_sq (by positivity)

/-- **Astra final packet exponent `391/256`** from the (weaker) kernel target `f^{263/128}`. -/
theorem astra_packet_391 {M N Q f x K Fsh Bc C0 L ε : ℝ} (hM : 0 < M) (hN : 0 < N)
    (hQ : 0 < Q) (hf : 0 < f) (hC0 : 0 ≤ C0) (hL : 0 ≤ L) (hx : x = M * N)
    (hK : |K| ≤ C0 * f ^ ((263 : ℝ) / 128) * N ^ 2 / Q * x ^ (-ε)) (hF : Fsh = M / f * K)
    (hB : Bc ≤ M * Q * L) :
    Real.sqrt (Bc * |Fsh|) ≤ x / f * (f ^ ((391 : ℝ) / 256) * x ^ (-(ε / 2)) * Real.sqrt (C0 * L)) := by
  have h := packet_exponent hM hN hQ hf hC0 hL hx hK hF hB
  rwa [show ((263 : ℝ) / 128 + 1) / 2 = 391 / 256 by norm_num] at h

/-- **V101 final packet exponent `775/256`** from the kernel exponent `647/128`. -/
theorem v101_packet_775 {M N Q f x K Fsh Bc C0 L ε : ℝ} (hM : 0 < M) (hN : 0 < N)
    (hQ : 0 < Q) (hf : 0 < f) (hC0 : 0 ≤ C0) (hL : 0 ≤ L) (hx : x = M * N)
    (hK : |K| ≤ C0 * f ^ ((647 : ℝ) / 128) * N ^ 2 / Q * x ^ (-ε)) (hF : Fsh = M / f * K)
    (hB : Bc ≤ M * Q * L) :
    Real.sqrt (Bc * |Fsh|) ≤ x / f * (f ^ ((775 : ℝ) / 256) * x ^ (-(ε / 2)) * Real.sqrt (C0 * L)) := by
  have h := packet_exponent hM hN hQ hf hC0 hL hx hK hF hB
  rwa [show ((647 : ℝ) / 128 + 1) / 2 = 775 / 256 by norm_num] at h

/-- **Astra strong ⟹ weak target**: for `f ≥ 1`, `x ≥ 1`, `ρ₀ ≤ 2ε`,
`f^{199/128} x^{-3ε+ρ₀} ≤ f^{263/128} x^{-ε}`. -/
theorem astra_strong_to_weak {f x ε ρ0 : ℝ} (hf : 1 ≤ f) (hx : 1 ≤ x) (hρ : ρ0 ≤ 2 * ε) :
    f ^ ((199 : ℝ) / 128) * x ^ (-3 * ε + ρ0) ≤ f ^ ((263 : ℝ) / 128) * x ^ (-ε) := by
  have h1 : f ^ ((199 : ℝ) / 128) ≤ f ^ ((263 : ℝ) / 128) :=
    Real.rpow_le_rpow_of_exponent_le hf (by norm_num)
  have h2 : x ^ (-3 * ε + ρ0) ≤ x ^ (-ε) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- Astra kernel ledger: `199/128 = 3/2 + 7/128` (phase complexity `7/128`), weak target
`263/128 = 2 + 7/128`. -/
theorem astra_kernel_ledger :
    (199 : ℚ) / 128 = 3 / 2 + 7 / 128 ∧ (263 : ℚ) / 128 = 2 + 7 / 128 ∧
      ((263 : ℚ) / 128 + 1) / 2 = 391 / 256 := by norm_num

/-- V101 kernel ledger: residue atomisation `4`, Fourier enlargement `1`, phase complexity
`7/128`: `647/128`; final `775/256`. -/
theorem v101_kernel_ledger :
    (4 : ℚ) + 1 + 7 / 128 = 647 / 128 ∧ ((647 : ℚ) / 128 + 1) / 2 = 775 / 256 := by norm_num

/-- The Astra route is strictly stronger than V101 at both levels. -/
theorem astra_beats_v101 : (263 : ℚ) / 128 < 647 / 128 ∧ (391 : ℚ) / 256 < 775 / 256 := by
  norm_num

end Erdos287.SourceChain
