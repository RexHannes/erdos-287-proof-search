import RequestProject.Erdos287.SourceChain.Physical.TypeII.UremFamilyCellFull

/-!
# Erdős #287 — the full actual Urem estimate `O_A(X/(log X)^A)`

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

Instantiation of `cell_urem_polylog_full` at the actual physical parameters, with every
parameter-range hypothesis discharged from the source:

* `H_le` — the number of high-prime boxes satisfies `H ≤ T^{11} + 1` for every `X > 1`, so the atom
  weight sum `∑_{J ≤ T²} H^J 3^J` is bounded by a constant `Wbound T` depending only on `T`;
* `physUrem_Gamma_zero` — packets with `Γ_ξ = 0` contribute nothing (so only the `Γ_ξ ≠ 0`
  packets, for which `f_ξ ≤ a_j W X^{2δ_s}`, are counted; no packet multiplicity is lost);
* `add_betaTop` — `e_c + E = ∑_i e_i + 6`;
* the base cap `F = ⌊a_max W X^{2δ_s}⌋`, the atom-band cap `2^{n₀}` with
  `n₀ = log₂ ⌊N X^{-κ}⌋ + 1`, the modulus cutoff (via `modulus_range_eventually`), the scale
  conditions, and the non-shortness `κ log(64X) ≤ log(2^{e_c} - 1/2)` are all **proved** for
  `X ≥ X₀`.

The remaining hypotheses are: Maynard I, Lemma 13.8 (`MaynardLemma13_8`, published, not
formalized), the interval Siegel–Walfisz input for the two base rough sequences at the scale of
`α` (`IntervalSWAt`, discussed in `ERDOS287_UREM_PAID_REPORT.md`), and fixed source data
(`k ≤ k₀`, the tensor bound `Bf` with `(V Bf^k)² k² ≤ CaMax`, `a_i ≤ a_max`, the test-function
support `δ_s` with `2δ_s < κ`, and the scalar level `K ≤ X`).

* `actual_cell_urem` — one actual critical cell: `∑_ξ |physUrem_ξ| ≤ C X/(log X)^A`.
* `actual_urem_total` — **all actual critical cells** `(j, e, c)` in the Heath–Brown box
  `[0, E₀)^6` with `2^{E₀} ≤ X`: total `≤ C X/(log X)^A`, for every `A > 0`.
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Physical.TypeII.UremFamily

open Erdos287.Physical Erdos287.Physical.TypeII Erdos287.Physical.Sieve
  Erdos287.Physical.Sieve.ScalarParams Erdos287.Physical.Factor

/-- **The number of high-prime boxes is bounded in terms of `T` alone**: `H ≤ T^{11} + 1`. -/
theorem H_le {S : ScalarParams} (hS : S.Good) : S.H ≤ S.T ^ 11 + 1 := by
  have hT : (2 : ℝ) ≤ S.T := by exact_mod_cast hS.T_two
  have hT0 : (0 : ℝ) < S.T := by linarith
  have hDint := Dint_gt_one hS
  have hex : Real.sqrt S.Dint < S.boxEnd (S.T ^ 11 + 1) := by
    unfold boxEnd u0
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith)]
    apply Real.rpow_lt_rpow_of_exponent_lt hDint
    -- `1/2 < ε₀² (1+τ)^{T^{11}+1}`
    have he : S.eps0 = 1 / (S.T : ℝ) := rfl
    have hτ : S.tau = S.eps0 ^ 9 := rfl
    have he0 : 0 < S.eps0 := by rw [he]; positivity
    have hτ0 : 0 ≤ S.tau := by rw [hτ]; positivity
    have hbern : 1 + ((S.T ^ 11 + 1 : ℕ) : ℝ) * S.tau ≤ (1 + S.tau) ^ (S.T ^ 11 + 1) :=
      one_add_mul_le_pow (by linarith) _
    have hkey : S.eps0 ^ 2 * (((S.T ^ 11 + 1 : ℕ) : ℝ) * S.tau) > 1 / 2 := by
      rw [hτ, he]
      push_cast
      have : (1 / (S.T : ℝ)) ^ 2 * (((S.T : ℝ) ^ 11 + 1) * (1 / (S.T : ℝ)) ^ 9) =
          1 + 1 / (S.T : ℝ) ^ 11 := by
        field_simp
      rw [this]
      have : 0 < 1 / (S.T : ℝ) ^ 11 := by positivity
      linarith
    have he2 : 0 ≤ S.eps0 ^ 2 := by positivity
    calc (1 : ℝ) / 2 < S.eps0 ^ 2 * (((S.T ^ 11 + 1 : ℕ) : ℝ) * S.tau) := hkey
      _ ≤ S.eps0 ^ 2 * (1 + S.tau) ^ (S.T ^ 11 + 1) := by
          apply mul_le_mul_of_nonneg_left _ he2; linarith
  have hexists : ∃ j, Real.sqrt S.Dint < S.boxEnd j := ⟨_, hex⟩
  unfold H
  rw [dif_pos hexists]
  exact Nat.find_min' hexists hex

/-- The atom-weight constant depending only on `T`. -/
def Wbound (T : ℕ) : ℝ := ∑ J ∈ range (T ^ 2 + 1), ((T ^ 11 + 1 : ℕ) : ℝ) ^ J * 3 ^ J

lemma atomWeightSum_le {S : ScalarParams} (hS : S.Good) :
    (∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J) ≤ Wbound S.T := by
  unfold Wbound
  refine sum_le_sum (fun J _ => ?_)
  have : (S.H : ℝ) ≤ ((S.T ^ 11 + 1 : ℕ) : ℝ) := by exact_mod_cast H_le hS
  gcongr

/-- Packets with `Γ_ξ = 0` contribute nothing to `physUrem`. -/
lemma physUrem_Gamma_zero (S : ScalarParams) (δ N : ℝ) (f c A : ℕ) (B : ℤ) (K K' : ℕ)
    (α β : ArithmeticFunction ℝ) : physUrem S δ N 0 f c A B K K' α β = 0 := by
  unfold physUrem physCoefCut physCoefAtom
  simp

/-- `e_c + E = ∑_i e_i + 6`, `E = betaTop e c`. -/
lemma add_betaTop (e : Fin 6 → ℕ) (c : Fin 6) : e c + betaTop e c = ∑ i, e i + 6 := by
  unfold betaTop
  rw [sum_add_distrib, sum_const, card_erase_of_mem (mem_univ c), card_univ, Fintype.card_fin,
    ← add_sum_erase univ e (mem_univ c)]
  simp only [smul_eq_mul, mul_one]
  omega

/-- **The physical roughness threshold** `z₀ = X^{1/(log log X)^3}` (source §19). -/
noncomputable def physZ0 (X : ℝ) : ℕ := ⌊X ^ (1 / Real.log (Real.log X) ^ 3)⌋₊

/-- **The Urem estimate for one actual critical cell.**

Fixed data: `k₀`, divisor exponent `b ≥ 2k₀ + 1`, SW constants `cSW`, `T`, `A > 0`,
`0 < κ`, `0 ≤ δ_s` with `2δ_s < κ`, `a_max ≥ 0`, `CaMax`.  Then there are `X₀`, `C` such that for
every `X = S.X ≥ X₀` and all actual data (`P.X = X`, `W = physW X`, presieve `WGood`, `k ≤ k₀`,
slopes `≤ a_max`, test function supported on `∑ t_i ≤ δ_s`, tensor bound `Bf`, `S.T = T` in the
critical regime of `κ`), every packet family `Ξ ⊆ XiAll`, every scalar level `K ≤ X`, and every
actual critical Heath–Brown cell `(j, e, c)` (`X^{3κ} ≤ 2^{e_c} ≤ X^{1/3+κ/2}`, cell meets
`[1, X]`), with the atom coefficients of the critical cell (`δ = κ`, `N = 2^{e_c}`) and any
`K'` covering the cell:
`∑_ξ |physUrem_ξ(alphaSeq, betaSeq)| ≤ C X/(log X)^A`,
provided the interval Siegel–Walfisz input holds at the scale of `α`. -/
theorem actual_cell_urem (hM : MaynardLemma13_8) (k₀ : ℕ) {b : ℕ} (hb : 2 * k₀ + 1 ≤ b)
    (cSW : ℝ → ℝ) (T : ℕ) {Astar κ δs amax CaMax : ℝ} (hA : 0 < Astar) (hκ0 : 0 < κ)
    (hδs : 0 ≤ δs) (hκδ : 2 * δs < κ) (hamax : 0 ≤ amax) :
    ∃ X0 Cfin : ℝ, ∀ (P : PhysData) (S : ScalarParams), X0 ≤ S.X → P.X = S.X →
    P.W = physW S.X → P.WGood → P.k ≤ k₀ → (∀ i, (P.a i : ℝ) ≤ amax) → FSupport P δs →
    ∀ (Bf : ℝ), (∀ v i t, |P.fp v i t| ≤ Bf) → (P.V * Bf ^ P.k) ^ 2 * (P.k : ℝ) ^ 2 ≤ CaMax →
    S.T = T → CritRegime S κ →
    ∀ (Ξ : Finset (Packet P.k)), Ξ ⊆ P.XiAll → ∀ (K K' : ℕ), (K : ℝ) ≤ S.X →
    ∀ (z z₀ j : ℕ) (e : Fin 6 → ℕ) (c : Fin 6), CritCell S κ ((2 : ℝ) ^ e c) →
    (2 : ℝ) ^ (∑ i, e i) ≤ S.X → 4 * 2 ^ e c * 2 ^ betaTop e c ≤ K' →
    IntervalSWAt (roughOne z₀) (alphaScale e c) b cSW →
    IntervalSWAt (roughMu z₀) (alphaScale e c) b cSW →
    ∑ ξ ∈ Ξ, |physUrem S κ ((2 : ℝ) ^ e c) (P.Gamma ξ) (P.f ξ) (P.cRes ξ) (P.A ξ) (P.B ξ) K K'
        (alphaSeq z z₀ j e c) (betaSeq z z₀ j e c)| ≤ Cfin * S.X / Real.log S.X ^ Astar := by
  obtain ⟨C, Cfin, hC⟩ := cell_urem_polylog_full hM k₀ hb cSW (Astar := Astar) (η := κ)
    (Wmax := Wbound T) (CaMax := CaMax) hA hκ0
  obtain ⟨X1, hX12, hX1⟩ := modulus_range_eventually (max C 0) amax δs κ hamax hδs hκδ
  set X2 : ℝ := (128 : ℝ) ^ (1 / κ) with hX2def
  refine ⟨max X1 X2, 64 * max Cfin 0, ?_⟩
  intro P S hX hPX hW hP hk ha hFs Bf hBf hCa hT hcr Ξ hΞ K K' hKX z z₀ j e c hN hcellX hK'
    hsw1 hsw2
  set X := S.X with hXdef
  have hX2 : (2 : ℝ) ≤ X := le_trans hX12 (le_trans (le_max_left _ _) hX)
  have hX0 : 0 < X := by linarith
  have hX1' : 1 < X := by linarith
  -- `X^κ ≥ 128`
  have hXκ : (128 : ℝ) ≤ X ^ κ := by
    have hle : X2 ≤ X := le_trans (le_max_right _ _) hX
    calc (128 : ℝ) = X2 ^ κ := by
          rw [hX2def, ← Real.rpow_mul (by norm_num)]; field_simp; simp
      _ ≤ X ^ κ := Real.rpow_le_rpow (by positivity) hle hκ0.le
  have hlogX : 7 * Real.log 2 ≤ κ * Real.log X := by
    have h := Real.log_le_log (by norm_num) hXκ
    rw [Real.log_rpow hX0] at h
    have : Real.log (128 : ℝ) = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
    linarith
  set N : ℝ := (2 : ℝ) ^ e c with hNdef
  have hκs : κ < 1 / 100000 := hcr.κ_small
  have hNlo : X ^ (3 * κ) ≤ N := hN.N_lo
  have hNhi : N ≤ X ^ (1 / 3 + κ / 2) := hN.N_hi
  have hNX : N ≤ X := hNhi.trans (by
    calc X ^ (1 / 3 + κ / 2) ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1'.le (by linarith)
      _ = X := Real.rpow_one _)
  have hX3κ : (128 : ℝ) ≤ X ^ (3 * κ) := by
    calc (128 : ℝ) ≤ X ^ κ := hXκ
      _ ≤ X ^ (3 * κ) := Real.rpow_le_rpow_of_exponent_le hX1'.le (by linarith)
  have hN128 : (128 : ℝ) ≤ N := hX3κ.trans hNlo
  have hN0 : 0 < N := by linarith
  have hαS : alphaScale e c = N - 1 / 2 := by unfold alphaScale; push_cast; rfl
  -- restrict to packets with `Γ ≠ 0`
  set Ξ' := Ξ.filter (fun ξ => P.Gamma ξ ≠ 0) with hΞ'
  have hsum : ∑ ξ ∈ Ξ, |physUrem S κ N (P.Gamma ξ) (P.f ξ) (P.cRes ξ) (P.A ξ) (P.B ξ) K K'
        (alphaSeq z z₀ j e c) (betaSeq z z₀ j e c)| =
      ∑ ξ ∈ Ξ', |physUrem S κ N (P.Gamma ξ) (P.f ξ) (P.cRes ξ) (P.A ξ) (P.B ξ) K K'
        (alphaSeq z z₀ j e c) (betaSeq z z₀ j e c)| := by
    rw [hΞ']
    refine (sum_filter_of_ne (fun ξ _ hne => ?_)).symm
    intro h0; apply hne; rw [h0, physUrem_Gamma_zero, abs_zero]
  rw [hsum]
  have hΞ'sub : Ξ' ⊆ P.XiAll := (filter_subset _ _).trans hΞ
  -- the base cap
  set Fr : ℝ := amax * physW X * X ^ (2 * δs) with hFr
  have hFr0 : 0 ≤ Fr := by positivity
  set F : ℕ := ⌊Fr⌋₊ with hFdef
  have hF : ∀ ξ ∈ Ξ', P.f ξ ≤ F := by
    intro ξ hξ
    have hΓ : P.Gamma ξ ≠ 0 := (mem_filter.1 hξ).2
    have h1 := f_le_of_Gamma_ne_zero hFs (by rw [hPX]; exact hX1') hΓ
    rw [hPX, hW] at h1
    apply Nat.le_floor
    refine h1.trans ?_
    have : 0 ≤ X ^ (2 * δs) := Real.rpow_nonneg hX0.le _
    rw [hFr]; gcongr; exact ha _
  have hFle : (F : ℝ) ≤ Fr := Nat.floor_le hFr0
  -- the atom band cap
  set Lr : ℝ := N * X ^ (-κ) with hLr
  have hLr1 : 1 ≤ Lr := by
    have h1 : X ^ (3 * κ) * X ^ (-κ) = X ^ (2 * κ) := by
      rw [← Real.rpow_add hX0]; ring_nf
    have h2 : (1 : ℝ) ≤ X ^ (2 * κ) := Real.one_le_rpow hX1'.le (by linarith)
    have h3 : X ^ (3 * κ) * X ^ (-κ) ≤ N * X ^ (-κ) :=
      mul_le_mul_of_nonneg_right hNlo (Real.rpow_nonneg hX0.le _)
    rw [hLr]; linarith
  set m : ℕ := ⌊Lr⌋₊ with hmdef
  have hm1 : 1 ≤ m := Nat.le_floor (by exact_mod_cast hLr1)
  set n0 : ℕ := Nat.log 2 m + 1 with hn0def
  have hmlt : m < 2 ^ n0 := Nat.lt_pow_succ_log_self (by norm_num) m
  have h2n0 : 2 ^ n0 ≤ 2 * m := by
    rw [hn0def, pow_succ]
    have := Nat.pow_log_le_self 2 (show m ≠ 0 by omega)
    omega
  have hl0 : ∀ ξ ∈ Ξ', ∀ J (Pb : Fin J → Fin S.H) (χ : Fin S.Kc → Fin 3) l r,
      physCoefCut S κ N (P.Gamma ξ) (P.f ξ) K J Pb χ l r ≠ 0 → l < 2 ^ n0 := by
    intro ξ _ J Pb χ l r hne
    have hl := coefCut_l_le hcr hN hne
    have : l ≤ m := Nat.le_floor hl
    omega
  have h2n0r : ((2 ^ n0 : ℕ) : ℝ) ≤ 2 * Lr := by
    have : ((2 ^ n0 : ℕ) : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast h2n0
    refine this.trans ?_
    push_cast
    have := Nat.floor_le (show 0 ≤ Lr by linarith)
    linarith
  -- the modulus cutoff
  set Q : ℝ := ((F * 2 ^ n0 : ℕ) : ℝ) with hQdef
  have hQ0 : 0 ≤ Q := Nat.cast_nonneg _
  have hQle : Q ≤ Fr * (2 * N * X ^ (-κ)) := by
    rw [hQdef]; push_cast
    have : ((2 : ℝ) ^ n0) ≤ 2 * Lr := by exact_mod_cast h2n0r
    rw [hLr] at this
    exact mul_le_mul hFle (by linarith) (by positivity) hFr0
  have hcut0 := hX1 X (le_trans (le_max_left _ _) hX) N hNlo hNX Q hQle
  set N' : ℝ := N - 1 / 2 with hN'def
  have hN'pos : 0 < N' := by rw [hN'def]; linarith
  have hlogN'1 : 1 ≤ Real.log N' := by
    rw [Real.le_log_iff_exp_le hN'pos]
    have := Real.exp_one_lt_d9
    rw [hN'def]; linarith
  have hpowle : Real.log N' ^ C ≤ Real.log N' ^ (max C 0) :=
    Real.rpow_le_rpow_of_exponent_le hlogN'1 (le_max_left _ _)
  have hpow0 : 0 < Real.log N' ^ C := Real.rpow_pos_of_pos (by linarith) _
  have hpow1 : 1 ≤ Real.log N' ^ (max C 0) := Real.one_le_rpow hlogN'1 (le_max_right _ _)
  have hcut : ((2 * F * 2 ^ n0 : ℕ) : ℝ) ≤ alphaScale e c / Real.log (alphaScale e c) ^ C := by
    rw [hαS]
    have e1 : ((2 * F * 2 ^ n0 : ℕ) : ℝ) = 2 * Q := by rw [hQdef]; push_cast; ring
    rw [e1]
    refine hcut0.le.trans ?_
    exact div_le_div_of_nonneg_left hN'pos.le hpow0 hpowle
  have hQN : Q ≤ N := by
    have h1 : N' / Real.log N' ^ (max C 0) ≤ N' := div_le_self hN'pos.le hpow1
    have : 2 * Q < N' := lt_of_lt_of_le hcut0 h1
    rw [hN'def] at this; linarith
  -- the scale conditions at `X_cell = 64 X`
  have hcell : ((2 ^ e c * 2 ^ betaTop e c : ℕ) : ℝ) ≤ 64 * X := by
    rw [← pow_add, add_betaTop, pow_add]
    push_cast
    linarith
  have hFX : (F : ℝ) ≤ 64 * X := by
    have : (F : ℝ) ≤ Q := by
      rw [hQdef]; exact_mod_cast Nat.le_mul_of_pos_right F (by positivity)
    linarith
  have hn0X : ((2 ^ n0 : ℕ) : ℝ) ≤ 64 * X := by
    have : Lr ≤ N := by
      rw [hLr]
      have : X ^ (-κ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX1'.le (by linarith)
      calc N * X ^ (-κ) ≤ N * 1 := mul_le_mul_of_nonneg_left this hN0.le
        _ = N := mul_one N
    linarith
  have hQX : ((F * 2 ^ n0 : ℕ) : ℝ) * 2 ^ e c ≤ 64 * X := by
    rw [← hQdef]
    have hNN : N * N ≤ X := by
      have h1 : N * N ≤ X ^ (1 / 3 + κ / 2) * X ^ (1 / 3 + κ / 2) :=
        mul_le_mul hNhi hNhi hN0.le (Real.rpow_nonneg hX0.le _)
      rw [← Real.rpow_add hX0] at h1
      refine h1.trans ?_
      calc X ^ (1 / 3 + κ / 2 + (1 / 3 + κ / 2)) ≤ X ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hX1'.le (by linarith)
        _ = X := Real.rpow_one _
    have : Q * N ≤ N * N := mul_le_mul_of_nonneg_right hQN hN0.le
    linarith
  have hη : κ * Real.log (64 * X) ≤ Real.log (alphaScale e c) := by
    rw [hαS]
    have hlog64 : Real.log (64 * X) = 6 * Real.log 2 + Real.log X := by
      rw [Real.log_mul (by norm_num) hX0.ne', show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
      norm_num
    have hN2 : N / 2 ≤ N' := by rw [hN'def]; linarith
    have hlogN' : Real.log (N / 2) ≤ Real.log N' := Real.log_le_log (by linarith) hN2
    have hlogN2 : Real.log (N / 2) = Real.log N - Real.log 2 := Real.log_div hN0.ne' two_ne_zero
    have hlogN : 3 * κ * Real.log X ≤ Real.log N := by
      have := Real.log_le_log (Real.rpow_pos_of_pos hX0 _) hNlo
      rwa [Real.log_rpow hX0] at this
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [hlog64, mul_add]
    have h6 : κ * (6 * Real.log 2) ≤ 6 * Real.log 2 :=
      mul_le_of_le_one_left (by positivity) (by linarith)
    have h3 : 3 * κ * Real.log X = 3 * (κ * Real.log X) := by ring
    rw [h3] at hlogN
    linarith
  have hWt : (∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J) ≤ Wbound T := by
    have := atomWeightSum_le hcr.good
    rwa [hT] at this ⊢
  have hmain := hC P hP hk Bf hBf hCa Ξ' hΞ'sub S hcr.good hWt κ N K K n0 K' F
    (Nat.lt_two_pow_self).le z z₀ j e c hK' hF hl0 (by rw [hαS]; linarith) hsw1 hsw2 hcut
    (64 * X) (by linarith) hcell (by linarith) hFX hn0X hQX hη
  refine hmain.trans ?_
  -- `Cfin (64X)/(log 64X)^A ≤ 64 max(Cfin,0) X/(log X)^A`
  have hlX0 : 0 < Real.log X := Real.log_pos hX1'
  have hlogle : Real.log X ≤ Real.log (64 * X) := Real.log_le_log hX0 (by linarith)
  have hpA : Real.log X ^ Astar ≤ Real.log (64 * X) ^ Astar :=
    Real.rpow_le_rpow hlX0.le hlogle hA.le
  have hpA0 : 0 < Real.log X ^ Astar := Real.rpow_pos_of_pos hlX0 _
  have hCm : Cfin ≤ max Cfin 0 := le_max_left _ _
  have hCm0 : 0 ≤ max Cfin 0 := le_max_right _ _
  calc Cfin * (64 * X) / Real.log (64 * X) ^ Astar
      ≤ max Cfin 0 * (64 * X) / Real.log (64 * X) ^ Astar := by
        apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCm (by positivity))
        exact (lt_of_lt_of_le hpA0 hpA).le
    _ ≤ max Cfin 0 * (64 * X) / Real.log X ^ Astar := by
        apply div_le_div_of_nonneg_left (by positivity) hpA0 hpA
    _ = 64 * max Cfin 0 * X / Real.log X ^ Astar := by ring

/-- **The full actual Urem estimate: `O_A(X/(log X)^A)` summed over all actual critical cells.**

For every `A > 0` there are `X₀`, `C` such that, with all actual data as in `actual_cell_urem`, for
every Heath–Brown box size `E₀` with `2^{E₀} ≤ X` and every set `𝒞 ⊆ cellBox E₀` of actual
critical cells `(j, e, c)` (each with `X^{3κ} ≤ 2^{e_c} ≤ X^{1/3+κ/2}`, meeting `[1, X]`, covered
by `K'`, and satisfying the interval SW input at the scale of its `α`), the total Urem
contribution — every cell, every packet `ξ ∈ Ξ` with its own `Γ_ξ, f_ξ, c_ξ, A_ξ, B_ξ`, every
atom `(J, P, χ)` and every `(l, r)` — is at most `C X/(log X)^A`.  The cell count `18 E₀⁶` and all
logarithmic losses are absorbed by applying the cell estimate with `A + 6`. -/
theorem actual_urem_total (hM : MaynardLemma13_8) (k₀ : ℕ) {b : ℕ} (hb : 2 * k₀ + 1 ≤ b)
    (cSW : ℝ → ℝ) (T : ℕ) {Astar κ δs amax CaMax : ℝ} (hA : 0 < Astar) (hκ0 : 0 < κ)
    (hδs : 0 ≤ δs) (hκδ : 2 * δs < κ) (hamax : 0 ≤ amax) :
    ∃ X0 Ctot : ℝ, ∀ (P : PhysData) (S : ScalarParams), X0 ≤ S.X → P.X = S.X →
    P.W = physW S.X → P.WGood → P.k ≤ k₀ → (∀ i, (P.a i : ℝ) ≤ amax) → FSupport P δs →
    ∀ (Bf : ℝ), (∀ v i t, |P.fp v i t| ≤ Bf) → (P.V * Bf ^ P.k) ^ 2 * (P.k : ℝ) ^ 2 ≤ CaMax →
    S.T = T → CritRegime S κ →
    ∀ (Ξ : Finset (Packet P.k)), Ξ ⊆ P.XiAll → ∀ (K K' : ℕ), (K : ℝ) ≤ S.X →
    ∀ (z z₀ E0 : ℕ), (2 : ℝ) ^ E0 ≤ S.X →
    ∀ 𝒞 : Finset (ℕ × (Fin 6 → ℕ) × Fin 6), 𝒞 ⊆ cellBox E0 → (∀ x ∈ 𝒞,
      CritCell S κ ((2 : ℝ) ^ x.2.1 x.2.2) ∧ (2 : ℝ) ^ (∑ i, x.2.1 i) ≤ S.X ∧
      4 * 2 ^ x.2.1 x.2.2 * 2 ^ betaTop x.2.1 x.2.2 ≤ K' ∧
      IntervalSWAt (roughOne z₀) (alphaScale x.2.1 x.2.2) b cSW ∧
      IntervalSWAt (roughMu z₀) (alphaScale x.2.1 x.2.2) b cSW) →
    ∑ x ∈ 𝒞, ∑ ξ ∈ Ξ, |physUrem S κ ((2 : ℝ) ^ x.2.1 x.2.2) (P.Gamma ξ) (P.f ξ) (P.cRes ξ)
        (P.A ξ) (P.B ξ) K K' (alphaSeq z z₀ x.1 x.2.1 x.2.2) (betaSeq z z₀ x.1 x.2.1 x.2.2)| ≤
      Ctot * S.X / Real.log S.X ^ Astar := by
  obtain ⟨X0, Cfin, hC⟩ := actual_cell_urem hM k₀ hb cSW T (Astar := Astar + 6) (CaMax := CaMax)
    (by linarith) hκ0 hδs hκδ hamax
  refine ⟨max X0 3, 18 * 64 * max Cfin 0, ?_⟩
  intro P S hX hPX hW hP hk ha hFs Bf hBf hCa hT hcr Ξ hΞ K K' hKX z z₀ E0 hE0 𝒞 h𝒞 hcells
  have hX3 : (3 : ℝ) ≤ S.X := le_trans (le_max_right _ _) hX
  have hX0 : X0 ≤ S.X := le_trans (le_max_left _ _) hX
  have hlX : 1 ≤ Real.log S.X := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hlX0 : 0 < Real.log S.X := by linarith
  have hcell : ∀ x ∈ 𝒞, ∑ ξ ∈ Ξ, |physUrem S κ ((2 : ℝ) ^ x.2.1 x.2.2) (P.Gamma ξ) (P.f ξ)
      (P.cRes ξ) (P.A ξ) (P.B ξ) K K' (alphaSeq z z₀ x.1 x.2.1 x.2.2)
      (betaSeq z z₀ x.1 x.2.1 x.2.2)| ≤ max Cfin 0 * S.X / Real.log S.X ^ (Astar + 6) := by
    intro x hx
    obtain ⟨h1, h2, h3, h4, h5⟩ := hcells x hx
    refine (hC P S hX0 hPX hW hP hk ha hFs Bf hBf hCa hT hcr Ξ hΞ K K' hKX z z₀ x.1 x.2.1 x.2.2
      h1 h2 h3 h4 h5).trans ?_
    have hp : 0 < Real.log S.X ^ (Astar + 6) := Real.rpow_pos_of_pos hlX0 _
    apply div_le_div_of_nonneg_right _ hp.le
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  refine (sum_le_card_nsmul _ _ _ hcell).trans ?_
  rw [nsmul_eq_mul]
  have hcard : (𝒞.card : ℝ) ≤ 18 * (E0 : ℝ) ^ 6 := by
    have := card_le_card h𝒞
    rw [card_cellBox] at this
    exact_mod_cast this
  have hE0l : (E0 : ℝ) ≤ 2 * Real.log S.X := nat_le_two_log hE0
  have hE6 : (E0 : ℝ) ^ 6 ≤ 64 * Real.log S.X ^ (6 : ℝ) := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (E0 : ℝ) ^ 6 ≤ (2 * Real.log S.X) ^ 6 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hE0l 6
      _ = 64 * Real.log S.X ^ 6 := by ring
  have hsplit : Real.log S.X ^ (Astar + 6) = Real.log S.X ^ Astar * Real.log S.X ^ (6 : ℝ) :=
    Real.rpow_add hlX0 _ _
  have hpA : 0 < Real.log S.X ^ Astar := Real.rpow_pos_of_pos hlX0 _
  have hp6 : 0 < Real.log S.X ^ (6 : ℝ) := Real.rpow_pos_of_pos hlX0 _
  have hB0 : 0 ≤ max Cfin 0 * S.X / Real.log S.X ^ (Astar + 6) := by
    have := le_max_right Cfin 0
    have : 0 < Real.log S.X ^ (Astar + 6) := Real.rpow_pos_of_pos hlX0 _
    positivity
  calc (𝒞.card : ℝ) * (max Cfin 0 * S.X / Real.log S.X ^ (Astar + 6))
      ≤ (18 * (64 * Real.log S.X ^ (6 : ℝ))) *
          (max Cfin 0 * S.X / Real.log S.X ^ (Astar + 6)) := by
        apply mul_le_mul_of_nonneg_right _ hB0
        linarith
    _ = 18 * 64 * max Cfin 0 * S.X / Real.log S.X ^ Astar := by
        rw [hsplit]
        field_simp

end Erdos287.Physical.TypeII.UremFamily
