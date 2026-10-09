import RequestProject.Erdos287.SourceChain.Physical.TypeII.UremFamilyCell

/-!
# Erdős #287 — the Urem branch: `O_A(X/(log X)^A)` for an actual Heath–Brown cell

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

`cell_urem_polylog`: for an actual Heath–Brown cell (coefficients `alphaSeq`, `betaSeq`) and the
literal packets, `∑_ξ |physUrem_ξ| ≤ C_fin X/(log X)^{A}` for every `A > 0`.  The only analytic
inputs are the published Maynard I, Lemma 13.8 (`MaynardLemma13_8`) and the interval
Siegel–Walfisz condition (6.1) for the two base sequences `1_{P^-(n) ≥ z₀}`, `μ(n)1_{P^-(n) ≥ z₀}`
(`IntervalSWAt`); both are explicit hypotheses, never axioms.  All other hypotheses are
parameter-range conditions (listed in the docstring of `cell_urem_polylog`).
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Physical.TypeII.UremFamily

open Erdos287.Physical Erdos287.Physical.TypeII Erdos287.Physical.Sieve
  Erdos287.Physical.Sieve.ScalarParams Erdos287.Physical.Factor

lemma sqrt_mul_sqrt_le_add (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt a * Real.sqrt b ≤ a + b := by
  rw [← Real.sqrt_mul ha]
  have : Real.sqrt (a * b) ≤ (a + b) / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_nonneg (a - b)]
  linarith

lemma sum_two_pow_le (E : ℕ) : ∑ k ∈ range E, ((2 : ℝ) ^ k) ≤ 2 ^ E := by
  have := geom_sum_eq (show (2 : ℝ) ≠ 1 by norm_num) E
  rw [this]; norm_num

lemma log_nat_le {m : ℕ} {X : ℝ} (hm : (m : ℝ) ≤ X) (hX : 1 ≤ X) :
    Real.log m ≤ Real.log X := by
  rcases Nat.eq_zero_or_pos m with rfl | h
  · simp; exact Real.log_nonneg hX
  · exact Real.log_le_log (by exact_mod_cast h) hm

/-- `2^m ≤ X ⇒ m ≤ 2 log X`. -/
lemma nat_le_two_log {m : ℕ} {X : ℝ} (hm : (2 : ℝ) ^ m ≤ X) : (m : ℝ) ≤ 2 * Real.log X := by
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  have hlog := Real.log_le_log h2 hm
  rw [Real.log_pow] at hlog
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

lemma sqrt_le_self_of_one_le (t : ℝ) (ht : 1 ≤ t) : Real.sqrt t ≤ t := by
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

lemma piece_term_le (l v Q a Λ : ℝ) (hl1 : 1 ≤ l) (hlΛ : l ≤ Λ) (hv : 0 ≤ v) (hQ : 0 ≤ Q)
    (ha : 0 ≤ a) :
    Real.sqrt (l ^ 10 * ((2 * v) * l ^ 256)) * Real.sqrt (a * (v + Q)) ≤
      Λ ^ 133 * Real.sqrt a * (3 * v + Q) := by
  have e0 : l ^ 10 * ((2 * v) * l ^ 256) = (l ^ 133) ^ 2 * (2 * v) := by ring
  have e1 : Real.sqrt (l ^ 10 * ((2 * v) * l ^ 256)) = l ^ 133 * Real.sqrt (2 * v) := by
    rw [e0, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg (by linarith) _)]
  rw [e1, Real.sqrt_mul ha]
  have hamgm := sqrt_mul_sqrt_le_add (2 * v) (v + Q) (by positivity) (by positivity)
  have hl133 : l ^ 133 ≤ Λ ^ 133 := pow_le_pow_left₀ (by linarith) hlΛ 133
  have hsa : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hΛ : 0 ≤ Λ ^ 133 := pow_nonneg (by linarith) _
  calc l ^ 133 * Real.sqrt (2 * v) * (Real.sqrt a * Real.sqrt (v + Q))
      = l ^ 133 * Real.sqrt a * (Real.sqrt (2 * v) * Real.sqrt (v + Q)) := by ring
    _ ≤ Λ ^ 133 * Real.sqrt a * ((2 * v) + (v + Q)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hl133 hsa) hamgm
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (mul_nonneg hΛ hsa)
    _ = Λ ^ 133 * Real.sqrt a * (3 * v + Q) := by ring

/-- **Sum over the dyadic `β` pieces.** -/
theorem pieces_sum_le (E : ℕ) (X Q a : ℝ) (hX : 1 ≤ X) (hE : (2 : ℝ) ^ E ≤ X) (hQ0 : 0 ≤ Q)
    (hQ : Q ≤ 2 ^ E) (ha : 0 ≤ a) :
    ∑ k ∈ range E, Real.sqrt (betaEnergy (2 ^ k)) * Real.sqrt (a * (((2 ^ k : ℕ) : ℝ) + Q)) ≤
      (1 + Real.log X) ^ 133 * Real.sqrt a * ((3 + E) * 2 ^ E) := by
  have hterm : ∀ k ∈ range E,
      Real.sqrt (betaEnergy (2 ^ k)) * Real.sqrt (a * (((2 ^ k : ℕ) : ℝ) + Q)) ≤
      (1 + Real.log X) ^ 133 * Real.sqrt a * (3 * 2 ^ k + Q) := by
    intro k hk
    have hk : k + 1 ≤ E := mem_range.1 hk
    have hu' : ((2 * 2 ^ k : ℕ) : ℝ) = 2 * 2 ^ k := by push_cast; ring
    have huX : ((2 * 2 ^ k : ℕ) : ℝ) ≤ X := by
      rw [hu']
      calc (2 : ℝ) * 2 ^ k = 2 ^ (k + 1) := by ring
        _ ≤ 2 ^ E := pow_le_pow_right₀ (by norm_num) hk
        _ ≤ X := hE
    have hl1 : 1 ≤ 1 + Real.log ((2 * 2 ^ k : ℕ) : ℝ) := by
      have : 0 ≤ Real.log ((2 * 2 ^ k : ℕ) : ℝ) := Real.log_natCast_nonneg _
      linarith
    have hlΛ : 1 + Real.log ((2 * 2 ^ k : ℕ) : ℝ) ≤ 1 + Real.log X := by
      have := log_nat_le huX hX
      linarith
    have hv : (((2 ^ k : ℕ) : ℝ)) = 2 ^ k := by push_cast; ring
    unfold betaEnergy
    rw [hv]
    have := piece_term_le (1 + Real.log ((2 * 2 ^ k : ℕ) : ℝ)) (2 ^ k) Q a (1 + Real.log X)
      hl1 hlΛ (by positivity) hQ0 ha
    rw [hu']
    rw [hu'] at this
    exact this
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum, sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  have h2 := sum_two_pow_le E
  have hc : 0 ≤ (1 + Real.log X) ^ 133 * Real.sqrt a := by
    have := Real.log_nonneg hX
    exact mul_nonneg (pow_nonneg (by linarith) _) (Real.sqrt_nonneg _)
  refine mul_le_mul_of_nonneg_left ?_ hc
  have : (E : ℝ) * Q ≤ E * 2 ^ E := mul_le_mul_of_nonneg_left hQ (Nat.cast_nonneg _)
  nlinarith

/-- Final arithmetic: absorbing the polylogarithmic losses. -/
lemma final_assembly (AN Wt Wmax LK n0 SY Sp Λ ℓ Cs Cq N' L E2 X η Astar : ℝ) (p1 p2 p3 : ℕ)
    (hAN : AN ≤ Λ) (hWt0 : 0 ≤ Wt) (hWt : Wt ≤ Wmax) (hLK0 : 0 ≤ LK)
    (hLK : LK ≤ Λ ^ p1) (hn00 : 0 ≤ n0) (hn0 : n0 ≤ 2 * Λ) (hCs : 0 ≤ Cs) (hCq : 0 ≤ Cq)
    (hN' : 0 ≤ N') (hE2 : 0 ≤ E2) (hη : 0 < η) (hℓ : 1 ≤ ℓ) (hΛ1 : 1 ≤ Λ) (hΛ : Λ ≤ 2 * ℓ)
    (hL : η * ℓ ≤ L) (hNE : N' * E2 ≤ X) (hA : 0 < Astar)
    (hSY0 : 0 ≤ SY) (hSY : SY ≤ Cs * Cq * N' / L ^ ((↑(p1 + p2 + p3 + 3) : ℝ) + Astar))
    (hSp0 : 0 ≤ Sp) (hSp : Sp ≤ Λ ^ p3 * (Cs * Λ ^ p2) * (5 * Λ) * E2) :
    AN * (Wt * LK * n0 * SY * Sp) ≤
      10 * Wmax * Cs ^ 2 * Cq * 2 ^ (p1 + p2 + p3 + 3) / η ^ ((↑(p1 + p2 + p3 + 3) : ℝ) + Astar) *
        X / ℓ ^ Astar := by
  set P0 : ℕ := p1 + p2 + p3 + 3 with hP0
  set h : ℝ := (P0 : ℝ) + Astar with hh
  have hηℓ : 0 < η * ℓ := by positivity
  have hL0 : 0 < L := lt_of_lt_of_le hηℓ hL
  have hLh : (η * ℓ) ^ h ≤ L ^ h := Real.rpow_le_rpow hηℓ.le hL (by positivity)
  have hηℓh : (η * ℓ) ^ h = η ^ h * (ℓ ^ P0 * ℓ ^ Astar) := by
    rw [Real.mul_rpow hη.le (by linarith)]
    congr 1
    rw [hh, Real.rpow_add (by linarith), Real.rpow_natCast]
  have hWmax : 0 ≤ Wmax := hWt0.trans hWt
  have hΛ0 : 0 ≤ Λ := by linarith
  have step1 : AN * (Wt * LK * n0 * SY * Sp) ≤
      Λ * (Wmax * Λ ^ p1 * (2 * Λ) * (Cs * Cq * N' / L ^ h) *
        (Λ ^ p3 * (Cs * Λ ^ p2) * (5 * Λ) * E2)) := by
    have hB : 0 ≤ Cs * Cq * N' / L ^ h := by positivity
    by_cases hAN0 : 0 ≤ AN
    · gcongr
    · push_neg at hAN0
      have : 0 ≤ Wt * LK * n0 * SY * Sp := by positivity
      have : AN * (Wt * LK * n0 * SY * Sp) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hAN0.le this
      refine this.trans ?_
      positivity
  have e2 : Λ * (Wmax * Λ ^ p1 * (2 * Λ) * (Cs * Cq * N' / L ^ h) *
        (Λ ^ p3 * (Cs * Λ ^ p2) * (5 * Λ) * E2)) =
      10 * Wmax * Cs ^ 2 * Cq * Λ ^ P0 * (N' * E2) / L ^ h := by
    rw [hP0]; ring
  rw [e2] at step1
  refine step1.trans ?_
  have hΛP : Λ ^ P0 ≤ (2 * ℓ) ^ P0 := pow_le_pow_left₀ hΛ0 hΛ P0
  have hLhpos : 0 < (η * ℓ) ^ h := by positivity
  have hX0 : 0 ≤ X := le_trans (by positivity) hNE
  calc 10 * Wmax * Cs ^ 2 * Cq * Λ ^ P0 * (N' * E2) / L ^ h
      ≤ 10 * Wmax * Cs ^ 2 * Cq * (2 * ℓ) ^ P0 * X / (η * ℓ) ^ h := by
        gcongr
    _ = 10 * Wmax * Cs ^ 2 * Cq * 2 ^ P0 / η ^ h * X / ℓ ^ Astar := by
        rw [hηℓh, mul_pow]
        have : 0 < ℓ ^ P0 := by positivity
        have : 0 < ℓ ^ Astar := by positivity
        have : 0 < η ^ h := by positivity
        field_simp

/-- **The Urem branch for an actual Heath–Brown cell: `O_A(X/(log X)^A)`.**

For every `A > 0` (`Astar`), there are `C` (the cutoff exponent) and `C_fin` such that for every
actual cell `(z, z₀, j, e, c)` and every family `Ξ` of literal packets,
`∑_ξ |physUrem_ξ(alphaSeq, betaSeq)| ≤ C_fin X / (log X)^A`.

Analytic inputs (explicit hypotheses, published theorems, not formalized):
* `MaynardLemma13_8` (Maynard I, Lemma 13.8);
* `IntervalSWAt` for `1_{P^-(n) ≥ z₀}` and `μ(n) 1_{P^-(n) ≥ z₀}` at `N' = 2^{e_c} - 1/2`, constants
  `c_A` (Siegel–Walfisz-type input).

Parameter conditions: `k ≤ k₀`, `b ≥ 2k₀ + 1`; `C_a = (V B_f^k)² k² ≤ CaMax`;
`∑_{J ≤ T²} H^J 3^J ≤ Wmax`; `K ≤ 2^n`; `4·2^{e_c}·2^{E} ≤ K'`; `f_ξ ≤ F`; band cap
`l < 2^{n₀}`; `N' ≥ 2`; modulus cutoff `2F2^{n₀} ≤ N'/(log N')^C`; `X ≥ 3` with
`2^{e_c} 2^{E} ≤ X`, `K, F, 2^{n₀} ≤ X`; `F 2^{n₀} ≤ 2^{E}` (moduli `q = f l` at most the size
of `β`); and `log N' ≥ η log X` (the critical variable is not short).
`C_fin` depends only on `k₀, b, c_A, A, η, Wmax, CaMax`. -/
theorem cell_urem_polylog (hM : MaynardLemma13_8) (k₀ : ℕ) {b : ℕ} (hb : 2 * k₀ + 1 ≤ b)
    (cSW : ℝ → ℝ) {Astar η Wmax CaMax : ℝ} (hA : 0 < Astar) (hη : 0 < η) :
    ∃ C Cfin : ℝ, ∀ (P : PhysData), P.WGood → P.k ≤ k₀ → ∀ (Bf : ℝ),
    (∀ v i t, |P.fp v i t| ≤ Bf) → (P.V * Bf ^ P.k) ^ 2 * (P.k : ℝ) ^ 2 ≤ CaMax →
    ∀ (Ξ : Finset (Packet P.k)), Ξ ⊆ P.XiAll → ∀ (S : ScalarParams), S.Good →
    (∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J) ≤ Wmax →
    ∀ (δ N : ℝ) (K n n0 K' F : ℕ), K ≤ 2 ^ n →
    ∀ (z z₀ j : ℕ) (e : Fin 6 → ℕ) (c : Fin 6),
    4 * 2 ^ e c * 2 ^ betaTop e c ≤ K' → (∀ ξ ∈ Ξ, P.f ξ ≤ F) →
    (∀ ξ ∈ Ξ, ∀ J (Pb : Fin J → Fin S.H) (χ : Fin S.Kc → Fin 3) l r,
      physCoefCut S δ N (P.Gamma ξ) (P.f ξ) K J Pb χ l r ≠ 0 → l < 2 ^ n0) →
    2 ≤ alphaScale e c →
    IntervalSWAt (roughOne z₀) (alphaScale e c) b cSW →
    IntervalSWAt (roughMu z₀) (alphaScale e c) b cSW →
    ((2 * F * 2 ^ n0 : ℕ) : ℝ) ≤ alphaScale e c / Real.log (alphaScale e c) ^ C →
    ∀ X : ℝ, 3 ≤ X → ((2 ^ e c * 2 ^ betaTop e c : ℕ) : ℝ) ≤ X → (K : ℝ) ≤ X → (F : ℝ) ≤ X →
    ((2 ^ n0 : ℕ) : ℝ) ≤ X → ((F * 2 ^ n0 : ℕ) : ℝ) ≤ ((2 ^ betaTop e c : ℕ) : ℝ) →
    η * Real.log X ≤ Real.log (alphaScale e c) →
    ∑ ξ ∈ Ξ, |physUrem S δ N (P.Gamma ξ) (P.f ξ) (P.cRes ξ) (P.A ξ) (P.B ξ) K K'
        (alphaSeq z z₀ j e c) (betaSeq z z₀ j e c)| ≤ Cfin * X / Real.log X ^ Astar := by
  set p1 : ℕ := 2 ^ (b + 1) with hp1
  set p2 : ℕ := 4 ^ k₀ with hp2
  set p3 : ℕ := 133 with hp3
  set h : ℝ := (↑(p1 + p2 + p3 + 3) : ℝ) + Astar with hh
  have hh0 : 0 < h := by positivity
  obtain ⟨C, Cimp, hC⟩ := cell_urem_bound hM (b := b) (by omega) cSW (Aexp := h * 2)
    (by positivity)
  refine ⟨C, 10 * Wmax * Real.sqrt CaMax ^ 2 * Real.sqrt (max Cimp 0) * 2 ^ (p1 + p2 + p3 + 3) /
      η ^ h, ?_⟩
  intro P hP hk₀ Bf hBf hCa Ξ hΞ S hS hWt δ N K n n0 K' F hKn z z₀ j e c hK' hF hl0 hN h1 hμ
    hcut X hX hXcell hKX hFX hn0X hQ hL
  have hkb : (2 * P.k : ℝ) + 1 ≤ b := by exact_mod_cast (by omega : 2 * P.k + 1 ≤ b)
  have hmain := hC P hP Bf hBf hkb Ξ hΞ S hS δ N K n n0 K' F hKn z z₀ j e c hK' hF hl0 hN h1 hμ
    hcut
  refine hmain.trans ?_
  -- basic facts
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hℓ : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  set ℓ := Real.log X with hℓdef
  set Λ := 1 + ℓ with hΛdef
  have hΛ1 : 1 ≤ Λ := by linarith
  have hΛ2 : Λ ≤ 2 * ℓ := by linarith
  set E := betaTop e c with hEdef
  have hE1 : 1 ≤ E := by rw [hEdef]; unfold betaTop; omega
  have hcell : ((2 : ℝ) ^ e c) * 2 ^ E ≤ X := by
    have : ((2 ^ e c * 2 ^ E : ℕ) : ℝ) = (2 : ℝ) ^ e c * 2 ^ E := by push_cast; ring
    rw [← this]; exact hXcell
  have h2ec : (1 : ℝ) ≤ 2 ^ e c := one_le_pow₀ (by norm_num)
  have h2E : (2 : ℝ) ^ E ≤ X := le_trans (le_mul_of_one_le_left (by positivity) h2ec) hcell
  set N' := alphaScale e c with hN'def
  have hN'le : N' ≤ (2 : ℝ) ^ e c := by
    rw [hN'def]; unfold alphaScale; push_cast; linarith
  -- alphaNorm ≤ Λ
  have hAN : alphaNorm e c ≤ Λ := by
    unfold alphaNorm
    split_ifs
    · have h2N : 2 * N' ≤ X := by
        have h2E2 : (2 : ℝ) ≤ 2 ^ E := by
          calc (2 : ℝ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ E := pow_le_pow_right₀ (by norm_num) hE1
        calc 2 * N' ≤ 2 * 2 ^ e c := by linarith
          _ ≤ 2 ^ E * 2 ^ e c := by gcongr
          _ = 2 ^ e c * 2 ^ E := by ring
          _ ≤ X := hcell
      have := Real.log_le_log (by linarith) h2N
      rw [hΛdef]; linarith
    · rw [hΛdef]; linarith
  -- (1 + log K)^p1 ≤ Λ^p1
  have hlogK0 : 0 ≤ 1 + Real.log K := one_add_log_nonneg K
  have hLK : (1 + Real.log K) ^ (2 ^ (b + 1)) ≤ Λ ^ p1 := by
    rw [hp1]
    exact pow_le_pow_left₀ hlogK0 (by have := log_nat_le hKX hX1; rw [hΛdef]; linarith) _
  -- n0 ≤ 2Λ
  have hn0 : (n0 : ℝ) ≤ 2 * Λ := by
    have : (2 : ℝ) ^ n0 ≤ X := by
      have e : ((2 ^ n0 : ℕ) : ℝ) = (2 : ℝ) ^ n0 := by push_cast; ring
      rw [← e]; exact hn0X
    have := nat_le_two_log this
    rw [hΛdef]; linarith
  have hE : (E : ℝ) ≤ 2 * Λ := by
    have := nat_le_two_log h2E
    rw [hΛdef]; linarith
  -- the packet-density factor
  set Ca := (P.V * Bf ^ P.k) ^ 2 * (P.k : ℝ) ^ 2 with hCadef
  have hCa0 : 0 ≤ Ca := by positivity
  have hCaMax0 : 0 ≤ CaMax := hCa0.trans hCa
  set a := Ca * (1 + Real.log F) ^ (2 ^ (2 * P.k)) with hadef
  have hlogF1 : 1 ≤ 1 + Real.log F := by have := Real.log_natCast_nonneg F; linarith
  have hlogFΛ : 1 + Real.log F ≤ Λ := by have := log_nat_le hFX hX1; rw [hΛdef]; linarith
  have hpow1 : 1 ≤ (1 + Real.log F) ^ (2 ^ (2 * P.k)) := one_le_pow₀ hlogF1
  have ha0 : 0 ≤ a := mul_nonneg hCa0 (by linarith)
  have hsqa : Real.sqrt a ≤ Real.sqrt CaMax * Λ ^ p2 := by
    rw [hadef, Real.sqrt_mul hCa0]
    refine mul_le_mul (Real.sqrt_le_sqrt hCa) ?_ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc Real.sqrt ((1 + Real.log F) ^ (2 ^ (2 * P.k)))
        ≤ (1 + Real.log F) ^ (2 ^ (2 * P.k)) := sqrt_le_self_of_one_le _ hpow1
      _ ≤ Λ ^ (2 ^ (2 * P.k)) := pow_le_pow_left₀ (by linarith) hlogFΛ _
      _ ≤ Λ ^ p2 := by
          apply pow_le_pow_right₀ hΛ1
          rw [hp2, pow_mul]
          exact Nat.pow_le_pow_right (by norm_num) hk₀
  -- the pieces sum
  set Q : ℝ := (F : ℝ) * ((2 ^ n0 : ℕ) : ℝ) with hQdef
  have hQ0 : 0 ≤ Q := by positivity
  have hQE : Q ≤ 2 ^ E := by
    have e1 : ((F * 2 ^ n0 : ℕ) : ℝ) = Q := by rw [hQdef]; push_cast; ring
    have e2 : ((2 ^ E : ℕ) : ℝ) = (2 : ℝ) ^ E := by push_cast; ring
    rw [← e1, ← e2]; exact hQ
  set Sp := ∑ k ∈ range E, Real.sqrt (betaEnergy (2 ^ k)) *
      Real.sqrt (a * (((2 ^ k : ℕ) : ℝ) + Q)) with hSpdef
  have hSp0 : 0 ≤ Sp := sum_nonneg (fun _ _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hSp : Sp ≤ Λ ^ p3 * (Real.sqrt CaMax * Λ ^ p2) * (5 * Λ) * 2 ^ E := by
    refine (pieces_sum_le E X Q a hX1 h2E hQ0 hQE ha0).trans ?_
    have h3E : (3 : ℝ) + E ≤ 5 * Λ := by linarith
    have hΛ0 : 0 ≤ Λ ^ 133 := pow_nonneg (by linarith) _
    rw [hp3]
    calc (1 + Real.log X) ^ 133 * Real.sqrt a * ((3 + E) * 2 ^ E)
        = Λ ^ 133 * Real.sqrt a * ((3 + E) * 2 ^ E) := by rw [hΛdef]
      _ ≤ Λ ^ 133 * (Real.sqrt CaMax * Λ ^ p2) * ((5 * Λ) * 2 ^ E) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hsqa hΛ0)
            (mul_le_mul_of_nonneg_right h3E (by positivity)) (by positivity)
          exact mul_nonneg hΛ0 (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (by linarith) _))
      _ = _ := by ring
  -- the BDH factor
  set L := Real.log N' with hLdef
  have hηℓ : 0 < η * ℓ := by positivity
  have hL0 : 0 < L := lt_of_lt_of_le hηℓ hL
  set Y := Cimp * N' ^ 2 / L ^ (h * 2) with hYdef
  have hN'0 : 0 ≤ N' := by linarith
  have hLh2 : L ^ (h * 2) = (L ^ h) ^ 2 := by
    rw [Real.rpow_mul hL0.le, Real.rpow_two]
  have hSY : Real.sqrt (Ca * Y) ≤ Real.sqrt CaMax * Real.sqrt (max Cimp 0) * N' / L ^ h := by
    have hLhpos : 0 < L ^ h := Real.rpow_pos_of_pos hL0 h
    have hYle : Ca * Y ≤ CaMax * (max Cimp 0 * N' ^ 2 / L ^ (h * 2)) := by
      rw [hYdef]
      have hden : 0 < L ^ (h * 2) := Real.rpow_pos_of_pos hL0 _
      have h1' : Cimp * N' ^ 2 / L ^ (h * 2) ≤ max Cimp 0 * N' ^ 2 / L ^ (h * 2) := by
        gcongr; exact le_max_left _ _
      have h2' : 0 ≤ max Cimp 0 * N' ^ 2 / L ^ (h * 2) := by
        have := le_max_right Cimp 0; positivity
      calc Ca * (Cimp * N' ^ 2 / L ^ (h * 2)) ≤ Ca * (max Cimp 0 * N' ^ 2 / L ^ (h * 2)) :=
            mul_le_mul_of_nonneg_left h1' hCa0
        _ ≤ CaMax * (max Cimp 0 * N' ^ 2 / L ^ (h * 2)) := mul_le_mul_of_nonneg_right hCa h2'
    refine (Real.sqrt_le_sqrt hYle).trans (le_of_eq ?_)
    rw [hLh2, Real.sqrt_mul hCaMax0, Real.sqrt_div' _ (by positivity),
      Real.sqrt_mul (le_max_right _ _), Real.sqrt_sq hN'0, Real.sqrt_sq hLhpos.le]
    ring
  -- rewrite the right-hand side of `hmain`
  set Wt := ∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J with hWtdef
  have hWt0 : 0 ≤ Wt := by positivity
  have hrhs : alphaNorm e c * ∑ k ∈ range E, Wt * (1 + Real.log K) ^ (2 ^ (b + 1)) * n0 *
      Real.sqrt (betaEnergy (2 ^ k)) * Real.sqrt (a * (((2 ^ k : ℕ) : ℝ) + Q)) *
      Real.sqrt (Ca * Y) =
      alphaNorm e c * (Wt * (1 + Real.log K) ^ (2 ^ (b + 1)) * n0 * Real.sqrt (Ca * Y) * Sp) := by
    congr 1
    rw [hSpdef, mul_sum]
    refine sum_congr rfl (fun k _ => ?_)
    ring
  have hgoal_rhs : alphaNorm e c * ∑ k ∈ range E, Wt * (1 + Real.log K) ^ (2 ^ (b + 1)) * n0 *
      Real.sqrt (betaEnergy (2 ^ k)) * Real.sqrt (a * (((2 ^ k : ℕ) : ℝ) + Q)) *
      Real.sqrt (Ca * Y) ≤ 10 * Wmax * Real.sqrt CaMax ^ 2 * Real.sqrt (max Cimp 0) *
        2 ^ (p1 + p2 + p3 + 3) / η ^ h * X / ℓ ^ Astar := by
    rw [hrhs]
    exact final_assembly (alphaNorm e c) Wt Wmax ((1 + Real.log K) ^ (2 ^ (b + 1))) n0
      (Real.sqrt (Ca * Y)) Sp Λ ℓ (Real.sqrt CaMax) (Real.sqrt (max Cimp 0)) N' L (2 ^ E) X η
      Astar p1 p2 p3 hAN hWt0 hWt (pow_nonneg hlogK0 _) hLK (Nat.cast_nonneg _) hn0
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hN'0 (by positivity) hη hℓ hΛ1 hΛ2 hL
      (le_trans (mul_le_mul_of_nonneg_right hN'le (by positivity)) hcell) hA
      (Real.sqrt_nonneg _) hSY hSp0 hSp
  exact hgoal_rhs

/-- The box of Heath–Brown cell indices `(j, e, c)` with `j ∈ {1,2,3}`, `e ∈ [0,E₀)^6`. -/
def cellBox (E0 : ℕ) : Finset (ℕ × (Fin 6 → ℕ) × Fin 6) :=
  Finset.Icc 1 3 ×ˢ (Fintype.piFinset (fun _ : Fin 6 => range E0) ×ˢ univ)

lemma card_cellBox (E0 : ℕ) : (cellBox E0).card = 18 * E0 ^ 6 := by
  unfold cellBox
  rw [card_product, card_product, Fintype.card_piFinset, card_univ, Fintype.card_fin]
  simp only [Nat.card_Icc, card_range, prod_const, card_univ, Fintype.card_fin]
  ring

/-- **Aggregation over Heath–Brown cells.**  With the constants `C`, `C_fin` of
`cell_urem_polylog`, for any set `𝒞` of cells `(j, e, c)` each of which satisfies the per-cell
conditions of `cell_urem_polylog`, the total Urem contribution is at most
`|𝒞| C_fin X/(log X)^A`; for `𝒞 ⊆ cellBox E₀` one has `|𝒞| ≤ 18 E₀^6` (`card_cellBox`), and
`E₀ ≤ 2 log X` when `2^{E₀} ≤ X`, so the total is `O(X/(log X)^{A-6})`. -/
theorem cells_urem_polylog (hM : MaynardLemma13_8) (k₀ : ℕ) {b : ℕ} (hb : 2 * k₀ + 1 ≤ b)
    (cSW : ℝ → ℝ) {Astar η Wmax CaMax : ℝ} (hA : 0 < Astar) (hη : 0 < η) :
    ∃ C Cfin : ℝ, ∀ (P : PhysData), P.WGood → P.k ≤ k₀ → ∀ (Bf : ℝ),
    (∀ v i t, |P.fp v i t| ≤ Bf) → (P.V * Bf ^ P.k) ^ 2 * (P.k : ℝ) ^ 2 ≤ CaMax →
    ∀ (Ξ : Finset (Packet P.k)), Ξ ⊆ P.XiAll → ∀ (S : ScalarParams), S.Good →
    (∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J) ≤ Wmax →
    ∀ (δ N : ℝ) (K n n0 K' F : ℕ), K ≤ 2 ^ n → (∀ ξ ∈ Ξ, P.f ξ ≤ F) →
    (∀ ξ ∈ Ξ, ∀ J (Pb : Fin J → Fin S.H) (χ : Fin S.Kc → Fin 3) l r,
      physCoefCut S δ N (P.Gamma ξ) (P.f ξ) K J Pb χ l r ≠ 0 → l < 2 ^ n0) →
    ∀ (z z₀ : ℕ) (X : ℝ), 3 ≤ X → (K : ℝ) ≤ X → (F : ℝ) ≤ X → ((2 ^ n0 : ℕ) : ℝ) ≤ X →
    ∀ 𝒞 : Finset (ℕ × (Fin 6 → ℕ) × Fin 6), (∀ x ∈ 𝒞,
      4 * 2 ^ x.2.1 x.2.2 * 2 ^ betaTop x.2.1 x.2.2 ≤ K' ∧ 2 ≤ alphaScale x.2.1 x.2.2 ∧
      IntervalSWAt (roughOne z₀) (alphaScale x.2.1 x.2.2) b cSW ∧
      IntervalSWAt (roughMu z₀) (alphaScale x.2.1 x.2.2) b cSW ∧
      ((2 * F * 2 ^ n0 : ℕ) : ℝ) ≤ alphaScale x.2.1 x.2.2 / Real.log (alphaScale x.2.1 x.2.2) ^ C ∧
      ((2 ^ x.2.1 x.2.2 * 2 ^ betaTop x.2.1 x.2.2 : ℕ) : ℝ) ≤ X ∧
      ((F * 2 ^ n0 : ℕ) : ℝ) ≤ ((2 ^ betaTop x.2.1 x.2.2 : ℕ) : ℝ) ∧
      η * Real.log X ≤ Real.log (alphaScale x.2.1 x.2.2)) →
    ∑ x ∈ 𝒞, ∑ ξ ∈ Ξ, |physUrem S δ N (P.Gamma ξ) (P.f ξ) (P.cRes ξ) (P.A ξ) (P.B ξ) K K'
        (alphaSeq z z₀ x.1 x.2.1 x.2.2) (betaSeq z z₀ x.1 x.2.1 x.2.2)| ≤
      𝒞.card * (Cfin * X / Real.log X ^ Astar) := by
  obtain ⟨C, Cfin, hC⟩ := cell_urem_polylog hM k₀ hb cSW (Wmax := Wmax) (CaMax := CaMax) hA hη
  refine ⟨C, Cfin, ?_⟩
  intro P hP hk₀ Bf hBf hCa Ξ hΞ S hS hWt δ N K n n0 K' F hKn hF hl0 z z₀ X hX hKX hFX hn0X 𝒞 h𝒞
  rw [← nsmul_eq_mul]
  refine sum_le_card_nsmul _ _ _ (fun x hx => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h𝒞 x hx
  exact hC P hP hk₀ Bf hBf hCa Ξ hΞ S hS hWt δ N K n n0 K' F hKn z z₀ x.1 x.2.1 x.2.2 h1 hF hl0
    h2 h3 h4 h5 X hX h6 hKX hFX hn0X h7 h8

end Erdos287.Physical.TypeII.UremFamily
