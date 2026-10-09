import RequestProject.Erdos287.SourceChain.Physical.TypeII.UremFamilyModulus

/-!
# Erdős #287 — the Urem cell estimate without the `β`-length hypothesis

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

`cell_urem_polylog` (in `UremFamilyFinal.lean`) assumes `F 2^{n₀} ≤ 2^{E}` (the moduli are at most
the length of `β`).  This fails for actual cells whose complementary variables are short (e.g.
`e_i = 0` for all `i ≠ c`, so `2^{E} = 64`).  `cell_urem_polylog_full` is the separate estimate for
**every** actual cell: the hypothesis is replaced by `F 2^{n₀} · 2^{e_c} ≤ X`, which holds for all
actual critical cells (`F 2^{n₀} ≤ N` and `N² ≤ X`).  The proof is the same Cauchy–Schwarz/BDH
chain; the `β`-piece sum now carries `(3 + E)(2^E + Q)` instead of `(3 + E)2^E`, and
`N'(2^E + Q) ≤ 2X`.
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Physical.TypeII.UremFamily

open Erdos287.Physical Erdos287.Physical.TypeII Erdos287.Physical.Sieve
  Erdos287.Physical.Sieve.ScalarParams Erdos287.Physical.Factor

/-- **Sum over the dyadic `β` pieces, no `Q ≤ 2^E` hypothesis.** -/
theorem pieces_sum_le_full (E : ℕ) (X Q a : ℝ) (hX : 1 ≤ X) (hE : (2 : ℝ) ^ E ≤ X)
    (hQ0 : 0 ≤ Q) (ha : 0 ≤ a) :
    ∑ k ∈ range E, Real.sqrt (betaEnergy (2 ^ k)) * Real.sqrt (a * (((2 ^ k : ℕ) : ℝ) + Q)) ≤
      (1 + Real.log X) ^ 133 * Real.sqrt a * ((3 + E) * (2 ^ E + Q)) := by
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
  have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg _
  have h2E : (0 : ℝ) ≤ 2 ^ E := by positivity
  nlinarith

/-- **The Urem cell estimate for every actual cell** (no `β`-length hypothesis).  Same
statement as `cell_urem_polylog` with `F 2^{n₀} ≤ 2^{E}` replaced by `F 2^{n₀} · 2^{e_c} ≤ X`. -/
theorem cell_urem_polylog_full (hM : MaynardLemma13_8) (k₀ : ℕ) {b : ℕ} (hb : 2 * k₀ + 1 ≤ b)
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
    ((2 ^ n0 : ℕ) : ℝ) ≤ X → ((F * 2 ^ n0 : ℕ) : ℝ) * 2 ^ e c ≤ X →
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
  refine ⟨C, 2 * (10 * Wmax * Real.sqrt CaMax ^ 2 * Real.sqrt (max Cimp 0) * 2 ^ (p1 + p2 + p3 + 3) /
      η ^ h), ?_⟩
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
  have hQX : Q * 2 ^ e c ≤ X := by
    have e1 : ((F * 2 ^ n0 : ℕ) : ℝ) = Q := by rw [hQdef]; push_cast; ring
    rw [← e1]; exact hQ
  set Sp := ∑ k ∈ range E, Real.sqrt (betaEnergy (2 ^ k)) *
      Real.sqrt (a * (((2 ^ k : ℕ) : ℝ) + Q)) with hSpdef
  have hSp0 : 0 ≤ Sp := sum_nonneg (fun _ _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hSp : Sp ≤ Λ ^ p3 * (Real.sqrt CaMax * Λ ^ p2) * (5 * Λ) * (2 ^ E + Q) := by
    refine (pieces_sum_le_full E X Q a hX1 h2E hQ0 ha0).trans ?_
    have h3E : (3 : ℝ) + E ≤ 5 * Λ := by linarith
    have hΛ0 : 0 ≤ Λ ^ 133 := pow_nonneg (by linarith) _
    rw [hp3]
    calc (1 + Real.log X) ^ 133 * Real.sqrt a * ((3 + E) * (2 ^ E + Q))
        = Λ ^ 133 * Real.sqrt a * ((3 + E) * (2 ^ E + Q)) := by rw [hΛdef]
      _ ≤ Λ ^ 133 * (Real.sqrt CaMax * Λ ^ p2) * ((5 * Λ) * (2 ^ E + Q)) := by
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
  have hNE2 : N' * (2 ^ E + Q) ≤ 2 * X := by
    have h1 : N' * 2 ^ E ≤ X :=
      le_trans (mul_le_mul_of_nonneg_right hN'le (by positivity)) hcell
    have h2 : N' * Q ≤ X := by
      calc N' * Q ≤ 2 ^ e c * Q := mul_le_mul_of_nonneg_right hN'le hQ0
        _ = Q * 2 ^ e c := by ring
        _ ≤ X := hQX
    rw [mul_add]; linarith
  have hgoal_rhs : alphaNorm e c * ∑ k ∈ range E, Wt * (1 + Real.log K) ^ (2 ^ (b + 1)) * n0 *
      Real.sqrt (betaEnergy (2 ^ k)) * Real.sqrt (a * (((2 ^ k : ℕ) : ℝ) + Q)) *
      Real.sqrt (Ca * Y) ≤ 10 * Wmax * Real.sqrt CaMax ^ 2 * Real.sqrt (max Cimp 0) *
        2 ^ (p1 + p2 + p3 + 3) / η ^ h * (2 * X) / ℓ ^ Astar := by
    rw [hrhs]
    exact final_assembly (alphaNorm e c) Wt Wmax ((1 + Real.log K) ^ (2 ^ (b + 1))) n0
      (Real.sqrt (Ca * Y)) Sp Λ ℓ (Real.sqrt CaMax) (Real.sqrt (max Cimp 0)) N' L (2 ^ E + Q) (2 * X) η
      Astar p1 p2 p3 hAN hWt0 hWt (pow_nonneg hlogK0 _) hLK (Nat.cast_nonneg _) hn0
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hN'0 (by positivity) hη hℓ hΛ1 hΛ2 hL
      hNE2 hA
      (Real.sqrt_nonneg _) hSY hSp0 hSp
  refine hgoal_rhs.trans (le_of_eq ?_)
  ring


end Erdos287.Physical.TypeII.UremFamily
