import RequestProject.Erdos287.SourceChain.Physical.TypeII.UremFamilyFinal
import RequestProject.Erdos287.SourceChain.Physical.Presieve
import RequestProject.Erdos287.SourceChain.Physical.Factorization.ActualParams

/-!
# Erdős #287 — the actual Urem moduli `q = f_ξ l` lie in the range of Maynard I, Lemma 13.8

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

For an actual Urem cell the complete modulus is `q = f_ξ · l`, where
* `f_ξ = a_j W q_0`, `q_0 = ∏_{i ≠ j, ℓ} [d_i, d'_i]` (`PhysData.f`), and
* `l` is the first variable of the constructed atom coefficient `physCoefCut S κ N …`
  (the `h_l U_r` part of the Type-II split).

Derived here from the source definitions:

* `omega_support` — if the Maynard test function `F = ∑_v ∏_i f'_{i,v}` is supported on
  `∑ t_i ≤ δ_s` (`FSupport`), then `ω_d ≠ 0 ⇒ ∏ d_i ≤ X^{δ_s}` and every `d_i ≥ 1`
  (source §6: "its support satisfies `∏ d_i ≤ X^{δ_s}`").
* `f_le_of_Gamma_ne_zero` — `Γ_ξ ≠ 0 ⇒ f_ξ ≤ a_j W X^{2δ_s}` (source §8: `q_0 ≤ X^{2δ_s}`).
* `coefCut_l_le` — in an actual critical cell (`CritRegime S κ`, `CritCell S κ N`) every nonzero
  atom coefficient has `l ≤ N X^{-κ}`.
* `urem_modulus_le` — hence `q = f_ξ l ≤ a_j W X^{2δ_s} · N X^{-κ}`.
* `physW_le_log_sq` — `W = ∏_{p ≤ log log log X} p ≤ (log X)^2` for `X ≥ e^e`.
* `urem_modulus_lt_maynard` — **the range check**: if `2δ_s < κ`, then for all `X ≥ X₀` and every
  actual critical cell of size `N = 2^{e_c}` (`X^{3κ} ≤ N ≤ X`) and every actual packet / atom
  coefficient, `q = f_ξ l < N'/(log N')^C` with `N' = 2^{e_c} - 1/2` the scale of `α` — exactly the
  hypothesis `Q < N/(log N)^C` of Lemma 13.8 (any fixed `C`).

**Exponent condition.**  The check needs `2δ_s < κ`.  The source fixes `δ_s` ("sufficiently small",
§5) and `κ < 10⁻⁵` (§18) independently and never states this relation; it is a genuine constraint
on the parameter order (`κ` first, then `δ_s < κ/2`, then `k`, `F`).  Without it the largest
moduli `q_0 l ≈ X^{2δ_s} N X^{-κ}` exceed `N` and Lemma 13.8 does not apply.
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Physical.TypeII.UremFamily

open Erdos287.Physical Erdos287.Physical.TypeII Erdos287.Physical.Sieve
  Erdos287.Physical.Sieve.ScalarParams Erdos287.Physical.Factor

/-- **Support of the Maynard test function**: `F(t) = ∑_v ∏_i f'_{i,v}(t_i)` vanishes when
`∑ t_i > δ_s` (source §5). -/
def FSupport (P : PhysData) (δs : ℝ) : Prop :=
  ∀ t : Fin P.k → ℝ, δs < ∑ i, t i → ∑ v, ∏ i, P.fp v i (t i) = 0

/-- **Support of `ω_d`**: `ω_d ≠ 0 ⇒ d_i ≥ 1` for all `i` and `∏ d_i ≤ X^{δ_s}`. -/
theorem omega_support {P : PhysData} {δs : ℝ} (hF : FSupport P δs) (hX : 1 < P.X)
    {d : Fin P.k → ℕ} (h : P.omega d ≠ 0) :
    (∀ i, 0 < d i) ∧ ((∏ i, d i : ℕ) : ℝ) ≤ P.X ^ δs := by
  unfold PhysData.omega at h
  split_ifs at h with hc
  · have hμ : (∏ i, (ArithmeticFunction.moebius (d i) : ℝ)) ≠ 0 := left_ne_zero_of_mul h
    have hFv : (∑ v, ∏ i, P.fp v i (Real.log (d i) / Real.log P.X)) ≠ 0 := right_ne_zero_of_mul h
    have hpos : ∀ i, 0 < d i := by
      intro i
      rw [Finset.prod_ne_zero_iff] at hμ
      have := hμ i (mem_univ i)
      rcases Nat.eq_zero_or_pos (d i) with h0 | h0
      · rw [h0] at this; simp at this
      · exact h0
    refine ⟨hpos, ?_⟩
    have hsum : ∑ i, Real.log (d i) / Real.log P.X ≤ δs := by
      by_contra hlt; push_neg at hlt
      exact hFv (hF _ hlt)
    have hlogX : 0 < Real.log P.X := Real.log_pos hX
    rw [← Finset.sum_div, div_le_iff₀ hlogX] at hsum
    have hprod_pos : (0 : ℝ) < ((∏ i, d i : ℕ) : ℝ) := by
      have : 0 < ∏ i, d i := Finset.prod_pos (fun i _ => hpos i)
      exact_mod_cast this
    have hlogprod : Real.log ((∏ i, d i : ℕ) : ℝ) = ∑ i, Real.log (d i) := by
      push_cast
      rw [Real.log_prod]
      intro i _
      exact_mod_cast (hpos i).ne'
    rw [← Real.log_le_log_iff hprod_pos (Real.rpow_pos_of_pos (by linarith) _),
      Real.log_rpow (by linarith), hlogprod]
    linarith
  · exact absurd rfl h

/-- `q_0 ≤ ∏ d_i · ∏ d'_i` when all entries are positive. -/
lemma q0_le_prod {P : PhysData} (ξ : Packet P.k) (hd : ∀ i, 0 < ξ.d i)
    (hd' : ∀ i, 0 < ξ.d' i) : P.q0 ξ ≤ (∏ i, ξ.d i) * ∏ i, ξ.d' i := by
  unfold PhysData.q0 PhysData.q
  calc ∏ i ∈ P.spec ξ, Nat.lcm (ξ.d i) (ξ.d' i)
      ≤ ∏ i ∈ P.spec ξ, (ξ.d i * ξ.d' i) := by
        apply Finset.prod_le_prod' (fun i _ => ?_)
        exact Nat.le_of_dvd (Nat.mul_pos (hd i) (hd' i)) (Nat.lcm_dvd_mul _ _)
    _ = (∏ i ∈ P.spec ξ, ξ.d i) * ∏ i ∈ P.spec ξ, ξ.d' i := Finset.prod_mul_distrib
    _ ≤ (∏ i, ξ.d i) * ∏ i, ξ.d' i := by
        apply Nat.mul_le_mul
        · exact Finset.prod_le_prod_of_subset_of_one_le' (subset_univ _)
            (fun i _ _ => hd i)
        · exact Finset.prod_le_prod_of_subset_of_one_le' (subset_univ _)
            (fun i _ _ => hd' i)

/-- **The packet modulus**: `Γ_ξ ≠ 0 ⇒ f_ξ ≤ a_j W X^{2δ_s}`. -/
theorem f_le_of_Gamma_ne_zero {P : PhysData} {δs : ℝ} (hF : FSupport P δs) (hX : 1 < P.X)
    {ξ : Packet P.k} (h : P.Gamma ξ ≠ 0) :
    (P.f ξ : ℝ) ≤ (P.a ξ.j : ℝ) * P.W * P.X ^ (2 * δs) := by
  unfold PhysData.Gamma at h
  obtain ⟨hd, hdX⟩ := omega_support hF hX (left_ne_zero_of_mul h)
  obtain ⟨hd', hd'X⟩ := omega_support hF hX (right_ne_zero_of_mul h)
  have hq0 : (P.q0 ξ : ℝ) ≤ P.X ^ (2 * δs) := by
    have h1 : (P.q0 ξ : ℝ) ≤ ((∏ i, ξ.d i : ℕ) : ℝ) * ((∏ i, ξ.d' i : ℕ) : ℝ) := by
      exact_mod_cast q0_le_prod ξ hd hd'
    refine h1.trans ?_
    rw [two_mul, Real.rpow_add (by linarith)]
    exact mul_le_mul hdX hd'X (by positivity) (by positivity)
  unfold PhysData.f
  push_cast
  exact mul_le_mul_of_nonneg_left hq0 (by positivity)

/-- **The atom variable**: in an actual critical cell every nonzero atom coefficient has
`l ≤ N X^{-κ}`. -/
theorem coefCut_l_le {S : ScalarParams} {κ N : ℝ} (h : CritRegime S κ) (hN : CritCell S κ N)
    {Γ : ℝ} {f K J : ℕ} {Pb : Fin J → Fin S.H} {χ : Fin S.Kc → Fin 3} {l r : ℕ}
    (hne : physCoefCut S κ N Γ f K J Pb χ l r ≠ 0) : (l : ℝ) ≤ N * S.X ^ (-κ) := by
  unfold physCoefCut at hne
  split_ifs at hne
  · exact (physCoefAtom_ranges h.good (atomParams_of_crit h hN) hne).1
  · exact absurd rfl hne

/-- **The complete Urem modulus** `q = f_ξ l ≤ a_j W X^{2δ_s} · N X^{-κ}`. -/
theorem urem_modulus_le {P : PhysData} {δs : ℝ} (hF : FSupport P δs) (hX : 1 < P.X)
    {S : ScalarParams} {κ N : ℝ} (h : CritRegime S κ) (hN : CritCell S κ N)
    {ξ : Packet P.k} {K J : ℕ} {Pb : Fin J → Fin S.H} {χ : Fin S.Kc → Fin 3} {l r : ℕ}
    (hne : physCoefCut S κ N (P.Gamma ξ) (P.f ξ) K J Pb χ l r ≠ 0) :
    ((P.f ξ * l : ℕ) : ℝ) ≤ ((P.a ξ.j : ℝ) * P.W * P.X ^ (2 * δs)) * (N * S.X ^ (-κ)) := by
  have hΓ : P.Gamma ξ ≠ 0 := by
    intro h0; apply hne
    unfold physCoefCut physCoefAtom
    simp [h0]
  push_cast
  exact mul_le_mul (f_le_of_Gamma_ne_zero hF hX hΓ) (coefCut_l_le h hN hne) (by positivity)
    (by positivity)

/-! ### `W ≤ (log X)^2` -/

lemma log_le_self_of_pos {x : ℝ} (hx : 0 < x) : Real.log x ≤ x := by
  have := Real.add_one_le_exp (Real.log x)
  rw [Real.exp_log hx] at this; linarith

/-- `W = ∏_{p ≤ log log log X} p ≤ (log X)^2` for `X ≥ e^e`. -/
theorem physW_le_log_sq {X : ℝ} (hX : Real.exp (Real.exp 1) ≤ X) :
    (physW X : ℝ) ≤ Real.log X ^ 2 := by
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hlX : Real.exp 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]; exact hX
  have hlX0 : 0 < Real.log X := lt_of_lt_of_le (Real.exp_pos _) hlX
  have hllX : 1 ≤ Real.log (Real.log X) := by
    rw [Real.le_log_iff_exp_le hlX0]; exact hlX
  have hllX0 : 0 < Real.log (Real.log X) := by linarith
  set w := Real.log (Real.log (Real.log X)) with hw
  have hw0 : 0 ≤ w := Real.log_nonneg hllX
  unfold physW
  have h4 : (primorial ⌊w⌋₊ : ℝ) ≤ 4 ^ (⌊w⌋₊ : ℝ) := by
    rw [Real.rpow_natCast]; exact_mod_cast primorial_le_4_pow _
  refine h4.trans ?_
  have h4' : (4 : ℝ) ^ (⌊w⌋₊ : ℝ) ≤ 4 ^ w :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hw0)
  refine h4'.trans ?_
  -- `4^w = (log log X)^{log 4} ≤ (log log X)^2 ≤ (log X)^2`
  have hlog4 : Real.log 4 ≤ 2 := by
    have : Real.log 4 < 2 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have := Real.exp_one_gt_d9
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith
    linarith
  have e1 : (4 : ℝ) ^ w = Real.log (Real.log X) ^ Real.log 4 := by
    rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hllX0, hw, mul_comm]
  rw [e1]
  calc Real.log (Real.log X) ^ Real.log 4 ≤ Real.log (Real.log X) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hllX hlog4
    _ = Real.log (Real.log X) ^ 2 := Real.rpow_two _
    _ ≤ Real.log X ^ 2 := by
        apply pow_le_pow_left₀ hllX0.le (log_le_self_of_pos hlX0)

/-! ### The range check -/

/-- Eventually `8 a (log X)^{m} ≤ X^{η}` for every fixed `a, m` and `η > 0`. -/
lemma eventually_log_pow_le (a m η : ℝ) (hη : 0 < η) :
    ∃ X0 : ℝ, ∀ X ≥ X0, a * Real.log X ^ m ≤ X ^ η := by
  have ho := isLittleO_log_rpow_rpow_atTop m hη
  have hc : (0 : ℝ) < 1 / (|a| + 1) := by positivity
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.1 (ho.bound hc)
  refine ⟨max X0 1, fun X hX => ?_⟩
  have h := hX0 X (le_trans (le_max_left _ _) hX)
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ X) η)] at h
  have hXη : 0 ≤ X ^ η := Real.rpow_nonneg (by linarith) _
  calc a * Real.log X ^ m ≤ |a| * |Real.log X ^ m| := by
        rw [← abs_mul]; exact le_abs_self _
    _ ≤ |a| * (1 / (|a| + 1) * X ^ η) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ ≤ X ^ η := by
        rw [← mul_assoc]
        have : |a| * (1 / (|a| + 1)) ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]; linarith
        nlinarith

/-- **The Urem modulus range check** (Maynard I, Lemma 13.8 hypothesis).

Fix `C` (the cutoff exponent of Lemma 13.8), a slope bound `a_max`, and exponents `0 ≤ δ_s`,
`2δ_s < κ`.  Then there is `X₀` such that for every `X ≥ X₀`, every `N` with `X^{3κ} ≤ N ≤ X`
(the actual critical range `X^{3κ} ≤ N ≤ X^{1/3+κ/2}` is contained in it) and every
`Q ≤ (a_max W X^{2δ_s})·(2 N X^{-κ})` with `W = physW X`,
`2 Q < (N - 1/2)/(log (N - 1/2))^C`.  -/
theorem modulus_range_eventually (C amax δs κ : ℝ) (hamax : 0 ≤ amax) (hδs : 0 ≤ δs)
    (hκ : 2 * δs < κ) :
    ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X ≥ X0, ∀ N : ℝ, X ^ (3 * κ) ≤ N → N ≤ X → ∀ Q : ℝ,
      Q ≤ (amax * physW X * X ^ (2 * δs)) * (2 * N * X ^ (-κ)) →
      2 * Q < (N - 1 / 2) / Real.log (N - 1 / 2) ^ C := by
  have hκ0 : 0 < κ := by linarith
  set η := κ - 2 * δs with hη
  have hη0 : 0 < η := by linarith
  set m := max C 0 + 2 with hm
  obtain ⟨X1, hX1⟩ := eventually_log_pow_le (16 * amax + 1) m η hη0
  -- also `X^{3κ} ≥ 2 e` eventually
  obtain ⟨X2, hX2⟩ : ∃ X2 : ℝ, ∀ X ≥ X2, 2 * Real.exp 1 ≤ X ^ (3 * κ) := by
    refine ⟨(2 * Real.exp 1) ^ (1 / (3 * κ)) + 1, fun X hX => ?_⟩
    have hb : 0 < (2 * Real.exp 1) ^ (1 / (3 * κ)) := Real.rpow_pos_of_pos (by positivity) _
    have hX0 : (2 * Real.exp 1) ^ (1 / (3 * κ)) ≤ X := by linarith
    calc 2 * Real.exp 1 = ((2 * Real.exp 1) ^ (1 / (3 * κ))) ^ (3 * κ) := by
          rw [← Real.rpow_mul (by positivity)]; field_simp; simp
      _ ≤ X ^ (3 * κ) := Real.rpow_le_rpow hb.le hX0 (by positivity)
  refine ⟨max (max X1 X2) (Real.exp (Real.exp 1) + 2), by
    have := Real.exp_pos (Real.exp 1); exact le_trans (by linarith) (le_max_right _ _),
    fun X hX N hNlo hNhi Q hQ => ?_⟩
  have hXe : Real.exp (Real.exp 1) ≤ X := le_trans (by linarith) (le_trans (le_max_right _ _) hX)
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hXe
  have hX1' := hX1 X (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX)
  have hX2' := hX2 X (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX)
  have hN2e : 2 * Real.exp 1 ≤ N := le_trans hX2' hNlo
  have he1 : (1 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  set N' := N - 1 / 2 with hN'
  have hN'pos : 0 < N' := by rw [hN']; linarith
  have hN'e : Real.exp 1 ≤ N' := by rw [hN']; linarith
  have hlogN'1 : 1 ≤ Real.log N' := by rw [Real.le_log_iff_exp_le hN'pos]; exact hN'e
  have hlogN'X : Real.log N' ≤ Real.log X := Real.log_le_log hN'pos (by rw [hN']; linarith)
  have hlX : 1 ≤ Real.log X := le_trans hlogN'1 hlogN'X
  -- `(log N')^C ≤ (log X)^{max C 0}`
  have hpowC : Real.log N' ^ C ≤ Real.log X ^ (max C 0) := by
    calc Real.log N' ^ C ≤ Real.log N' ^ (max C 0) :=
          Real.rpow_le_rpow_of_exponent_le hlogN'1 (le_max_left _ _)
      _ ≤ Real.log X ^ (max C 0) :=
          Real.rpow_le_rpow (by linarith) hlogN'X (le_max_right _ _)
  have hpowC0 : 0 < Real.log N' ^ C := Real.rpow_pos_of_pos (by linarith) _
  have hW := physW_le_log_sq hXe
  have hW0 : (0 : ℝ) ≤ physW X := Nat.cast_nonneg _
  -- main inequality: `2Q · (log N')^C < N'`
  rw [lt_div_iff₀ hpowC0]
  have hXκ : X ^ (2 * δs) * X ^ (-κ) = X ^ (-η) := by
    rw [← Real.rpow_add hX0, hη]; ring_nf
  have hQ' : Q ≤ 2 * amax * physW X * N * X ^ (-η) := by
    calc Q ≤ (amax * physW X * X ^ (2 * δs)) * (2 * N * X ^ (-κ)) := hQ
      _ = 2 * amax * physW X * N * (X ^ (2 * δs) * X ^ (-κ)) := by ring
      _ = _ := by rw [hXκ]
  have hN0 : 0 ≤ N := by linarith
  have hXη0 : 0 < X ^ (-η) := Real.rpow_pos_of_pos hX0 _
  have hlogpow : Real.log X ^ (max C 0) * Real.log X ^ 2 = Real.log X ^ m := by
    rw [hm, Real.rpow_add (by linarith), Real.rpow_two]
  have hXm : Real.log X ^ m * X ^ (-η) * (16 * amax + 1) ≤ 1 := by
    have h1 : (16 * amax + 1) * Real.log X ^ m ≤ X ^ η := hX1'
    have h2 : X ^ η * X ^ (-η) = 1 := by
      rw [← Real.rpow_add hX0]; simp
    nlinarith [Real.rpow_nonneg (by linarith : (0:ℝ) ≤ Real.log X) m]
  have hlogXm0 : 0 ≤ Real.log X ^ m := Real.rpow_nonneg (by linarith) _
  have hlogXC0 : 0 ≤ Real.log X ^ (max C 0) := Real.rpow_nonneg (by linarith) _
  calc 2 * Q * Real.log N' ^ C
      ≤ 2 * (2 * amax * physW X * N * X ^ (-η)) * Real.log X ^ (max C 0) := by
        apply mul_le_mul (by linarith) hpowC hpowC0.le (by positivity)
    _ ≤ 2 * (2 * amax * Real.log X ^ 2 * N * X ^ (-η)) * Real.log X ^ (max C 0) := by
        gcongr
    _ = 4 * amax * N * (Real.log X ^ m * X ^ (-η)) := by rw [← hlogpow]; ring
    _ ≤ N / 4 := by
        have : 16 * amax * (Real.log X ^ m * X ^ (-η)) ≤ 1 := by nlinarith
        nlinarith
    _ < N' := by rw [hN']; linarith

/-- **Every actual Urem modulus lies in the range of Maynard I, Lemma 13.8.**

For fixed `C`, slope bound `a_max`, `0 ≤ δ_s`, `2δ_s < κ`: there is `X₀` such that for all
`X ≥ X₀`, all actual data with `P.X = S.X = X`, `W = physW X`, slopes `a_i ≤ a_max`, test function
supported on `∑ t_i ≤ δ_s`, every actual critical cell `N` (`CritRegime S κ`, `CritCell S κ N`),
every packet `ξ` and every nonzero atom coefficient at `(l, r)`, the complete modulus satisfies
`f_ξ l < N'/(log N')^C`, `N' = N - 1/2` (for `N = 2^{e_c}`, `N' = alphaScale e c`). -/
theorem urem_modulus_lt_maynard (C amax δs κ : ℝ) (hamax : 0 ≤ amax) (hδs : 0 ≤ δs)
    (hκ : 2 * δs < κ) :
    ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ (P : PhysData) (S : ScalarParams), X0 ≤ S.X → P.X = S.X →
      P.W = physW S.X → (∀ i, (P.a i : ℝ) ≤ amax) → FSupport P δs → CritRegime S κ →
      ∀ N : ℝ, CritCell S κ N → ∀ (ξ : Packet P.k) (K J : ℕ) (Pb : Fin J → Fin S.H)
      (χ : Fin S.Kc → Fin 3) (l r : ℕ),
      physCoefCut S κ N (P.Gamma ξ) (P.f ξ) K J Pb χ l r ≠ 0 →
      ((P.f ξ * l : ℕ) : ℝ) < (N - 1 / 2) / Real.log (N - 1 / 2) ^ C := by
  obtain ⟨X0, hX02, hX0⟩ := modulus_range_eventually C amax δs κ hamax hδs hκ
  refine ⟨X0, hX02, fun P S hX hPX hW ha hF hcr N hN ξ K J Pb χ l r hne => ?_⟩
  have hX1 : 1 < S.X := by linarith
  have hq := urem_modulus_le hF (by rw [hPX]; exact hX1) hcr hN hne
  rw [hPX, hW] at hq
  have hNX : N ≤ S.X := by
    refine hN.N_hi.trans ?_
    calc S.X ^ (1 / 3 + κ / 2) ≤ S.X ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX1.le (by linarith [hcr.κ_small])
      _ = S.X := Real.rpow_one _
  have hN0 : 0 ≤ N := le_trans (Real.rpow_nonneg (by linarith) _) hN.N_lo
  have hQ : ((P.f ξ * l : ℕ) : ℝ) ≤ (amax * physW S.X * S.X ^ (2 * δs)) *
      (2 * N * S.X ^ (-κ)) := by
    refine hq.trans ?_
    have hXd : 0 ≤ S.X ^ (2 * δs) := Real.rpow_nonneg (by linarith) _
    have hXk : 0 ≤ S.X ^ (-κ) := Real.rpow_nonneg (by linarith) _
    apply mul_le_mul _ _ (by positivity) (by positivity)
    · gcongr; exact ha _
    · nlinarith
  have h2 := hX0 S.X hX N hN.N_lo hNX _ hQ
  have : (0 : ℝ) ≤ ((P.f ξ * l : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

end Erdos287.Physical.TypeII.UremFamily
