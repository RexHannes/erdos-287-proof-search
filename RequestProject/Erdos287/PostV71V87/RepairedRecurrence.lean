import RequestProject.Erdos287.PostV71V87.EntropyInversion
import RequestProject.Erdos287.PostV71V87.RecurrenceGrowth
import RequestProject.Erdos287.PostV71V87.AnalyticProviders

/-!
# Erdős #287 — V87 repaired recurrence theorem (Astra-repaired, two-case proof)

**Theorem (`repaired_recurrence`).**  There are an absolute constant `c > 0` and `M0` such
that every exact word with `a > 1` and `M ≥ M0` satisfies

  `(M - a) / q_*  ≥  c · log D · log log D / log log log D`,   `D = M - a`.

Proof (two cases, **no dependence on V85's `δ₀`**):

* if `q_*` is bounded or `q_* < √D`, then `D / q_* ≥ √D`, which dominates;
* otherwise the entropy inequality (`entropy_inequality`) and the reciprocal-image bound
  (`log_Srec_le`) give, by the inversion lemma `entropy_inversion`,
  `H = ⌊16M/q_*⌋ ≥ c · g(log q_*)`, and `log q_* ≥ ½ log D`.

All inputs are proved in this subtree from Mathlib (Chebyshev's upper bound is imported; the
lower bound is proved from the central binomial coefficient).  **No analytic provider is
assumed.**  This is the *superlogarithmic recurrence* of the minimal grid; it does **not**
close polylogarithmic terminal windows (see `Firewalls.lean`).
-/

open Real
open scoped BigOperators

namespace Erdos287.PostV71V87

/-- `log S_rec(H) ≤ H` (trivial bound from `S_rec(H) ≤ 2^H`). -/
theorem log_Srec_le_self (H : ℕ) : Real.log (Srec H) ≤ H := by
  have h1 : Srec H ≤ 2 ^ H := by
    have := recipImage_card_le_two_pow (Finset.Icc 1 H); simpa [Srec] using this
  have h2 : (Srec H : ℝ) ≤ (2 : ℝ) ^ H := by exact_mod_cast h1
  have h3 := Real.log_le_log (by exact_mod_cast Srec_pos H) h2
  rw [Real.log_pow] at h3
  have := Real.log_two_lt_d9
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  nlinarith

theorem exp_exp_one_le_256 : Real.exp (Real.exp 1) ≤ 256 := by
  have h1 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have h2 : Real.exp (Real.exp 1) ≤ Real.exp 3 := Real.exp_le_exp.2 h1
  have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have h4 : Real.exp 1 ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le h1 3
  linarith

theorem log_ge_e_of_ge_256 {L : ℝ} (hL : 256 ≤ L) : Real.exp 1 ≤ Real.log L :=
  log_ge_e_of (le_trans exp_exp_one_le_256 hL)

theorem one_le_loglog {L : ℝ} (hL : 256 ≤ L) : 1 ≤ Real.log (Real.log L) := by
  have h := log_ge_e_of_ge_256 hL
  rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) h)]; exact h

theorem four_log_add_five_le {L : ℝ} (hL : 256 ≤ L) : 4 * Real.log L + 5 ≤ L / 2 := by
  have hx0 : 0 ≤ L := by linarith
  set t := L ^ (1 / 4 : ℝ)
  have ht4 : t ^ 4 = L := rpow_quarter_pow_four hx0
  have ht0 : 0 ≤ t := Real.rpow_nonneg hx0 _
  have ht : 4 ≤ t := by
    by_contra hc; push_neg at hc
    have : t ^ 4 < 4 ^ 4 := pow_lt_pow_left₀ hc ht0 (by norm_num)
    norm_num at this; linarith
  have h1 := log_le_four_rpow hx0
  have h3 : (64 : ℝ) ≤ t ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) ht 3; norm_num at this; linarith
  have h4 : 64 * t ≤ t ^ 4 := by
    have : t ^ 4 = t ^ 3 * t := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right h3 ht0
  linarith

theorem sqrt_le_div_sixteen {L : ℝ} (hL : 256 ≤ L) : Real.sqrt L ≤ L / 16 := by
  have h16 : 16 ≤ Real.sqrt L := by
    rw [show (16 : ℝ) = Real.sqrt 256 by
      rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hL
  have := Real.mul_self_sqrt (show (0 : ℝ) ≤ L by linarith)
  nlinarith

theorem log_sixteen_lt_three : Real.log 16 < 3 := by
  have : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_lt_d9; linarith

/-- **Entropy inversion.**  If `F` satisfies the reciprocal-image bound
`F(H) ≤ C H log log H / log H` (for `H ≥ H0`) and `F(H) ≤ H`, then
`L ≤ log 16 + F(H) + 2 log(H + 1)` with `L ≥ L0` forces `H ≥ c · g(L)`. -/
theorem entropy_inversion {F : ℕ → ℝ} {C H0 : ℝ} (hC : 0 < C)
    (hF : ∀ H : ℕ, H0 ≤ H → F H ≤ C * H * Real.log (Real.log H) / Real.log H)
    (hFtriv : ∀ H : ℕ, F H ≤ H) :
    ∃ c L0 : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (H : ℕ) (L : ℝ), L0 ≤ L → 1 ≤ H →
      L ≤ Real.log 16 + F H + 2 * Real.log ((H : ℝ) + 1) → c * gRec L ≤ H := by
  set c := 1 / (16 * (C + 1)) with hcdef
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := by rw [hcdef, div_le_one (by positivity)]; linarith
  have hCc : C * c ≤ 1 / 16 := by
    rw [hcdef, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  refine ⟨c, max 256 ((max H0 1) ^ 2), hc0, hc1, ?_⟩
  intro H L hL hH1 hineq
  by_contra hlt
  push_neg at hlt
  have hL256 : 256 ≤ L := le_trans (le_max_left _ _) hL
  have hLH0 : (max H0 1) ^ 2 ≤ L := le_trans (le_max_right _ _) hL
  have hLpos : 0 < L := by linarith
  have hl16 := log_sixteen_lt_three
  have hlog1 : ∀ x : ℝ, 0 ≤ x → Real.log (x + 1) ≤ x := fun x hx => by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < x + 1); linarith
  have hsq := sqrt_le_div_sixteen hL256
  by_cases hcase : (H : ℝ) ≤ Real.sqrt L
  · have h1 := hFtriv H
    have h2 := hlog1 H (Nat.cast_nonneg _)
    linarith
  · push_neg at hcase
    have hsq16 : 16 ≤ Real.sqrt L := by
      rw [show (16 : ℝ) = Real.sqrt 256 by
        rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hL256
    have hHH0 : H0 ≤ H := by
      have : max H0 1 ≤ Real.sqrt L := by
        calc max H0 1 = Real.sqrt ((max H0 1) ^ 2) :=
              (Real.sqrt_sq (le_trans zero_le_one (le_max_right _ _))).symm
          _ ≤ Real.sqrt L := Real.sqrt_le_sqrt hLH0
      linarith [le_max_left H0 1]
    have hHpos : (0 : ℝ) < H := by linarith
    set lL := Real.log L with hlLdef
    set llL := Real.log lL with hllLdef
    have hllL1 : 1 ≤ llL := one_le_loglog hL256
    have hlLpos : 0 < lL := by have := log_ge_e_of_ge_256 hL256; have := Real.exp_pos 1; linarith
    set lH := Real.log H with hlHdef
    have hlH_low : lL / 2 ≤ lH := by
      have := Real.log_le_log (Real.sqrt_pos.2 hLpos) hcase.le
      rw [Real.log_sqrt hLpos.le] at this; exact this
    have hlH1 : 1 < lH := by
      have h16 : Real.log 16 ≤ lH := Real.log_le_log (by norm_num) (by linarith)
      have : 1 < Real.log 16 := by
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
        have := Real.log_two_gt_d9; norm_num; linarith
      linarith
    have hg0 : 0 ≤ gRec L := gRec_nonneg (le_trans exp_exp_one_le_256 hL256)
    have hgsq : gRec L ≤ L ^ 2 := gRec_le_sq (le_trans exp_exp_one_le_256 hL256)
    have hHL2 : (H : ℝ) ≤ L ^ 2 := by nlinarith
    have hlH_up : lH ≤ 2 * lL := by
      have := Real.log_le_log hHpos hHL2
      rw [Real.log_pow] at this; push_cast at this; exact this
    set llH := Real.log lH with hllHdef
    have hllH0 : 0 ≤ llH := Real.log_nonneg hlH1.le
    have hllH_up : llH ≤ Real.log 2 + llL := by
      have := Real.log_le_log (by linarith) hlH_up
      rw [Real.log_mul (by norm_num) hlLpos.ne'] at this; exact this
    have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    -- `H · log log H ≤ 2 c L log L`
    have hgdef : gRec L = L * lL / llL := rfl
    have hA : (H : ℝ) * llH ≤ c * gRec L * (Real.log 2 + llL) :=
      mul_le_mul hlt.le hllH_up hllH0 (by positivity)
    have hB : c * gRec L * (Real.log 2 + llL) ≤ 2 * c * L * lL := by
      rw [hgdef]
      have hllpos : 0 < llL := by linarith
      have : c * (L * lL / llL) * (Real.log 2 + llL) = c * L * lL * ((Real.log 2 + llL) / llL) := by
        ring
      rw [this]
      have h2 : (Real.log 2 + llL) / llL ≤ 2 := by
        rw [div_le_iff₀ hllpos]; linarith
      have h3 : 0 ≤ c * L * lL := by positivity
      nlinarith
    have hFH := hF H hHH0
    rw [← hlHdef, ← hllHdef] at hFH
    clear_value llH lH llL lL c
    have hFb : F H ≤ L / 4 := by
      have hlHpos : 0 < lH := by linarith
      have h1 : C * H * llH / lH ≤ L / 4 := by
        rw [div_le_iff₀ hlHpos]
        have e1 : C * H * llH = C * (H * llH) := by ring
        rw [e1]
        have e2 : C * ((H : ℝ) * llH) ≤ C * (2 * c * L * lL) :=
          mul_le_mul_of_nonneg_left (le_trans hA hB) hC.le
        have e3 : C * (2 * c * L * lL) = 2 * (C * c) * (L * lL) := by ring
        have e4 : 2 * (C * c) * (L * lL) ≤ 2 * (1 / 16) * (L * lL) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        have e5 : L / 4 * (lL / 2) ≤ L / 4 * lH := mul_le_mul_of_nonneg_left hlH_low (by positivity)
        nlinarith
      linarith
    have hlogH1 : Real.log ((H : ℝ) + 1) ≤ Real.log 2 + 2 * lL := by
      have h1 : (H : ℝ) + 1 ≤ 2 * L ^ 2 := by
        have := one_le_pow₀ (n := 2) (by linarith : (1 : ℝ) ≤ L); linarith
      have := Real.log_le_log (by positivity) h1
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at this
      push_cast at this; rw [← hlLdef] at this; linarith
    have h45 := four_log_add_five_le hL256
    rw [← hlLdef] at h45
    linarith

end Erdos287.PostV71V87

namespace Erdos287.PostV71V87

theorem two_e_le_exp_e : 2 * Real.exp (Real.exp 1) ≤ Real.exp (2 * Real.exp 1) := by
  have h1 : Real.exp (2 * Real.exp 1) = Real.exp (Real.exp 1) * Real.exp (Real.exp 1) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : (2 : ℝ) ≤ Real.exp (Real.exp 1) := by
    have h3 := Real.add_one_le_exp (Real.exp 1)
    have h4 := Real.add_one_le_exp (1 : ℝ)
    linarith
  rw [h1]; nlinarith [Real.exp_pos (Real.exp 1)]

/-- `(log D)^2 ≤ √D` for `D ≥ 2^24`. -/
theorem log_sq_le_sqrt {D : ℝ} (hD : 2 ^ 24 ≤ D) : Real.log D ^ 2 ≤ Real.sqrt D := by
  have hD0 : 0 ≤ D := by linarith
  set r := D ^ (1 / 8 : ℝ)
  have hr0 : 0 ≤ r := Real.rpow_nonneg hD0 _
  have hr8 : r ^ 8 = D := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD0]; norm_num
  have hr4 : r ^ 4 = Real.sqrt D := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD0, Real.sqrt_eq_rpow]; norm_num
  have hr : 8 ≤ r := by
    by_contra hc; push_neg at hc
    have : r ^ 8 < 8 ^ 8 := pow_lt_pow_left₀ hc hr0 (by norm_num)
    norm_num at this; linarith
  have hlog : Real.log D ≤ 8 * r := by
    have := Real.log_le_rpow_div hD0 (by norm_num : (0 : ℝ) < 1 / 8)
    linarith [show r / (1 / 8) = 8 * r by ring]
  have hlog0 : 0 ≤ Real.log D := Real.log_nonneg (by linarith)
  have h1 : Real.log D ^ 2 ≤ (8 * r) ^ 2 := pow_le_pow_left₀ hlog0 hlog 2
  have h2 : (8 * r) ^ 2 ≤ r ^ 4 := by
    have h64 : (64 : ℝ) ≤ r ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) hr 2; norm_num at this; linarith
    have : r ^ 4 = r ^ 2 * r ^ 2 := by ring
    rw [this]; nlinarith
  rw [← hr4]; linarith

/-- **V87 repaired recurrence theorem.**  There are `c > 0` and `M0` such that every exact
word with `a > 1` and `M ≥ M0` satisfies
`(M - a)/q_* ≥ c · log D · log log D / log log log D` with `D = M - a`. -/
theorem repaired_recurrence :
    ∃ c : ℝ, 0 < c ∧ ∃ M0 : ℕ, ∀ W : ExactWord, 1 < W.a → M0 ≤ W.M →
      c * gRec (Real.log W.D) ≤ (W.D : ℝ) / W.qstar := by
  obtain ⟨C, H0, hC, hS⟩ := log_Srec_le
  obtain ⟨c, L0, hc0, hc1, hinv⟩ :=
    entropy_inversion (F := fun H => Real.log (Srec H)) hC hS log_Srec_le_self
  obtain ⟨q0, hq0, hent⟩ := entropy_inequality
  set Q0 : ℝ := max (q0 : ℝ) (Real.exp L0) with hQ0
  set D0 : ℝ := max (max (2 ^ 24) (Real.exp (Real.exp (2 * Real.exp 1)))) (Q0 ^ 2) with hD0
  refine ⟨c / 128, by positivity, ⌈2 * D0⌉₊ + 16, ?_⟩
  intro W ha hM
  have hM16 : 16 ≤ W.M := by omega
  have hs := W.two_mul_a_add_two_le ha hM16
  have hMD : W.M + 2 ≤ 2 * W.D := by unfold Word.D; omega
  have hqD : W.qstar ≤ W.D := le_trans (W.qstar_le Nat.prime_two) (W.Q_two_le_D ha)
  have hq2 : 2 ≤ W.qstar := W.one_lt_qstar
  have hDM : W.D ≤ W.M := Nat.sub_le _ _
  set q := W.qstar with hqdef
  set D := W.D with hDdef
  have hDr : D0 ≤ (D : ℝ) := by
    have h1 : 2 * D0 ≤ (W.M : ℝ) := by
      have := Nat.le_ceil (2 * D0)
      have h2 : ((⌈2 * D0⌉₊ : ℕ) : ℝ) ≤ W.M := by exact_mod_cast (by omega : ⌈2 * D0⌉₊ ≤ W.M)
      linarith
    have h3 : (W.M : ℝ) + 2 ≤ 2 * D := by exact_mod_cast hMD
    linarith
  have hD24 : (2 : ℝ) ^ 24 ≤ D := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hDr
  have hDee : Real.exp (Real.exp (2 * Real.exp 1)) ≤ D :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hDr
  have hDQ : Q0 ^ 2 ≤ (D : ℝ) := le_trans (le_max_right _ _) hDr
  have hDpos : (0 : ℝ) < D := by linarith [show (0 : ℝ) < 2 ^ 24 by norm_num]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  set x := Real.log (D : ℝ) with hxdef
  have hx : Real.exp (2 * Real.exp 1) ≤ x := by
    rw [hxdef, Real.le_log_iff_exp_le hDpos]; exact hDee
  have hxee : Real.exp (Real.exp 1) ≤ x / 2 := by
    have := two_e_le_exp_e; linarith
  have hxe : Real.exp (Real.exp 1) ≤ x := by have := Real.exp_pos (Real.exp 1); linarith
  have hgx0 : 0 ≤ gRec x := gRec_nonneg hxe
  have hgsqrt : gRec x ≤ Real.sqrt D := by
    have h1 := gRec_le_sq hxe
    have h2 := log_sq_le_sqrt hD24
    rw [← hxdef] at h2; linarith
  have hsqrtpos : 0 < Real.sqrt D := Real.sqrt_pos.2 hDpos
  have hQ0sqrt : Q0 ≤ Real.sqrt D := by
    have hQ0pos : 0 ≤ Q0 := le_trans (Nat.cast_nonneg _) (le_max_left _ _)
    calc Q0 = Real.sqrt (Q0 ^ 2) := (Real.sqrt_sq hQ0pos).symm
      _ ≤ Real.sqrt D := Real.sqrt_le_sqrt hDQ
  by_cases hcase : (q : ℝ) < Q0 ∨ (q : ℝ) ^ 2 < D
  · -- small minimal ceiling: `D / q ≥ √D`
    have hqs : (q : ℝ) ≤ Real.sqrt D := by
      rcases hcase with h | h
      · linarith
      · exact (Real.lt_sqrt hqpos.le).2 h |>.le
    have h1 : Real.sqrt D ≤ (D : ℝ) / q := by
      rw [le_div_iff₀ hqpos]
      calc Real.sqrt D * q ≤ Real.sqrt D * Real.sqrt D :=
            mul_le_mul_of_nonneg_left hqs hsqrtpos.le
        _ = D := Real.mul_self_sqrt hDpos.le
    have h2 : c / 128 * gRec x ≤ gRec x := by
      have : c / 128 ≤ 1 := by linarith
      nlinarith
    linarith
  · push_neg at hcase
    obtain ⟨hqQ, hqD2⟩ := hcase
    have hqq0 : q0 ≤ q := by
      have : (q0 : ℝ) ≤ q := le_trans (le_max_left _ _) hqQ
      exact_mod_cast this
    have hlq : L0 ≤ Real.log q := by
      rw [Real.le_log_iff_exp_le hqpos]; exact le_trans (le_max_right _ _) hqQ
    have hE := hent W ha hqq0
    have hH1 : 1 ≤ 16 * W.M / q := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
    have hI := hinv (16 * W.M / q) (Real.log q) hlq hH1 hE
    -- `log q ≥ x / 2`
    have hlqx : x / 2 ≤ Real.log q := by
      have := Real.log_le_log hDpos hqD2
      rw [Real.log_pow] at this; push_cast at this; rw [← hxdef] at this; linarith
    have hg1 : gRec (x / 2) ≤ gRec (Real.log q) := gRec_mono hxee hlqx
    have hg2 : gRec x / 4 ≤ gRec (x / 2) := gRec_half hx
    have hH : ((16 * W.M / q : ℕ) : ℝ) ≤ 32 * (D : ℝ) / q := by
      have h1 : ((16 * W.M / q : ℕ) : ℝ) ≤ (16 * W.M : ℕ) / (q : ℝ) := Nat.cast_div_le
      have h2 : ((16 * W.M : ℕ) : ℝ) ≤ 32 * (D : ℝ) := by
        have : (W.M : ℝ) + 2 ≤ 2 * D := by exact_mod_cast hMD
        push_cast; linarith
      calc ((16 * W.M / q : ℕ) : ℝ) ≤ (16 * W.M : ℕ) / (q : ℝ) := h1
        _ ≤ 32 * (D : ℝ) / q := div_le_div_of_nonneg_right h2 hqpos.le
    have hchain : c * (gRec x / 4) ≤ 32 * (D : ℝ) / q := by
      have := mul_le_mul_of_nonneg_left (le_trans hg2 hg1) hc0.le
      linarith
    have : c / 128 * gRec x = c * (gRec x / 4) / 32 := by ring
    rw [this, div_le_iff₀ (by norm_num)]
    have e : (D : ℝ) / q * 32 = 32 * (D : ℝ) / q := by ring
    rw [e]; exact hchain

end Erdos287.PostV71V87
