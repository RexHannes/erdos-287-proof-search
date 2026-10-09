import RequestProject.Erdos287.SourceChain.Physical.Scalar.Weights

/-!
# Erdős #287 — scalar sieve: levels and the box grid

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

Elementary facts about the levels of §13 and the high-prime box grid of §14:

* `Dtot_eq` — `D_tot = D_int^{1+ε₀+τ}` (the distinction `D_tot = X^{59/100}` vs `D_int` is kept);
* `Dlow_mul` — `D_low · D_int^{1+τ} = D_tot`;
* `u0_sq_le_Dlow` — `u² ≤ D_low` (`T ≥ 2`), so the lower-sieve condition `p_1² ≤ D_low` is
  automatic for low primes;
* `boxTop_eq` — `D_j^{1+τ} = D_{j+1}` (consecutive boxes tile `(u, D_H]`);
* `lt_H_iff` — `j < H ↔ D_j ≤ √D_int`;
* `inBox_unique`, `boxOf_spec`, `boxOf_mono` — the ownership rule;
* `prime_le_ztop` — every prime `p ≤ z = D_H` is low or high, or equals `u`.
-/

open scoped BigOperators
open Finset

namespace Erdos287.Physical.Sieve.ScalarParams

variable {S : ScalarParams}

theorem T_pos (hS : S.Good) : (0 : ℝ) < S.T := by
  have := hS.T_two; exact_mod_cast (by omega : 0 < S.T)

theorem eps0_pos (hS : S.Good) : 0 < S.eps0 := by
  unfold eps0; exact div_pos one_pos (T_pos hS)

theorem eps0_le_half (hS : S.Good) : S.eps0 ≤ 1 / 2 := by
  unfold eps0
  have : (2 : ℝ) ≤ S.T := by exact_mod_cast hS.T_two
  exact one_div_le_one_div_of_le (by norm_num) this

theorem tau_pos (hS : S.Good) : 0 < S.tau := pow_pos (eps0_pos hS) 9

theorem Dtot_gt_one (hS : S.Good) : 1 < S.Dtot :=
  Real.one_lt_rpow hS.X_gt (by norm_num)

theorem Dtot_pos (hS : S.Good) : 0 < S.Dtot := lt_trans one_pos (Dtot_gt_one hS)

theorem expo_pos (hS : S.Good) : 0 < 1 + S.eps0 + S.tau := by
  linarith [eps0_pos hS, tau_pos hS]

theorem Dint_gt_one (hS : S.Good) : 1 < S.Dint :=
  Real.one_lt_rpow (Dtot_gt_one hS) (div_pos one_pos (expo_pos hS))

theorem Dint_pos (hS : S.Good) : 0 < S.Dint := lt_trans one_pos (Dint_gt_one hS)

theorem u0_gt_one (hS : S.Good) : 1 < S.u0 :=
  Real.one_lt_rpow (Dint_gt_one hS) (pow_pos (eps0_pos hS) 2)

theorem u0_pos (hS : S.Good) : 0 < S.u0 := lt_trans one_pos (u0_gt_one hS)

theorem Dlow_ge_one (hS : S.Good) : 1 ≤ S.Dlow :=
  (Real.one_lt_rpow (Dint_gt_one hS) (eps0_pos hS)).le

/-- **`D_tot = D_int^{1+ε₀+τ}`**. -/
theorem Dtot_eq (hS : S.Good) : S.Dtot = S.Dint ^ (1 + S.eps0 + S.tau) := by
  unfold Dint
  rw [← Real.rpow_mul (Dtot_pos hS).le, one_div, inv_mul_cancel₀ (expo_pos hS).ne',
    Real.rpow_one]

/-- **`D_low · D_int^{1+τ} = D_tot`**. -/
theorem Dlow_mul (hS : S.Good) : S.Dlow * S.Dint ^ (1 + S.tau) = S.Dtot := by
  rw [Dtot_eq hS, Dlow, ← Real.rpow_add (Dint_pos hS)]
  ring_nf

/-- `u^{T²} = D_int`. -/
theorem u0_pow_T_sq (hS : S.Good) : S.u0 ^ ((S.T : ℝ) ^ 2) = S.Dint := by
  unfold u0
  rw [← Real.rpow_mul (Dint_pos hS).le, eps0, div_pow, one_pow,
    one_div_mul_cancel (pow_pos (T_pos hS) 2).ne', Real.rpow_one]

/-- **`u² ≤ D_low`** (since `2ε₀² ≤ ε₀`). -/
theorem u0_sq_le_Dlow (hS : S.Good) : S.u0 ^ 2 ≤ S.Dlow := by
  unfold u0 Dlow
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Dint_pos hS).le]
  apply Real.rpow_le_rpow_of_exponent_le (Dint_gt_one hS).le
  have h1 := eps0_pos hS
  have h2 := eps0_le_half hS
  push_cast
  nlinarith

theorem boxEnd_ge_u0 (hS : S.Good) (j : ℕ) : S.u0 ≤ S.boxEnd j := by
  unfold boxEnd
  conv_lhs => rw [← Real.rpow_one S.u0]
  apply Real.rpow_le_rpow_of_exponent_le (u0_gt_one hS).le
  exact one_le_pow₀ (by linarith [tau_pos hS])

theorem boxEnd_gt_one (hS : S.Good) (j : ℕ) : 1 < S.boxEnd j :=
  lt_of_lt_of_le (u0_gt_one hS) (boxEnd_ge_u0 hS j)

theorem boxEnd_pos (hS : S.Good) (j : ℕ) : 0 < S.boxEnd j :=
  lt_trans one_pos (boxEnd_gt_one hS j)

theorem boxEnd_zero : S.boxEnd 0 = S.u0 := by simp [boxEnd]

/-- **`D_j^{1+τ} = D_{j+1}`**. -/
theorem boxTop_eq (hS : S.Good) (j : ℕ) : S.boxTop j = S.boxEnd (j + 1) := by
  unfold boxTop boxEnd
  rw [← Real.rpow_mul (u0_pos hS).le, pow_succ]

theorem boxEnd_strictMono (hS : S.Good) : StrictMono S.boxEnd := by
  apply strictMono_nat_of_lt_succ
  intro j
  unfold boxEnd
  apply Real.rpow_lt_rpow_of_exponent_lt (u0_gt_one hS)
  rw [pow_succ]
  have := pow_pos (show 0 < 1 + S.tau by linarith [tau_pos hS]) j
  nlinarith [tau_pos hS]

theorem boxEnd_le_iff (hS : S.Good) {i j : ℕ} : S.boxEnd i ≤ S.boxEnd j ↔ i ≤ j :=
  (boxEnd_strictMono hS).le_iff_le

theorem boxEnd_unbounded (hS : S.Good) (M : ℝ) : ∃ j, M < S.boxEnd j := by
  -- `D_j ≥ u^{1 + jτ}` by Bernoulli
  have hu := u0_gt_one hS
  have hlog : 0 < Real.log S.u0 := Real.log_pos hu
  obtain ⟨j, hj⟩ := exists_nat_gt ((Real.log (max M 1)) / (Real.log S.u0 * S.tau))
  refine ⟨j, ?_⟩
  have hbern : 1 + (j : ℝ) * S.tau ≤ (1 + S.tau) ^ j :=
    one_add_mul_le_pow (by linarith [tau_pos hS]) j
  have h1 : S.u0 ^ (1 + (j : ℝ) * S.tau) ≤ S.boxEnd j :=
    Real.rpow_le_rpow_of_exponent_le hu.le hbern
  have h2 : max M 1 < S.u0 ^ (1 + (j : ℝ) * S.tau) := by
    rw [← Real.exp_log (lt_of_lt_of_le one_pos (le_max_right M 1)),
      Real.rpow_def_of_pos (u0_pos hS)]
    apply Real.exp_lt_exp.2
    have hτ := tau_pos hS
    rw [div_lt_iff₀ (mul_pos hlog hτ)] at hj
    nlinarith
  exact lt_of_le_of_lt (le_max_left M 1) (lt_of_lt_of_le h2 h1)

theorem H_spec (hS : S.Good) : ∀ j, j < S.H ↔ S.boxEnd j ≤ Real.sqrt S.Dint := by
  classical
  have hex : ∃ j, Real.sqrt S.Dint < S.boxEnd j := boxEnd_unbounded hS _
  intro j
  have hH : S.H = Nat.find hex := by unfold H; rw [dif_pos hex]
  rw [hH]
  constructor
  · intro hj
    exact not_lt.1 (Nat.find_min hex hj)
  · intro hj
    by_contra hc
    push_neg at hc
    have := Nat.find_spec hex
    have hmono := (boxEnd_le_iff hS).2 hc
    linarith

theorem lt_H_iff (hS : S.Good) {j : ℕ} : j < S.H ↔ S.boxEnd j ≤ Real.sqrt S.Dint :=
  H_spec hS j

/-- Boxes are disjoint: a prime lies in at most one box. -/
theorem inBox_unique (hS : S.Good) {i j p : ℕ} (hi : S.InBox i p) (hj : S.InBox j p) :
    i = j := by
  unfold InBox at hi hj
  rw [boxTop_eq hS] at hi hj
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := (boxEnd_le_iff hS).2 (show i + 1 ≤ j by omega)
    linarith [hi.2, hj.1]
  · have := (boxEnd_le_iff hS).2 (show j + 1 ≤ i by omega)
    linarith [hj.2, hi.1]

theorem boxOf_spec {p : ℕ} (hp : S.IsHigh p) : S.boxOf p < S.H ∧ S.InBox (S.boxOf p) p := by
  classical
  obtain ⟨-, j, hj, hb⟩ := hp
  have hex : ∃ j, j < S.H ∧ S.InBox j p := ⟨j, hj, hb⟩
  unfold boxOf
  rw [dif_pos hex]
  exact Nat.find_spec hex

theorem boxOf_eq (hS : S.Good) {p j : ℕ} (hp : S.IsHigh p) (hj : S.InBox j p) :
    S.boxOf p = j :=
  inBox_unique hS (boxOf_spec hp).2 hj

/-- Ownership is monotone: larger high primes lie in weakly larger boxes. -/
theorem boxOf_mono (hS : S.Good) {p q : ℕ} (hp : S.IsHigh p) (hq : S.IsHigh q) (hpq : p ≤ q) :
    S.boxOf p ≤ S.boxOf q := by
  by_contra hc
  push_neg at hc
  have h1 := (boxOf_spec hp).2
  have h2 := (boxOf_spec hq).2
  unfold InBox at h1 h2
  rw [boxTop_eq hS] at h2
  have := (boxEnd_le_iff hS).2 (show S.boxOf q + 1 ≤ S.boxOf p by omega)
  have hpq' : (p : ℝ) ≤ q := by exact_mod_cast hpq
  linarith [h1.1, h2.2]

theorem high_gt_u0 (hS : S.Good) {p : ℕ} (hp : S.IsHigh p) : S.u0 < p := by
  obtain ⟨-, j, -, hb, -⟩ := hp
  exact lt_of_le_of_lt (boxEnd_ge_u0 hS j) hb

theorem not_low_of_high (hS : S.Good) {p : ℕ} (hp : S.IsHigh p) : ¬ (p : ℝ) < S.u0 :=
  not_lt.2 (high_gt_u0 hS hp).le

theorem high_le_ztop (hS : S.Good) {p : ℕ} (hp : S.IsHigh p) : (p : ℝ) ≤ S.ztop := by
  obtain ⟨-, j, hj, -, hb⟩ := hp
  rw [boxTop_eq hS] at hb
  exact hb.trans ((boxEnd_le_iff hS).2 hj)

/-- Every real `y ∈ (u, D_H]` lies in some box of the grid. -/
theorem exists_box (hS : S.Good) {y : ℝ} (h1 : S.u0 < y) (h2 : y ≤ S.ztop) :
    ∃ j < S.H, S.boxEnd j < y ∧ y ≤ S.boxTop j := by
  classical
  have hex : ∃ j, y ≤ S.boxEnd j := ⟨S.H, h2⟩
  set n := Nat.find hex with hn
  have hspec : y ≤ S.boxEnd n := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro h0; rw [h0, boxEnd_zero] at hspec; linarith
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hmin : ¬ y ≤ S.boxEnd j := Nat.find_min hex (by omega)
  have hnH : n ≤ S.H := Nat.find_min' hex h2
  refine ⟨j, by omega, lt_of_not_ge hmin, ?_⟩
  rw [boxTop_eq hS, show j + 1 = n by omega]; exact hspec

/-- **Every prime `p ≤ z` is low, or high, or equals `u`.** -/
theorem prime_le_ztop (hS : S.Good) {p : ℕ} (hp : p.Prime) (hpz : (p : ℝ) ≤ S.ztop) :
    (p : ℝ) < S.u0 ∨ S.IsHigh p ∨ (p : ℝ) = S.u0 := by
  rcases lt_trichotomy (p : ℝ) S.u0 with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)
  · obtain ⟨j, hj, hb⟩ := exists_box hS h hpz
    exact Or.inr (Or.inl ⟨hp, j, hj, hb⟩)

theorem threshold_le_Dint (hS : S.Good) (J : ℕ) : S.threshold J ≤ S.Dint := by
  unfold threshold
  split_ifs
  · exact le_rfl
  · conv_rhs => rw [← Real.rpow_one S.Dint]
    apply Real.rpow_le_rpow_of_exponent_le (Dint_gt_one hS).le
    rw [div_le_one (by linarith [tau_pos hS])]
    linarith [tau_pos hS]

theorem threshold_pos (hS : S.Good) (J : ℕ) : 0 < S.threshold J := by
  unfold threshold
  split_ifs
  · exact Dint_pos hS
  · exact Real.rpow_pos_of_pos (Dint_pos hS) _

/-- `threshold J ^ (1+τ) ≤ D_int^{1+τ}`, with equality to `D_int` for odd `J`. -/
theorem threshold_rpow_le (hS : S.Good) (J : ℕ) :
    S.threshold J ^ (1 + S.tau) ≤ S.Dint ^ (1 + S.tau) :=
  Real.rpow_le_rpow (threshold_pos hS J).le (threshold_le_Dint hS J) (by linarith [tau_pos hS])

end Erdos287.Physical.Sieve.ScalarParams
