import Mathlib

/-!
# Erdős #287 — post-V87 → V90R: the repaired pair-energy (moment) consumer

**ERDŐS #287 REMAINS OPEN.  This file is finite probability / real algebra only.**

We work in a *finite* weighted probability space `F : FiniteWeights` (finitely many integer
parameters `t ∈ F.T` with non-negative weights summing to one), so there is no hidden
measure-theoretic content.  For non-negative integer block counts `Y t j` (blocks `j` in a
finite type `ι`) put

* `P t = ∑ⱼ Y t j`, `Q t = ∑ⱼ C(Y t j, 2)`, `Z t = #{j : Y t j > 0}`.

Results (all unconditional):

* `pointwise_cauchy` — `P² ≤ Z (P + 2Q)` at every parameter;
* `moment_cauchy` — `(𝔼P)² ≤ (𝔼Z)(𝔼P + 2𝔼Q)`, hence `𝔼Z ≥ (𝔼P)²/(𝔼P + 2𝔼Q)`
  (`expected_occupancy_lower`);
* `exists_occupancy_of_moment` — if `(𝔼P)² > m(𝔼P + 2𝔼Q)` there is a parameter `t`
  **of positive weight** with `Z t ≥ m + 1` (an actual existence theorem);
* `moment_numerical` / `occupancy_of_normalized_moments` — the `C`-normalisation: from
  `𝔼P ≥ μ > 0`, `𝔼Q ≤ C μ²/(2r)`, `C < r/m` and `μ > m r/(r - m C)`, occupancy `≥ m + 1`;
* `occupancy_11_3` — the specialisation `r = 11`, `m = 3`: `C < 11/3` **together with**
  `μ > 33/(11 - 3C)`;
* `qbal_le_pairs` — the exact integer balancing lemma: if at most `m` blocks are occupied,
  `∑ⱼ C(Yⱼ,2) ≥ q_m(∑ⱼ Yⱼ)` where `q_m(n) = ∑_{i<n} ⌊i/m⌋` is the balanced pair count;
* `sharp_mean_consumer` — the finite-weight Jensen version: if `Z ≤ m` on the support then
  `𝔼Q ≥ q̃_m(𝔼P)` (piecewise-linear interpolation of `q_m`), hence
  `exists_occupancy_of_sharp`: `𝔼Q < q̃_m(𝔼P)` ⟹ a parameter with `Z ≥ m + 1`.

The obsolete constant `11/6` is **not** used anywhere; see `RegressionSuite.lean`.
-/

open scoped BigOperators
open Finset

namespace Erdos287.PostV87V90R

/-- A finite weighted probability space on integer parameters. -/
structure FiniteWeights where
  /-- The finite parameter set. -/
  T : Finset ℕ
  /-- The weights. -/
  w : ℕ → ℝ
  w_nonneg : ∀ t ∈ T, 0 ≤ w t
  w_sum : ∑ t ∈ T, w t = 1

namespace FiniteWeights

variable (F : FiniteWeights)

/-- Expectation. -/
noncomputable def E (f : ℕ → ℝ) : ℝ := ∑ t ∈ F.T, F.w t * f t

theorem E_const (c : ℝ) : F.E (fun _ => c) = c := by
  simp [E, ← Finset.sum_mul, F.w_sum]

theorem E_add (f g : ℕ → ℝ) : F.E (fun t => f t + g t) = F.E f + F.E g := by
  simp [E, mul_add, Finset.sum_add_distrib]

theorem E_smul (c : ℝ) (f : ℕ → ℝ) : F.E (fun t => c * f t) = c * F.E f := by
  simp [E, Finset.mul_sum]; refine Finset.sum_congr rfl fun t _ => by ring

theorem E_mono {f g : ℕ → ℝ} (h : ∀ t ∈ F.T, 0 < F.w t → f t ≤ g t) : F.E f ≤ F.E g := by
  unfold E
  apply Finset.sum_le_sum
  intro t ht
  rcases (F.w_nonneg t ht).lt_or_eq with hw | hw
  · exact mul_le_mul_of_nonneg_left (h t ht hw) hw.le
  · rw [← hw]; simp

theorem E_nonneg {f : ℕ → ℝ} (h : ∀ t ∈ F.T, 0 ≤ f t) : 0 ≤ F.E f :=
  Finset.sum_nonneg fun t ht => mul_nonneg (F.w_nonneg t ht) (h t ht)

end FiniteWeights

/-! ## Block statistics -/

section Blocks

variable {ι : Type*} [Fintype ι]

/-- Total count `P = ∑ⱼ Yⱼ`. -/
def Pcount (Y : ℕ → ι → ℕ) (t : ℕ) : ℕ := ∑ j, Y t j

/-- Pair count `Q = ∑ⱼ C(Yⱼ, 2)`. -/
def Qcount (Y : ℕ → ι → ℕ) (t : ℕ) : ℕ := ∑ j, (Y t j).choose 2

/-- Number of occupied blocks `Z = #{j : Yⱼ > 0}`. -/
def Zcount (Y : ℕ → ι → ℕ) (t : ℕ) : ℕ := (univ.filter (fun j => 0 < Y t j)).card

theorem sq_eq_add_two_choose (n : ℕ) : n ^ 2 = n + 2 * n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith [ih]

theorem sq_eq_add_two_choose_real (n : ℕ) : (n : ℝ) ^ 2 = n + 2 * (n.choose 2 : ℝ) := by
  exact_mod_cast sq_eq_add_two_choose n

/-- `P + 2Q = ∑ⱼ Yⱼ²`. -/
theorem P_add_two_Q (Y : ℕ → ι → ℕ) (t : ℕ) :
    (Pcount Y t : ℝ) + 2 * Qcount Y t = ∑ j, ((Y t j : ℕ) : ℝ) ^ 2 := by
  simp only [Pcount, Qcount, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => (sq_eq_add_two_choose_real _).symm

theorem Zcount_eq_sum (Y : ℕ → ι → ℕ) (t : ℕ) :
    (Zcount Y t : ℝ) = ∑ j, (if 0 < Y t j then (1 : ℝ) else 0) := by
  simp [Zcount]

/-- **Pointwise Cauchy:** `P² ≤ Z (P + 2Q)`. -/
theorem pointwise_cauchy (Y : ℕ → ι → ℕ) (t : ℕ) :
    (Pcount Y t : ℝ) ^ 2 ≤ Zcount Y t * ((Pcount Y t : ℝ) + 2 * Qcount Y t) := by
  rw [P_add_two_Q, Zcount_eq_sum]
  have : (Pcount Y t : ℝ) = ∑ j, ((Y t j : ℕ) : ℝ) := by simp [Pcount]
  rw [this]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro j _; split_ifs <;> norm_num
  · intro j _; positivity
  · intro j _
    split_ifs with h
    · ring
    · have : Y t j = 0 := by omega
      simp [this]

variable (F : FiniteWeights)

/-- **Expectation Cauchy:** `(𝔼P)² ≤ (𝔼Z)(𝔼P + 2𝔼Q)`. -/
theorem moment_cauchy (Y : ℕ → ι → ℕ) :
    F.E (fun t => Pcount Y t) ^ 2 ≤
      F.E (fun t => Zcount Y t) * (F.E (fun t => Pcount Y t) + 2 * F.E (fun t => Qcount Y t)) := by
  have hP : F.E (fun t => Pcount Y t) = ∑ x ∈ F.T ×ˢ (univ : Finset ι), F.w x.1 * Y x.1 x.2 := by
    simp [FiniteWeights.E, Pcount, Finset.sum_product, Finset.mul_sum]
  have hZ : F.E (fun t => Zcount Y t) =
      ∑ x ∈ F.T ×ˢ (univ : Finset ι), F.w x.1 * (if 0 < Y x.1 x.2 then (1 : ℝ) else 0) := by
    simp only [FiniteWeights.E, Zcount_eq_sum, Finset.sum_product, Finset.mul_sum]
  have hS : F.E (fun t => Pcount Y t) + 2 * F.E (fun t => Qcount Y t) =
      ∑ x ∈ F.T ×ˢ (univ : Finset ι), F.w x.1 * ((Y x.1 x.2 : ℕ) : ℝ) ^ 2 := by
    rw [← F.E_smul, ← F.E_add]
    simp only [FiniteWeights.E, P_add_two_Q, Finset.sum_product, Finset.mul_sum]
  rw [hS, hP, hZ]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro x hx
    have := F.w_nonneg x.1 (Finset.mem_product.1 hx).1
    split_ifs <;> simp [this]
  · intro x hx
    have := F.w_nonneg x.1 (Finset.mem_product.1 hx).1
    positivity
  · intro x _
    split_ifs with h
    · ring
    · have : Y x.1 x.2 = 0 := by omega
      simp [this]

/-- **Expected occupancy lower bound** `𝔼Z ≥ (𝔼P)²/(𝔼P + 2𝔼Q)` (when the denominator is
positive). -/
theorem expected_occupancy_lower (Y : ℕ → ι → ℕ)
    (hden : 0 < F.E (fun t => Pcount Y t) + 2 * F.E (fun t => Qcount Y t)) :
    F.E (fun t => Pcount Y t) ^ 2 /
        (F.E (fun t => Pcount Y t) + 2 * F.E (fun t => Qcount Y t)) ≤
      F.E (fun t => Zcount Y t) := by
  rw [div_le_iff₀ hden]
  exact moment_cauchy F Y

/-- **Moment-to-occupancy existence theorem.**  If `(𝔼P)² > m (𝔼P + 2𝔼Q)` then some
parameter of positive weight has at least `m + 1` occupied blocks. -/
theorem exists_occupancy_of_moment (Y : ℕ → ι → ℕ) (m : ℕ)
    (h : (m : ℝ) * (F.E (fun t => Pcount Y t) + 2 * F.E (fun t => Qcount Y t)) <
      F.E (fun t => Pcount Y t) ^ 2) :
    ∃ t ∈ F.T, 0 < F.w t ∧ m + 1 ≤ Zcount Y t := by
  by_contra hc
  push_neg at hc
  have hZ : F.E (fun t => Zcount Y t) ≤ m := by
    calc F.E (fun t => Zcount Y t) ≤ F.E (fun _ => (m : ℝ)) := by
          apply F.E_mono
          intro t ht hw
          have := hc t ht hw
          exact_mod_cast (by omega : Zcount Y t ≤ m)
      _ = m := F.E_const _
  have hS : 0 ≤ F.E (fun t => Pcount Y t) + 2 * F.E (fun t => Qcount Y t) := by
    have h1 : 0 ≤ F.E (fun t => Pcount Y t) := F.E_nonneg fun t _ => by positivity
    have h2 : 0 ≤ F.E (fun t => Qcount Y t) := F.E_nonneg fun t _ => by positivity
    linarith
  have := moment_cauchy F Y
  have := mul_le_mul_of_nonneg_right hZ hS
  linarith

/-! ## `C`-normalisation -/

/-- **Numerical core of the `C`-normalisation.**  If `x ≥ μ > 0`, `0 ≤ q ≤ C μ²/(2r)`,
`C < r/m` and `μ > m r/(r - m C)` (with `r > 0`, `m ≥ 1`), then `x² > m (x + 2q)`. -/
theorem moment_numerical {x q μ C r : ℝ} {m : ℕ} (hr : 0 < r) (hm : 1 ≤ m) (hμ : 0 < μ)
    (hx : μ ≤ x) (hq0 : 0 ≤ q) (hq : q ≤ C * μ ^ 2 / (2 * r)) (hC : C < r / m)
    (hμbig : (m : ℝ) * r / (r - m * C) < μ) : (m : ℝ) * (x + 2 * q) < x ^ 2 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hD : 0 < r - m * C := by
    rw [lt_div_iff₀ hmpos] at hC; linarith
  have hC0 : 0 ≤ C := by
    have : 0 ≤ C * μ ^ 2 / (2 * r) := le_trans hq0 hq
    have hpos : 0 < μ ^ 2 / (2 * r) := by positivity
    have : 0 ≤ C * (μ ^ 2 / (2 * r)) := by rw [← mul_div_assoc]; exact this
    exact nonneg_of_mul_nonneg_left this hpos
  have hμD : (m : ℝ) * r < μ * (r - m * C) := by
    rw [div_lt_iff₀ hD] at hμbig; linarith
  -- `μ ≥ m`
  have hμm : (m : ℝ) ≤ μ := by
    have h1 : μ * (r - m * C) ≤ μ * r :=
      mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hmpos.le hC0]) hμ.le
    have h2 : (m : ℝ) * r < μ * r := by linarith
    exact le_of_lt (lt_of_mul_lt_mul_right h2 hr.le)
  -- `μ² - mμ > m C μ²/r`
  have key : (m : ℝ) * C * μ ^ 2 / r < μ ^ 2 - m * μ := by
    rw [div_lt_iff₀ hr]
    nlinarith
  have hq2 : (m : ℝ) * (2 * q) ≤ m * C * μ ^ 2 / r := by
    have : 2 * q ≤ C * μ ^ 2 / r := by
      have := mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 2)
      calc 2 * q ≤ 2 * (C * μ ^ 2 / (2 * r)) := this
        _ = C * μ ^ 2 / r := by field_simp
    calc (m : ℝ) * (2 * q) ≤ m * (C * μ ^ 2 / r) := mul_le_mul_of_nonneg_left this hmpos.le
      _ = m * C * μ ^ 2 / r := by ring
  have hmono : μ ^ 2 - m * μ ≤ x ^ 2 - m * x := by nlinarith
  nlinarith

/-- **Normalised moments ⟹ occupancy.**  With `r > 0`, `m ≥ 1`: if `𝔼P ≥ μ > 0`,
`𝔼Q ≤ C μ²/(2r)`, `C < r/m` and `μ > m r/(r - mC)`, then some parameter of positive weight has
at least `m + 1` occupied blocks. -/
theorem occupancy_of_normalized_moments (Y : ℕ → ι → ℕ) {μ C r : ℝ} {m : ℕ} (hr : 0 < r)
    (hm : 1 ≤ m) (hμ : 0 < μ) (hP : μ ≤ F.E (fun t => Pcount Y t))
    (hQ : F.E (fun t => Qcount Y t) ≤ C * μ ^ 2 / (2 * r)) (hC : C < r / m)
    (hμbig : (m : ℝ) * r / (r - m * C) < μ) :
    ∃ t ∈ F.T, 0 < F.w t ∧ m + 1 ≤ Zcount Y t :=
  exists_occupancy_of_moment F Y m
    (moment_numerical hr hm hμ hP (F.E_nonneg fun t _ => by positivity) hQ hC hμbig)

/-- **Specialisation `r = 11`, `m = 3`:** `C < 11/3` *together with* the first-moment
condition `μ > 33/(11 - 3C)` gives a parameter with at least four occupied blocks. -/
theorem occupancy_11_3 (Y : ℕ → ι → ℕ) {μ C : ℝ} (hμ : 0 < μ)
    (hP : μ ≤ F.E (fun t => Pcount Y t))
    (hQ : F.E (fun t => Qcount Y t) ≤ C * μ ^ 2 / (2 * 11)) (hC : C < 11 / 3)
    (hμbig : 33 / (11 - 3 * C) < μ) :
    ∃ t ∈ F.T, 0 < F.w t ∧ 4 ≤ Zcount Y t := by
  have := occupancy_of_normalized_moments F Y (r := 11) (m := 3) (by norm_num) (by norm_num) hμ
    hP hQ (by norm_num; linarith) (by norm_num; linarith)
  simpa using this

/-! ## Exact integer balancing and the sharp finite-mean consumer -/

/-- The balanced pair count `q_m(n) = ∑_{i<n} ⌊i/m⌋`: the minimum of `∑ C(yⱼ,2)` over
distributions of `n` among at most `m` blocks (attained by the balanced distribution). -/
def qbal (m n : ℕ) : ℕ := ∑ i ∈ range n, i / m

theorem qbal_succ (m n : ℕ) : qbal m (n + 1) = qbal m n + n / m := by
  simp [qbal, Finset.sum_range_succ]

theorem choose_two_eq_pred (k : ℕ) (hk : 1 ≤ k) : k.choose 2 = (k - 1).choose 2 + (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp [Nat.choose_succ_succ, add_comm]

/-- **Exact integer balancing lemma.**  If at most `m` of the counts `yⱼ` are positive then
`q_m(∑ yⱼ) ≤ ∑ C(yⱼ, 2)`. -/
theorem qbal_le_pairs (m : ℕ) : ∀ (n : ℕ) (y : ι → ℕ), ∑ j, y j = n →
    (univ.filter (fun j => 0 < y j)).card ≤ m → qbal m n ≤ ∑ j, (y j).choose 2 := by
  classical
  intro n
  induction n with
  | zero => intro y _ _; simp [qbal]
  | succ n ih =>
    intro y hsum hcard
    have hne : (univ : Finset ι).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h] at hsum; simp at hsum
    obtain ⟨j0, -, hmax⟩ := Finset.exists_max_image univ y hne
    -- `n + 1 ≤ Z · y j0 ≤ m · y j0`
    have hbound : n + 1 ≤ m * y j0 := by
      have h1 : ∑ j, y j = ∑ j ∈ univ.filter (fun j => 0 < y j), y j := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun j _ => by split_ifs with h <;> omega
      have h2 : ∑ j ∈ univ.filter (fun j => 0 < y j), y j ≤
          (univ.filter (fun j => 0 < y j)).card * y j0 := by
        have := Finset.sum_le_card_nsmul (univ.filter (fun j => 0 < y j)) y (y j0)
          (fun j _ => hmax j (mem_univ _))
        simpa using this
      calc n + 1 = ∑ j, y j := hsum.symm
        _ ≤ _ := h1 ▸ h2
        _ ≤ m * y j0 := Nat.mul_le_mul_right _ hcard
    have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h] at hbound; omega
      · exact h
    have hy0 : 1 ≤ y j0 := by
      rcases Nat.eq_zero_or_pos (y j0) with h | h
      · rw [h] at hbound; omega
      · exact h
    set y' : ι → ℕ := Function.update y j0 (y j0 - 1) with hy'
    have hsum' : ∑ j, y' j = n := by
      have e1 := Finset.add_sum_erase univ y (mem_univ j0)
      have e2 := Finset.add_sum_erase univ y' (mem_univ j0)
      have e3 : ∑ j ∈ univ.erase j0, y' j = ∑ j ∈ univ.erase j0, y j :=
        Finset.sum_congr rfl fun j hj => by
          rw [hy', Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      have : y' j0 = y j0 - 1 := by simp [hy']
      omega
    have hcard' : (univ.filter (fun j => 0 < y' j)).card ≤ m := by
      refine le_trans (Finset.card_le_card ?_) hcard
      intro j hj
      simp only [Finset.mem_filter, mem_univ, true_and] at hj ⊢
      by_cases hj0 : j = j0
      · subst hj0; omega
      · rwa [hy', Function.update_of_ne hj0] at hj
    have hih := ih y' hsum' hcard'
    have hpairs : ∑ j, (y j).choose 2 = ∑ j, (y' j).choose 2 + (y j0 - 1) := by
      have e1 := Finset.add_sum_erase univ (fun j => (y j).choose 2) (mem_univ j0)
      have e2 := Finset.add_sum_erase univ (fun j => (y' j).choose 2) (mem_univ j0)
      have e3 : ∑ j ∈ univ.erase j0, (y' j).choose 2 = ∑ j ∈ univ.erase j0, (y j).choose 2 :=
        Finset.sum_congr rfl fun j hj => by
          rw [hy', Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      have : y' j0 = y j0 - 1 := by simp [hy']
      have hc := choose_two_eq_pred (y j0) hy0
      simp only at e1 e2
      rw [this] at e2
      omega
    have hdiv : n / m ≤ y j0 - 1 := by
      have : n / m < y j0 := (Nat.div_lt_iff_lt_mul hm).2 (by rw [mul_comm]; omega)
      omega
    rw [qbal_succ, hpairs]
    omega

/-- Discrete convexity of `q_m`: `q_m(n) ≥ q_m(k) + ⌊k/m⌋ (n - k)` for all `n, k`. -/
theorem qbal_supporting_line (m k n : ℕ) :
    (qbal m k : ℝ) + ((k / m : ℕ) : ℝ) * ((n : ℝ) - k) ≤ qbal m n := by
  rcases le_total k n with hkn | hnk
  · have hsplit : ∑ i ∈ range k, i / m + ∑ i ∈ Ico k n, i / m = ∑ i ∈ range n, i / m :=
      Finset.sum_range_add_sum_Ico _ hkn
    have hlow : (n - k) * (k / m) ≤ ∑ i ∈ Ico k n, i / m := by
      have := Finset.card_nsmul_le_sum (Ico k n) (fun i => i / m) (k / m)
        (fun i hi => Nat.div_le_div_right (Finset.mem_Ico.1 hi).1)
      simpa using this
    have h : qbal m k + (n - k) * (k / m) ≤ qbal m n := by
      unfold qbal; omega
    have hc : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by rw [Nat.cast_sub hkn]
    have : ((qbal m k + (n - k) * (k / m) : ℕ) : ℝ) ≤ qbal m n := by exact_mod_cast h
    push_cast [hc] at this
    linarith
  · have hsplit : ∑ i ∈ range n, i / m + ∑ i ∈ Ico n k, i / m = ∑ i ∈ range k, i / m :=
      Finset.sum_range_add_sum_Ico _ hnk
    have hup : ∑ i ∈ Ico n k, i / m ≤ (k - n) * (k / m) := by
      have := Finset.sum_le_card_nsmul (Ico n k) (fun i => i / m) (k / m)
        (fun i hi => Nat.div_le_div_right (Finset.mem_Ico.1 hi).2.le)
      simpa using this
    have h : qbal m k ≤ qbal m n + (k - n) * (k / m) := by
      unfold qbal; omega
    have hc : ((k - n : ℕ) : ℝ) = (k : ℝ) - n := by rw [Nat.cast_sub hnk]
    have : (qbal m k : ℝ) ≤ ((qbal m n + (k - n) * (k / m) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast [hc] at this
    linarith

/-- The piecewise-linear interpolation `q̃_m(x)` of the balanced pair count. -/
noncomputable def qlin (m : ℕ) (x : ℝ) : ℝ :=
  (qbal m ⌊x⌋₊ : ℝ) + ((⌊x⌋₊ / m : ℕ) : ℝ) * (x - ⌊x⌋₊)

theorem qlin_natCast (m n : ℕ) : qlin m n = qbal m n := by
  simp [qlin]

/-- **Sharp finite-mean consumer (Jensen form).**  If at every parameter of positive weight at
most `m` blocks are occupied, then `𝔼Q ≥ q̃_m(𝔼P)`. -/
theorem sharp_mean_consumer (Y : ℕ → ι → ℕ) (m : ℕ)
    (hZ : ∀ t ∈ F.T, 0 < F.w t → Zcount Y t ≤ m) :
    qlin m (F.E (fun t => Pcount Y t)) ≤ F.E (fun t => Qcount Y t) := by
  set k := ⌊F.E (fun t => Pcount Y t)⌋₊
  have hline : ∀ t ∈ F.T, 0 < F.w t →
      (qbal m k : ℝ) + ((k / m : ℕ) : ℝ) * ((Pcount Y t : ℝ) - k) ≤ Qcount Y t := by
    intro t ht hw
    have h1 := qbal_supporting_line m k (Pcount Y t)
    have h2 : qbal m (Pcount Y t) ≤ Qcount Y t :=
      qbal_le_pairs m (Pcount Y t) (Y t) rfl (hZ t ht hw)
    have : (qbal m (Pcount Y t) : ℝ) ≤ Qcount Y t := by exact_mod_cast h2
    linarith
  have := F.E_mono hline
  rw [F.E_add, F.E_const, F.E_smul] at this
  have hsub : F.E (fun t => (Pcount Y t : ℝ) - k) = F.E (fun t => Pcount Y t) - k := by
    have := F.E_add (fun t => (Pcount Y t : ℝ)) (fun _ => -(k : ℝ))
    rw [F.E_const] at this
    simpa [sub_eq_add_neg] using this
  rw [hsub] at this
  simpa [qlin] using this

/-- **Sharp occupancy existence.**  `𝔼Q < q̃_m(𝔼P)` forces a parameter of positive weight with
at least `m + 1` occupied blocks. -/
theorem exists_occupancy_of_sharp (Y : ℕ → ι → ℕ) (m : ℕ)
    (h : F.E (fun t => Qcount Y t) < qlin m (F.E (fun t => Pcount Y t))) :
    ∃ t ∈ F.T, 0 < F.w t ∧ m + 1 ≤ Zcount Y t := by
  by_contra hc
  push_neg at hc
  have := sharp_mean_consumer F Y m (fun t ht hw => by have := hc t ht hw; omega)
  linarith

end Blocks

end Erdos287.PostV87V90R
