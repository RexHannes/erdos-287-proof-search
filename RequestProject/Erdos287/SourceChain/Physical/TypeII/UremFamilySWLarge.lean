import RequestProject.Erdos287.SourceChain.Physical.TypeII.UremFamilySW

/-!
# Erdős #287 — interval Siegel–Walfisz: the large moduli are trivial

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

Maynard's condition (6.1), hence `IntervalSWAt`, is required for **every** modulus `q ≥ 1`,
whereas the published Siegel–Walfisz theorem is stated for `q ≤ (log N)^B`.  This file proves
that, for any sequence bounded by `1` (both `roughOne z₀` and `roughMu z₀` are), the moduli
`q > (log N)^{A+1}` are trivially admissible:

* `card_simN_mod_le` — `#{n ∼ N : n ≡ r (mod q)} ≤ N/q + 3`;
* `card_simN_coprime_le` — `#{n ∼ N : (n, q) = 1} ≤ φ(q) (N/q + 3)`;
* `abs_sum_swW_le` — `|∑_{n ∼ N, n ≤ t} g(n) w_{d,q,a}(n)| ≤ 2(N/q + 3)` for `|g| ≤ 1`;
* `intervalSW_of_small` — `IntervalSWSmall` (the condition for `q ≤ (log N)^{A+1}` only) implies
  `IntervalSWAt` with constants `max(c_A, 7 + 8 A^A)`.

So the analytic input for the actual coefficients is reduced to the small-modulus range, which is
exactly the range of the published Siegel–Walfisz theorem.
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Physical.TypeII.UremFamily

open Erdos287.Physical.TypeII

/-- Interval Siegel–Walfisz restricted to small moduli `q ≤ (log N)^{A+1}`. -/
def IntervalSWSmall (g : ℕ → ℝ) (N B0 : ℝ) (cSW : ℝ → ℝ) : Prop :=
  ∀ t : ℕ, ∀ d q a : ℕ, 1 ≤ d → 1 ≤ q → Nat.Coprime a q → ∀ A : ℝ, 1 < A →
    (q : ℝ) ≤ Real.log N ^ (A + 1) →
    |∑ n ∈ simN N with n ≤ t, g n * swW d q a n| ≤ cSW A * N * tau d ^ B0 / Real.log N ^ A

lemma mem_simN_iff {N : ℝ} {n : ℕ} : n ∈ simN N ↔ n ≤ ⌊2 * N⌋₊ ∧ N < n := by
  simp [simN]

/-- `#{n ∼ N : n ≡ r (mod q)} ≤ N/q + 3`. -/
theorem card_simN_mod_le {N : ℝ} (hN : 0 ≤ N) {q : ℕ} (hq : 1 ≤ q) (r : ℕ) :
    (((simN N).filter (fun n => n % q = r)).card : ℝ) ≤ N / q + 4 := by
  set s := (simN N).filter (fun n => n % q = r) with hs
  have hinj : Set.InjOn (fun n => n / q) (s : Set ℕ) := by
    intro x hx y hy hxy
    simp only [hs, coe_filter, Set.mem_setOf_eq] at hx hy
    have := Nat.div_add_mod x q
    have := Nat.div_add_mod y q
    simp only at hxy
    rw [← Nat.div_add_mod x q, ← Nat.div_add_mod y q, hxy, hx.2, hy.2]
  have himg : s.image (fun n => n / q) ⊆ Icc (⌊N⌋₊ / q) (⌊2 * N⌋₊ / q) := by
    intro k hk
    rw [mem_image] at hk
    obtain ⟨n, hn, rfl⟩ := hk
    rw [hs, mem_filter, mem_simN_iff] at hn
    rw [mem_Icc]
    refine ⟨Nat.div_le_div_right ?_, Nat.div_le_div_right hn.1.1⟩
    have : (⌊N⌋₊ : ℝ) ≤ n := le_trans (Nat.floor_le hN) hn.1.2.le
    exact_mod_cast this
  have hcard : s.card ≤ ⌊2 * N⌋₊ / q + 1 - ⌊N⌋₊ / q := by
    rw [← card_image_of_injOn hinj]
    exact (card_le_card himg).trans (by rw [Nat.card_Icc])
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  -- real bounds on the two quotients
  have h1 : ((⌊2 * N⌋₊ / q : ℕ) : ℝ) ≤ 2 * N / q := by
    rw [le_div_iff₀ hq0]
    have := Nat.div_mul_le_self ⌊2 * N⌋₊ q
    have h' : ((⌊2 * N⌋₊ / q * q : ℕ) : ℝ) ≤ (⌊2 * N⌋₊ : ℝ) := by exact_mod_cast this
    push_cast at h'
    exact h'.trans (Nat.floor_le (by linarith))
  have h2 : N / q - 2 ≤ ((⌊N⌋₊ / q : ℕ) : ℝ) := by
    have hlt := Nat.lt_div_mul_add (a := ⌊N⌋₊) hq
    have h' : (⌊N⌋₊ : ℝ) < ((⌊N⌋₊ / q : ℕ) : ℝ) * q + q := by exact_mod_cast hlt
    have hfl : N < (⌊N⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one N
    have : N / q < ((⌊N⌋₊ / q : ℕ) : ℝ) + 1 + 1 / q := by
      rw [div_lt_iff₀ hq0]
      have : ((⌊N⌋₊ / q : ℕ) : ℝ) * q + q + 1 = (((⌊N⌋₊ / q : ℕ) : ℝ) + 1 + 1 / q) * q := by
        field_simp
      linarith
    have : 1 / (q : ℝ) ≤ 1 := by
      rw [div_le_one hq0]; exact_mod_cast hq
    linarith
  have hc : (s.card : ℝ) ≤ ((⌊2 * N⌋₊ / q + 1 - ⌊N⌋₊ / q : ℕ) : ℝ) := by exact_mod_cast hcard
  refine hc.trans ?_
  have hNq0 : 0 ≤ N / q := div_nonneg hN hq0.le
  rcases le_or_gt (⌊N⌋₊ / q) (⌊2 * N⌋₊ / q + 1) with h | h
  · rw [Nat.cast_sub h]; push_cast
    have : 2 * N / q - N / q = N / q := by ring
    linarith
  · rw [Nat.sub_eq_zero_of_le h.le]; push_cast; linarith

/-- `#{n ∼ N : (n, q) = 1} ≤ φ(q) (N/q + 3)`. -/
theorem card_simN_coprime_le {N : ℝ} (hN : 0 ≤ N) {q : ℕ} (hq : 1 ≤ q) :
    (((simN N).filter (fun n => Nat.Coprime n q)).card : ℝ) ≤
      (Nat.totient q : ℝ) * (N / q + 4) := by
  set s := (simN N).filter (fun n => Nat.Coprime n q) with hs
  set U := (range q).filter (fun b => Nat.Coprime q b) with hU
  have hmaps : ∀ n ∈ s, n % q ∈ U := by
    intro n hn
    rw [hs, mem_filter] at hn
    rw [hU, mem_filter, mem_range]
    refine ⟨Nat.mod_lt _ (by omega), ?_⟩
    show Nat.gcd q (n % q) = 1
    rw [Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]; exact hn.2
  rw [card_eq_sum_card_fiberwise (f := fun n => n % q) (t := U) (fun n hn => hmaps n hn)]
  have hfib : ∀ b ∈ U, ((s.filter (fun n => n % q = b)).card : ℝ) ≤ N / q + 4 := by
    intro b _
    refine le_trans ?_ (card_simN_mod_le hN hq b)
    exact_mod_cast card_le_card (fun n hn => by
      rw [mem_filter] at hn ⊢; exact ⟨(mem_filter.1 hn.1).1, hn.2⟩)
  push_cast
  refine (sum_le_sum hfib).trans ?_
  rw [sum_const, nsmul_eq_mul]
  unfold Nat.totient
  rw [hU]

/-- **Trivial bound for the SW weight.** -/
theorem abs_sum_swW_le {g : ℕ → ℝ} (hg : ∀ n, |g n| ≤ 1) {N : ℝ} (hN : 0 ≤ N) (t : ℕ)
    {d q a : ℕ} (hq : 1 ≤ q) :
    |∑ n ∈ simN N with n ≤ t, g n * swW d q a n| ≤ 2 * (N / q + 4) := by
  set I := (simN N).filter (fun n => n ≤ t) with hI
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hterm : ∀ n ∈ I, |g n * swW d q a n| ≤
      (if n % q = a % q then 1 else 0) + (1 / (Nat.totient q : ℝ)) *
        (if Nat.Coprime n q then 1 else 0) := by
    intro n _
    rw [abs_mul]
    have hsw : |swW d q a n| ≤ (if n % q = a % q then 1 else 0) + (1 / (Nat.totient q : ℝ)) *
        (if Nat.Coprime n q then 1 else 0) := by
      unfold swW
      refine (abs_sub _ _).trans ?_
      have h1 : |(if n ≡ a [MOD q] ∧ Nat.Coprime n d then (1 : ℝ) else 0)| ≤
          (if n % q = a % q then 1 else 0) := by
        split_ifs with ha hb hb <;> simp_all [Nat.ModEq]
      have h2 : |(1 / (Nat.totient q : ℝ)) * (if Nat.Coprime n (d * q) then 1 else 0)| ≤
          (1 / (Nat.totient q : ℝ)) * (if Nat.Coprime n q then 1 else 0) := by
        rw [abs_mul, abs_of_pos (by positivity)]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        split_ifs with ha hb hb
        · simp
        · exact absurd (Nat.Coprime.coprime_mul_left_right ha) hb
        · simp
        · simp
      linarith
    calc |g n| * |swW d q a n| ≤ 1 * |swW d q a n| :=
          mul_le_mul_of_nonneg_right (hg n) (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hsw
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [sum_add_distrib, ← mul_sum]
  have hc1 : ∑ n ∈ I, (if n % q = a % q then (1 : ℝ) else 0) ≤ N / q + 4 := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    refine le_trans ?_ (card_simN_mod_le hN hq (a % q))
    exact_mod_cast card_le_card (fun n hn => by
      simp only [hI, mem_filter] at hn ⊢; exact ⟨hn.1.1, hn.2⟩)
  have hc2 : ∑ n ∈ I, (if Nat.Coprime n q then (1 : ℝ) else 0) ≤
      (Nat.totient q : ℝ) * (N / q + 4) := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    refine le_trans ?_ (card_simN_coprime_le hN hq)
    exact_mod_cast card_le_card (fun n hn => by
      simp only [hI, mem_filter] at hn ⊢; exact ⟨hn.1.1, hn.2⟩)
  have : (1 / (Nat.totient q : ℝ)) * ∑ n ∈ I, (if Nat.Coprime n q then (1 : ℝ) else 0) ≤
      N / q + 4 := by
    rw [one_div, inv_mul_le_iff₀ hφ]; exact hc2
  linarith

/-- `(log N)^A ≤ A^A N` for `N ≥ 1`, `A > 0`. -/
lemma log_rpow_le (N A : ℝ) (hN : 1 ≤ N) (hA : 0 < A) : Real.log N ^ A ≤ A ^ A * N := by
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg hN
  have h := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ N) (inv_pos.2 hA)
  have h' : Real.log N ≤ A * N ^ A⁻¹ := by rw [div_inv_eq_mul] at h; linarith
  calc Real.log N ^ A ≤ (A * N ^ A⁻¹) ^ A := Real.rpow_le_rpow hl0 h' hA.le
    _ = A ^ A * N := by
        rw [Real.mul_rpow hA.le (by positivity), ← Real.rpow_mul (by linarith),
          inv_mul_cancel₀ hA.ne', Real.rpow_one]

/-- **Large moduli are trivial**: small-modulus interval SW for a `1`-bounded sequence gives the
full `IntervalSWAt` (every `q ≥ 1`) with constants `max(c_A, 7 + 8 A^A)`. -/
theorem intervalSW_of_small {g : ℕ → ℝ} (hg : ∀ n, |g n| ≤ 1) {N B0 : ℝ} (hN : 2 ≤ N)
    (hB0 : 0 ≤ B0) {cSW : ℝ → ℝ} (h : IntervalSWSmall g N B0 cSW) :
    IntervalSWAt g N B0 (fun A => max (cSW A) (7 + 8 * A ^ A)) := by
  intro t d q a hd hq haq A hA
  have hlN : 0 < Real.log N := Real.log_pos (by linarith)
  have hτ : 1 ≤ tau d ^ B0 := Real.one_le_rpow (one_le_tau hd) hB0
  have hpA : 0 < Real.log N ^ A := Real.rpow_pos_of_pos hlN _
  by_cases hsmall : (q : ℝ) ≤ Real.log N ^ (A + 1)
  · refine (h t d q a hd hq haq A hA hsmall).trans ?_
    apply div_le_div_of_nonneg_right _ hpA.le
    have : 0 ≤ N * tau d ^ B0 := by positivity
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) this
  · push_neg at hsmall
    refine (abs_sum_swW_le hg (by linarith) t hq).trans ?_
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    -- `2N/q ≤ 2N/(log N)^{A+1}` and `(log N)^{A+1} ≥ (log N)^A · log 2`
    have hl2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN
    have hl2' : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hpA1 : Real.log N ^ (A + 1) = Real.log N ^ A * Real.log N := by
      rw [Real.rpow_add hlN, Real.rpow_one]
    have hNq : N / q ≤ 2 * N / Real.log N ^ A := by
      rw [div_le_div_iff₀ hq0 hpA]
      have : Real.log N ^ A * (1 / 2) ≤ Real.log N ^ A * Real.log N :=
        mul_le_mul_of_nonneg_left (by linarith) hpA.le
      nlinarith
    have hconst : (8 : ℝ) ≤ 8 * A ^ A * N / Real.log N ^ A := by
      rw [le_div_iff₀ hpA]
      have := log_rpow_le N A (by linarith) (by linarith)
      linarith
    have hfinal : 2 * (N / q + 4) ≤ (7 + 8 * A ^ A) * N / Real.log N ^ A := by
      have e : (7 + 8 * A ^ A) * N / Real.log N ^ A =
          7 * N / Real.log N ^ A + 8 * A ^ A * N / Real.log N ^ A := by ring
      rw [e]
      have : 2 * (2 * N / Real.log N ^ A) ≤ 7 * N / Real.log N ^ A := by
        rw [← mul_div_assoc]
        apply div_le_div_of_nonneg_right _ hpA.le
        linarith
      linarith
    refine hfinal.trans ?_
    have hmax : 7 + 8 * A ^ A ≤ max (cSW A) (7 + 8 * A ^ A) := le_max_right _ _
    have h7 : 0 ≤ 7 + 8 * A ^ A := by positivity
    calc (7 + 8 * A ^ A) * N / Real.log N ^ A
        ≤ max (cSW A) (7 + 8 * A ^ A) * N / Real.log N ^ A := by
          apply div_le_div_of_nonneg_right _ hpA.le
          exact mul_le_mul_of_nonneg_right hmax (by linarith)
      _ ≤ max (cSW A) (7 + 8 * A ^ A) * N * tau d ^ B0 / Real.log N ^ A := by
          apply div_le_div_of_nonneg_right _ hpA.le
          have : 0 ≤ max (cSW A) (7 + 8 * A ^ A) * N := by
            have := le_trans h7 hmax; positivity
          nlinarith

/-- Both actual base sequences are bounded by `1`. -/
lemma abs_roughOne_le (z₀ n : ℕ) : |roughOne z₀ n| ≤ 1 := by
  unfold roughOne; split_ifs <;> simp

lemma abs_roughMu_le (z₀ n : ℕ) : |roughMu z₀ n| ≤ 1 := by
  unfold roughMu; split_ifs
  · exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  · simp

end Erdos287.Physical.TypeII.UremFamily
