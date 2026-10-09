import Mathlib

/-!
# Erdős #287 — elementary divisor moments for the Urem aggregation

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

Unconditional, fully elementary estimates (no analytic input) used to collapse the family Urem
bound to `O(X/(log X)^A)`:

* `sum_tau_pow_div_le` — `∑_{n ≤ x} τ(n)^k / n ≤ (1 + log x)^{2^k}`.
  Proof: `τ(n)^{k+1} = ∑_{ab = n} τ(n)^k ≤ ∑_{ab=n} τ(a)^k τ(b)^k` (submultiplicativity
  `τ(ab) ≤ τ(a) τ(b)`), so the `k+1` moment is at most the square of the `k` moment; the case
  `k = 0` is the harmonic bound `H_x ≤ 1 + log x`.
* `nat_le_card_divisors_mul_totient` — `n ≤ τ(n) φ(n)` (from `n = ∑_{d ∣ n} φ(d)` and
  `φ(d) ∣ φ(n)`).
* `sum_tau_pow_div_totient_le` — the reciprocal-divisor moment
  `∑_{1 ≤ r < K} τ(r)^B / φ(r) ≤ (1 + log K)^{2^{B+1}}`.
* `sum_tau_pow_le`, `sum_Ico_tau_pow_le` — `∑_{n ≤ x} τ(n)^k ≤ x (1 + log x)^{2^k}`.
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Physical.TypeII.UremFamily

/-- Submultiplicativity of the divisor function, `τ(ab) ≤ τ(a) τ(b)`. -/
lemma card_divisors_mul_le_real (a b : ℕ) :
    (((a * b).divisors.card : ℕ) : ℝ) ≤ (a.divisors.card : ℝ) * b.divisors.card := by
  rw [Nat.divisors_mul]; exact_mod_cast Finset.card_mul_le

/-- Harmonic bound `∑_{n ≤ x} 1/n ≤ 1 + log x`. -/
lemma harmonic_sum_le (x : ℕ) : ∑ n ∈ Icc 1 x, (1 : ℝ) / n ≤ 1 + Real.log x := by
  have h := harmonic_le_one_add_log x
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

lemma one_add_log_nonneg (x : ℕ) : 0 ≤ 1 + Real.log x := by
  have := Real.log_natCast_nonneg x; linarith

/-- `∑_{n ≤ x} ∑_{ab = n} F(a) G(b) ≤ (∑_{a ≤ x} F(a)) (∑_{b ≤ x} G(b))` for `F, G ≥ 0`. -/
lemma sum_antidiag_le_mul (x : ℕ) (F G : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) (hG : ∀ n, 0 ≤ G n) :
    ∑ n ∈ Icc 1 x, ∑ p ∈ n.divisorsAntidiagonal, F p.1 * G p.2 ≤
      (∑ a ∈ Icc 1 x, F a) * (∑ b ∈ Icc 1 x, G b) := by
  classical
  rw [← sum_biUnion]
  · rw [sum_mul_sum, ← sum_product']
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [mem_biUnion, mem_Icc, Nat.mem_divisorsAntidiagonal] at hp
      obtain ⟨n, ⟨h1, h2⟩, hpn, -⟩ := hp
      have hn0 : n ≠ 0 := by omega
      have ha : p.1 ∣ n := ⟨p.2, hpn.symm⟩
      have hb : p.2 ∣ n := ⟨p.1, by rw [← hpn]; ring⟩
      have ha0 : p.1 ≠ 0 := fun h => hn0 (by rw [← hpn, h, zero_mul])
      have hb0 : p.2 ≠ 0 := fun h => hn0 (by rw [← hpn, h, mul_zero])
      have := Nat.le_of_dvd (by omega) ha
      have := Nat.le_of_dvd (by omega) hb
      simp only [mem_product, mem_Icc]
      omega
    · intro p _ _; exact mul_nonneg (hF _) (hG _)
  · intro n _ m _ hnm
    exact Finset.disjoint_left.2 (fun p hp hq => hnm
      ((Nat.mem_divisorsAntidiagonal.1 hp).1.symm.trans (Nat.mem_divisorsAntidiagonal.1 hq).1))

lemma card_divisorsAntidiagonal_eq (n : ℕ) : n.divisorsAntidiagonal.card = n.divisors.card := by
  rw [← Nat.map_div_right_divisors, card_map]

/-- **Logarithmic divisor moments**: `∑_{n ≤ x} τ(n)^k / n ≤ (1 + log x)^{2^k}`. -/
theorem sum_tau_pow_div_le (x k : ℕ) :
    ∑ n ∈ Icc 1 x, ((n.divisors.card : ℝ)) ^ k / n ≤ (1 + Real.log x) ^ (2 ^ k) := by
  induction k with
  | zero => simpa using harmonic_sum_le x
  | succ k ih =>
    have step : ∑ n ∈ Icc 1 x, ((n.divisors.card : ℝ)) ^ (k + 1) / n ≤
        ∑ n ∈ Icc 1 x, ∑ p ∈ n.divisorsAntidiagonal,
          ((p.1.divisors.card : ℝ) ^ k / p.1) * ((p.2.divisors.card : ℝ) ^ k / p.2) := by
      apply sum_le_sum
      intro n _
      have e : ((n.divisors.card : ℝ)) ^ (k + 1) / n =
          ∑ p ∈ n.divisorsAntidiagonal, ((n.divisors.card : ℝ)) ^ k / n := by
        rw [sum_const, card_divisorsAntidiagonal_eq, nsmul_eq_mul, pow_succ]; ring
      rw [e]
      apply sum_le_sum
      intro p hp
      obtain ⟨hpn, -⟩ := Nat.mem_divisorsAntidiagonal.1 hp
      rw [← hpn, div_mul_div_comm, ← mul_pow]
      push_cast
      gcongr
      exact card_divisors_mul_le_real _ _
    refine step.trans ((sum_antidiag_le_mul x (fun a => (a.divisors.card : ℝ) ^ k / a)
      (fun a => (a.divisors.card : ℝ) ^ k / a) (fun n => by positivity)
      (fun n => by positivity)).trans ?_)
    have h0 : 0 ≤ ∑ n ∈ Icc 1 x, ((n.divisors.card : ℝ)) ^ k / n :=
      sum_nonneg (fun _ _ => by positivity)
    have e : (1 + Real.log x) ^ (2 ^ (k + 1)) =
        (1 + Real.log x) ^ (2 ^ k) * (1 + Real.log x) ^ (2 ^ k) := by
      rw [← pow_add]; congr 1; rw [pow_succ]; ring
    rw [e]
    exact mul_le_mul ih ih h0 (h0.trans ih)

/-- `n ≤ τ(n) φ(n)`. -/
theorem nat_le_card_divisors_mul_totient (n : ℕ) :
    (n : ℝ) ≤ (n.divisors.card : ℝ) * (Nat.totient n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h : n ≤ n.divisors.card * Nat.totient n := by
    calc n = ∑ d ∈ n.divisors, Nat.totient d := (Nat.sum_totient n).symm
      _ ≤ ∑ _d ∈ n.divisors, Nat.totient n := by
          apply sum_le_sum
          intro d hd
          exact Nat.le_of_dvd (Nat.totient_pos.2 hn) (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
      _ = n.divisors.card * Nat.totient n := by rw [sum_const, smul_eq_mul]
  exact_mod_cast h

/-- `τ(r)^B / φ(r) ≤ τ(r)^{B+1} / r` for `r ≥ 1`. -/
lemma tau_pow_div_totient_le (B : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    ((r.divisors.card : ℝ)) ^ B / Nat.totient r ≤ ((r.divisors.card : ℝ)) ^ (B + 1) / r := by
  have hφ : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.2 hr
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  rw [div_le_div_iff₀ hφ hr0, pow_succ, mul_assoc]
  exact mul_le_mul_of_nonneg_left (nat_le_card_divisors_mul_totient r) (by positivity)

/-- **Reciprocal-divisor moment**: `∑_{1 ≤ r < K} τ(r)^B / φ(r) ≤ (1 + log K)^{2^{B+1}}`. -/
theorem sum_tau_pow_div_totient_le (K B : ℕ) :
    ∑ r ∈ Ico 1 K, ((r.divisors.card : ℝ)) ^ B / Nat.totient r ≤
      (1 + Real.log K) ^ (2 ^ (B + 1)) := by
  calc ∑ r ∈ Ico 1 K, ((r.divisors.card : ℝ)) ^ B / Nat.totient r
      ≤ ∑ r ∈ Ico 1 K, ((r.divisors.card : ℝ)) ^ (B + 1) / r :=
        sum_le_sum (fun r hr => tau_pow_div_totient_le B (mem_Ico.1 hr).1)
    _ ≤ ∑ r ∈ Icc 1 K, ((r.divisors.card : ℝ)) ^ (B + 1) / r :=
        sum_le_sum_of_subset_of_nonneg Ico_subset_Icc_self (fun _ _ _ => by positivity)
    _ ≤ _ := sum_tau_pow_div_le K (B + 1)

/-- **Divisor moments**: `∑_{n ≤ x} τ(n)^k ≤ x (1 + log x)^{2^k}`. -/
theorem sum_tau_pow_le (x k : ℕ) :
    ∑ n ∈ Icc 1 x, ((n.divisors.card : ℝ)) ^ k ≤ x * (1 + Real.log x) ^ (2 ^ k) := by
  calc ∑ n ∈ Icc 1 x, ((n.divisors.card : ℝ)) ^ k
      ≤ ∑ n ∈ Icc 1 x, (x : ℝ) * (((n.divisors.card : ℝ)) ^ k / n) := by
        apply sum_le_sum
        intro n hn
        obtain ⟨h1, h2⟩ := mem_Icc.1 hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
        have hnx : (n : ℝ) ≤ x := by exact_mod_cast h2
        rw [mul_div_assoc', le_div_iff₀ hn0, mul_comm (x : ℝ)]
        exact mul_le_mul_of_nonneg_left hnx (by positivity)
    _ = x * ∑ n ∈ Icc 1 x, ((n.divisors.card : ℝ)) ^ k / n := by rw [mul_sum]
    _ ≤ x * (1 + Real.log x) ^ (2 ^ k) :=
        mul_le_mul_of_nonneg_left (sum_tau_pow_div_le x k) (Nat.cast_nonneg _)

/-- Dyadic form: `∑_{M ≤ n < 2M} τ(n)^k ≤ 2M (1 + log 2M)^{2^k}`. -/
theorem sum_Ico_tau_pow_le (M k : ℕ) :
    ∑ n ∈ Ico M (2 * M), ((n.divisors.card : ℝ)) ^ k ≤
      ((2 * M : ℕ) : ℝ) * (1 + Real.log ((2 * M : ℕ) : ℝ)) ^ (2 ^ k) := by
  refine le_trans ?_ (sum_tau_pow_le (2 * M) k)
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    rw [mem_Ico] at hn
    rw [mem_Icc]; omega
  · intro _ _ _; positivity

end Erdos287.Physical.TypeII.UremFamily
