import Mathlib

/-!
# Window lemma for reciprocal representations of `1`

If `A` is a finite set of positive integers with `∑_{n ∈ A} 1/n = 1`, and `p^a` is a prime power
whose set of multiples up to `max A` is very short, then a `p`-adic valuation argument shows that
`A` contains no multiple of `p^a` at all.

The precise statement is `Erdos287.no_dvd_of_window`.
-/

namespace Erdos287

open Finset

/-- A finite sum of rationals each of positive `p`-adic valuation, which is itself nonzero,
has positive `p`-adic valuation. -/
theorem padicValRat_sum_pos {p : ℕ} [Fact p.Prime] {ι : Type*}
    {S : Finset ι} {F : ι → ℚ}
    (hF : ∀ i ∈ S, 0 < padicValRat p (F i)) (h0 : ∑ i ∈ S, F i ≠ 0) :
    0 < padicValRat p (∑ i ∈ S, F i) := by
  classical
  induction S using Finset.induction with
  | empty => simp at h0
  | insert x s hx ih =>
      rw [Finset.sum_insert hx] at h0 ⊢
      by_cases hs : ∑ i ∈ s, F i = 0
      · rw [hs, add_zero]; exact hF x (by simp)
      · refine lt_of_lt_of_le ?_ (padicValRat.min_le_padicValRat_add h0)
        exact lt_min (hF x (by simp)) (ih (fun i hi => hF i (by simp [hi])) hs)

/-- The `p`-adic valuation of `n` is `< a` exactly when `p ^ a` does not divide `n`. -/
theorem padicValNat_lt_of_not_pow_dvd {p n a : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (h : ¬ p ^ a ∣ n) : padicValNat p n < a := by
  rw [hp.pow_dvd_iff_le_factorization hn, Nat.factorization_def _ hp] at h
  omega

/--
**Window lemma.**  Let `A` be a finite set of positive integers whose reciprocals sum to `1`.
Let `p` be a prime and `a ≥ 1`.  Assume

* every element of `A` is `< (w + 1) * p ^ a`  (so the multiples of `p ^ a` occurring in `A`
  are among `1 * p ^ a, …, w * p ^ a`).

Let `L` be a common multiple of `1, …, w` which is not divisible by `p`, and assume that for every
nonempty `J ⊆ {1, …, w}` the integer `∑_{j ∈ J} L / j` is not divisible by `p`.

Then `A` contains no multiple of `p ^ a`.
-/
theorem no_dvd_of_window {A : Finset ℕ} (hA0 : ∀ n ∈ A, 0 < n)
    (hsum : ∑ n ∈ A, (1 : ℚ) / n = 1)
    {p a w L : ℕ} (hp : p.Prime) (ha : 0 < a)
    (hwin : ∀ n ∈ A, n < (w + 1) * p ^ a)
    (hL0 : 0 < L)
    (hLdvd : ∀ j ∈ Finset.Icc 1 w, j ∣ L)
    (hpL : ¬ p ∣ L)
    (hcond : ∀ J : Finset ℕ, J ⊆ Finset.Icc 1 w → J.Nonempty → ¬ p ∣ ∑ j ∈ J, L / j) :
    ∀ n ∈ A, ¬ p ^ a ∣ n := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.pos
  have hpQ : ((p : ℚ)) ≠ 0 := ne_of_gt hp0
  have hpa0 : 0 < p ^ a := Nat.pow_pos hp.pos
  by_contra hcon
  push_neg at hcon
  obtain ⟨n₀, hn₀A, hn₀d⟩ := hcon
  set B := A.filter (fun n => p ^ a ∣ n) with hBdef
  set C := A.filter (fun n => ¬ p ^ a ∣ n) with hCdef
  have hBmem : ∀ n ∈ B, n ∈ A ∧ p ^ a ∣ n := by
    intro n hn; simpa [hBdef] using hn
  have hCmem : ∀ n ∈ C, n ∈ A ∧ ¬ p ^ a ∣ n := by
    intro n hn; simpa [hCdef] using hn
  have hn₀B : n₀ ∈ B := by simp [hBdef, hn₀A, hn₀d]
  -- multiply the reciprocal identity by `p ^ a`
  have key : ∑ n ∈ A, (p : ℚ) ^ a / n = (p : ℚ) ^ a := by
    calc ∑ n ∈ A, (p : ℚ) ^ a / n = (p : ℚ) ^ a * ∑ n ∈ A, (1 : ℚ) / n := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
      _ = (p : ℚ) ^ a := by rw [hsum, mul_one]
  have hsplit : (∑ n ∈ B, (p : ℚ) ^ a / n) + (∑ n ∈ C, (p : ℚ) ^ a / n) = (p : ℚ) ^ a := by
    rw [hBdef, hCdef, Finset.sum_filter_add_sum_filter_not]; exact key
  ---------------------------------------------------------------------------
  -- The `B` part equals `m / L` for the natural number `m = ∑_{j ∈ J} L / j`.
  ---------------------------------------------------------------------------
  set J : Finset ℕ := B.image (fun n => n / p ^ a) with hJdef
  have hJsub : J ⊆ Finset.Icc 1 w := by
    intro j hj
    simp only [hJdef, Finset.mem_image] at hj
    obtain ⟨n, hnB, rfl⟩ := hj
    obtain ⟨hnA, hnd⟩ := hBmem n hnB
    have hn0 : 0 < n := hA0 n hnA
    have hne : n / p ^ a * p ^ a = n := Nat.div_mul_cancel hnd
    have h1 : 1 ≤ n / p ^ a := by
      rcases Nat.eq_zero_or_pos (n / p ^ a) with h | h
      · rw [h] at hne; omega
      · exact h
    have h2 : n / p ^ a ≤ w := by
      by_contra hc
      push_neg at hc
      have : (w + 1) * p ^ a ≤ n := by
        calc (w + 1) * p ^ a ≤ (n / p ^ a) * p ^ a := Nat.mul_le_mul_right _ hc
          _ = n := hne
      exact absurd (hwin n hnA) (by omega)
    simp [Finset.mem_Icc, h1, h2]
  have hJne : J.Nonempty := ⟨n₀ / p ^ a, by simp only [hJdef, Finset.mem_image]; exact ⟨n₀, hn₀B, rfl⟩⟩
  have hinj : Set.InjOn (fun n => n / p ^ a) (B : Set ℕ) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe] at hx hy
    obtain ⟨_, hxd⟩ := hBmem x hx
    obtain ⟨_, hyd⟩ := hBmem y hy
    have h1 := Nat.div_mul_cancel hxd
    have h2 := Nat.div_mul_cancel hyd
    simp only at hxy
    rw [← h1, ← h2, hxy]
  have hBsum : ∑ n ∈ B, (p : ℚ) ^ a / n = ∑ j ∈ J, (1 : ℚ) / j := by
    rw [hJdef, Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hnA, hnd⟩ := hBmem n hn
    have hn0 : 0 < n := hA0 n hnA
    obtain ⟨j, rfl⟩ := hnd
    have hj0 : 0 < j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; simp at hn0
      · exact h
    rw [Nat.mul_div_cancel_left j hpa0]
    have h2 : ((j : ℚ)) ≠ 0 := by positivity
    push_cast
    field_simp
  set m : ℕ := ∑ j ∈ J, L / j with hmdef
  have hJpos : ∀ j ∈ J, 0 < j := fun j hj => (Finset.mem_Icc.1 (hJsub hj)).1
  have hJdvd : ∀ j ∈ J, j ∣ L := fun j hj => hLdvd j (hJsub hj)
  have hmQ : ((m : ℚ)) = ∑ j ∈ J, (L : ℚ) / j := by
    rw [hmdef]
    push_cast
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj0 : ((j : ℚ)) ≠ 0 := by
      have := hJpos j hj; positivity
    exact Nat.cast_div (hJdvd j hj) hj0
  have hLQ : ((L : ℚ)) ≠ 0 := by positivity
  have hBsum2 : ∑ n ∈ B, (p : ℚ) ^ a / n = (m : ℚ) / (L : ℚ) := by
    rw [hBsum, hmQ, Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj0 : ((j : ℚ)) ≠ 0 := by have := hJpos j hj; positivity
    field_simp
  have hm0 : 0 < m := by
    obtain ⟨j, hj⟩ := hJne
    have hjL : 0 < L / j := Nat.div_pos (Nat.le_of_dvd hL0 (hJdvd j hj)) (hJpos j hj)
    exact lt_of_lt_of_le hjL (Finset.single_le_sum (f := fun j => L / j) (fun _ _ => Nat.zero_le _) hj)
  ---------------------------------------------------------------------------
  -- Valuation bookkeeping.
  ---------------------------------------------------------------------------
  have hBpos : (0 : ℚ) < ∑ n ∈ B, (p : ℚ) ^ a / n := by
    refine Finset.sum_pos' (fun n hn => ?_) ⟨n₀, hn₀B, ?_⟩
    · have := hA0 n (hBmem n hn).1; positivity
    · have h := hA0 n₀ hn₀A
      have : (0:ℚ) < (n₀ : ℚ) := by exact_mod_cast h
      positivity
  have hBne : (∑ n ∈ B, (p : ℚ) ^ a / n) ≠ 0 := ne_of_gt hBpos
  have hvalB : 0 < padicValRat p (∑ n ∈ B, (p : ℚ) ^ a / n) := by
    have hCval : ∀ n ∈ C, 0 < padicValRat p ((p : ℚ) ^ a / n) := by
      intro n hn
      obtain ⟨hnA, hnd⟩ := hCmem n hn
      have hn0 : 0 < n := hA0 n hnA
      have hnQ : ((n : ℚ)) ≠ 0 := by positivity
      rw [padicValRat.div (by positivity) hnQ, padicValRat.pow hpQ,
        padicValRat.self hp.one_lt, mul_one, padicValRat.of_nat]
      have := padicValNat_lt_of_not_pow_dvd hp hn0.ne' hnd
      omega
    have hBeq : ∑ n ∈ B, (p : ℚ) ^ a / n = (p : ℚ) ^ a + (-(∑ n ∈ C, (p : ℚ) ^ a / n)) := by
      linarith [hsplit]
    have hvalpa : 0 < padicValRat p ((p : ℚ) ^ a) := by
      rw [padicValRat.pow hpQ, padicValRat.self hp.one_lt, mul_one]
      exact_mod_cast ha
    by_cases hC : ∑ n ∈ C, (p : ℚ) ^ a / n = 0
    · rw [hBeq, hC, neg_zero, add_zero]; exact hvalpa
    · have h1 : 0 < padicValRat p (∑ n ∈ C, (p : ℚ) ^ a / n) :=
        padicValRat_sum_pos hCval hC
      have h2 : 0 < padicValRat p (-(∑ n ∈ C, (p : ℚ) ^ a / n)) := by
        rwa [padicValRat.neg]
      rw [hBeq]
      refine lt_of_lt_of_le (lt_min hvalpa h2) (padicValRat.min_le_padicValRat_add ?_)
      rw [← hBeq]; exact hBne
  -- conclude `p ∣ m`
  have hvalm : 0 < padicValRat p ((m : ℚ) / (L : ℚ)) := by rwa [hBsum2] at hvalB
  rw [padicValRat.div (by exact_mod_cast hm0.ne') hLQ, padicValRat.of_nat,
    padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hpL] at hvalm
  have hpm : p ∣ m := by
    by_contra hc
    rw [padicValNat.eq_zero_of_not_dvd hc] at hvalm
    simp at hvalm
  exact hcond J hJsub hJne hpm

end Erdos287
