import RequestProject.Erdos287.SourceChain.Physical.Scalar.Levels

/-!
# Erdős #287 — scalar sieve: the low-prime weights `λ^±_low`

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

* `sum_divisors_eq_sum_powerset` — a divisor sum of a function supported on squarefree numbers
  with prime factors in `Q` is a sum over subsets of the `Q`-prime factors;
* `lamLowPlus_sum_ge` — `∑_{b ∣ v} λ⁺_low(b) ≥ 1_{(v, P(u)) = 1}` (upper sieve);
* `lamLowMinus_sum_le` — `∑_{b ∣ v} λ⁻_low(b) ≤ 1_{(v, P(u)) = 1}` (lower sieve; uses
  `u² ≤ D_low`, so the condition `p_1² ≤ D_low` never fails on low primes);
* `lamLowPlus_level`, `lamLowMinus_level` — support in `b ≤ D_low`;
* `lamLow_support` — support on squarefree `b` with all prime factors `< u`.
-/

open scoped BigOperators
open Finset

namespace Erdos287.Physical.Sieve

/-- Divisor sums of functions supported on squarefree numbers with prime factors in `Q`. -/
theorem sum_divisors_eq_sum_powerset {M : Type*} [AddCommMonoid M] {v : ℕ} (hv : v ≠ 0)
    (Q : ℕ → Prop) [DecidablePred Q] (g : ℕ → M)
    (hg : ∀ d, g d ≠ 0 → Squarefree d ∧ ∀ p ∈ d.primeFactors, Q p) :
    ∑ d ∈ v.divisors, g d = ∑ T ∈ (v.primeFactors.filter Q).powerset, g (∏ p ∈ T, p) := by
  refine Finset.sum_bij_ne_zero (fun d _ _ => d.primeFactors) ?_ ?_ ?_ ?_
  · intro d hd hgd
    obtain ⟨-, hQ⟩ := hg d hgd
    rw [Finset.mem_powerset]
    intro p hp
    rw [Finset.mem_filter]
    exact ⟨Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hv hp, hQ p hp⟩
  · intro d1 _ h1 d2 _ h2 heq
    rw [← Nat.prod_primeFactors_of_squarefree (hg d1 h1).1,
      ← Nat.prod_primeFactors_of_squarefree (hg d2 h2).1]
    simp only at heq
    rw [heq]
  · intro T hT hgT
    have hTp : ∀ p ∈ T, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 (Finset.mem_powerset.1 hT hp)).1
    refine ⟨∏ p ∈ T, p, ?_, hgT, Nat.primeFactors_prod hTp⟩
    rw [Nat.mem_divisors]
    refine ⟨?_, hv⟩
    apply Finset.prod_primes_dvd
    · intro p hp; exact (Nat.prime_iff.1 (hTp p hp))
    · intro p hp
      exact Nat.dvd_of_mem_primeFactors (Finset.mem_filter.1 (Finset.mem_powerset.1 hT hp)).1
  · intro d _ hgd
    rw [Nat.prod_primeFactors_of_squarefree (hg d hgd).1]

theorem squarefree_prod_primes' {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) :
    Squarefree (∏ p ∈ T, p) ∧ ArithmeticFunction.cardFactors (∏ p ∈ T, p) = T.card := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T haT ih =>
    have hT' : ∀ p ∈ T, p.Prime := fun p hp => hT p (Finset.mem_insert_of_mem hp)
    have ha : a.Prime := hT a (Finset.mem_insert_self a T)
    obtain ⟨ih1, ih2⟩ := ih hT'
    rw [Finset.prod_insert haT, Finset.card_insert_of_notMem haT]
    have hcop : Nat.Coprime a (∏ p ∈ T, p) := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes ha (hT' q hq)).2 (fun h => haT (h ▸ hq))
    refine ⟨Nat.squarefree_mul_iff.2 ⟨hcop, ha.squarefree, ih1⟩, ?_⟩
    rw [ArithmeticFunction.cardFactors_mul ha.ne_zero
      (Finset.prod_ne_zero_iff.2 (fun p hp => (hT' p hp).ne_zero)),
      ArithmeticFunction.cardFactors_apply_prime ha, ih2, add_comm]

theorem squarefree_prod_primes {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) :
    Squarefree (∏ p ∈ T, p) := (squarefree_prod_primes' hT).1

theorem moebius_prod_primes {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) :
    (ArithmeticFunction.moebius (∏ p ∈ T, p) : ℝ) = (-1) ^ T.card := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree (squarefree_prod_primes hT),
    (squarefree_prod_primes' hT).2]
  push_cast; rfl

/-- The `u`-rough indicator `1_{(v, P(u)) = 1}`: no prime factor `p < u`. -/
noncomputable def roughLow (u : ℝ) (v : ℕ) : ℝ :=
  if v.primeFactors.filter (fun p : ℕ => (p : ℝ) < u) = ∅ then 1 else 0

namespace ScalarParams

variable {S : ScalarParams}

theorem lamLowPlus_support {b : ℕ} (h : S.lamLowPlus b ≠ 0) :
    Squarefree b ∧ ∀ p ∈ b.primeFactors, (p : ℝ) < S.u0 := by
  unfold lamLowPlus at h
  split_ifs at h with hc
  · exact ⟨hc.1, hc.2.1⟩
  · exact absurd rfl h

theorem lamLowMinus_support {b : ℕ} (h : S.lamLowMinus b ≠ 0) :
    Squarefree b ∧ ∀ p ∈ b.primeFactors, (p : ℝ) < S.u0 := by
  unfold lamLowMinus at h
  split_ifs at h with hc
  · exact ⟨hc.1, hc.2.1⟩
  · exact absurd rfl h

theorem kappa_support {J b : ℕ} (h : S.kappa J b ≠ 0) :
    Squarefree b ∧ ∀ p ∈ b.primeFactors, (p : ℝ) < S.u0 := by
  unfold kappa at h
  split_ifs at h
  · exact lamLowPlus_support h
  · exact lamLowMinus_support h

theorem lamLowPlus_prod {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) (hu : ∀ p ∈ T, (p : ℝ) < S.u0)
    [Decidable (DplusSet S.Dlow T)] :
    S.lamLowPlus (∏ p ∈ T, p) = if DplusSet S.Dlow T then (-1) ^ T.card else 0 := by
  unfold lamLowPlus
  rw [Nat.primeFactors_prod hT, moebius_prod_primes hT]
  by_cases hD : DplusSet S.Dlow T
  · rw [if_pos ⟨squarefree_prod_primes hT, hu, hD⟩, if_pos hD]
  · rw [if_neg (fun h => hD h.2.2), if_neg hD]

theorem lamLowMinus_prod {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) (hu : ∀ p ∈ T, (p : ℝ) < S.u0)
    [Decidable (DminusSet S.Dlow T)] :
    S.lamLowMinus (∏ p ∈ T, p) = if DminusSet S.Dlow T then (-1) ^ T.card else 0 := by
  unfold lamLowMinus
  rw [Nat.primeFactors_prod hT, moebius_prod_primes hT]
  by_cases hD : DminusSet S.Dlow T
  · rw [if_pos ⟨squarefree_prod_primes hT, hu, hD⟩, if_pos hD]
  · rw [if_neg (fun h => hD h.2.2), if_neg hD]

theorem DplusSet_pre (D : ℝ) : ∀ s p, (∀ x ∈ s, p < x) → DplusSet D (insert p s) → DplusSet D s := by
  intro s p hp h q hq hev
  have := h q (Finset.mem_insert_of_mem hq)
  rw [above_insert_of_lt hp hq] at this
  exact this hev

theorem DplusSet_ext (D : ℝ) : ∀ s p, True → (∀ x ∈ s, p < x) → Odd s.card → DplusSet D s →
    DplusSet D (insert p s) := by
  intro s p _ hp hodd h q hq hev
  rcases Finset.mem_insert.1 hq with rfl | hq
  · rw [above_insert_self hp] at hev
    exact absurd hev (Nat.not_even_iff_odd.2 hodd)
  · rw [above_insert_of_lt hp hq] at hev ⊢
    exact h q hq hev

theorem DminusSet_pre (D : ℝ) :
    ∀ s p, (∀ x ∈ s, p < x) → DminusSet D (insert p s) → DminusSet D s := by
  intro s p hp h
  refine ⟨fun q hq hodd => ?_, fun q hq hemp => ?_⟩
  · have := h.1 q (Finset.mem_insert_of_mem hq)
    rw [above_insert_of_lt hp hq] at this
    exact this hodd
  · have := h.2 q (Finset.mem_insert_of_mem hq)
    rw [above_insert_of_lt hp hq] at this
    exact this hemp

theorem DminusSet_ext (D : ℝ) : ∀ (s : Finset ℕ) (p : ℕ), (p : ℝ) ^ 2 ≤ D → (∀ x ∈ s, p < x) → Even s.card →
    DminusSet D s → DminusSet D (insert p s) := by
  intro s p hpD hp hev h
  refine ⟨fun q hq hodd => ?_, fun q hq hemp => ?_⟩
  · rcases Finset.mem_insert.1 hq with rfl | hq
    · rw [above_insert_self hp] at hodd
      exact absurd hev (Nat.not_even_iff_odd.2 hodd)
    · rw [above_insert_of_lt hp hq] at hodd ⊢
      exact h.1 q hq hodd
  · rcases Finset.mem_insert.1 hq with rfl | hq
    · exact hpD
    · rw [above_insert_of_lt hp hq] at hemp
      exact h.2 q hq hemp

theorem DplusSet_empty (D : ℝ) : DplusSet D ∅ := fun p hp => absurd hp (Finset.notMem_empty p)

/-- **Upper low sieve**: `∑_{b ∣ v} λ⁺_low(b) ≥ 1_{(v, P(u)) = 1}`. -/
theorem lamLowPlus_sum_ge {v : ℕ} (hv : v ≠ 0) :
    roughLow S.u0 v ≤ ∑ b ∈ v.divisors, S.lamLowPlus b := by
  classical
  rw [sum_divisors_eq_sum_powerset hv (fun p : ℕ => (p : ℝ) < S.u0) S.lamLowPlus
    (fun d hd => lamLowPlus_support hd)]
  have hprime : ∀ T ∈ (v.primeFactors.filter (fun p : ℕ => (p : ℝ) < S.u0)).powerset,
      (∀ p ∈ T, p.Prime) ∧ ∀ p ∈ T, (p : ℝ) < S.u0 := by
    intro T hT
    have h := Finset.mem_powerset.1 hT
    exact ⟨fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 (h hp)).1,
      fun p hp => (Finset.mem_filter.1 (h hp)).2⟩
  rw [Finset.sum_congr rfl (fun T hT => lamLowPlus_prod (hprime T hT).1 (hprime T hT).2)]
  have key := rosser_upper (DplusSet S.Dlow) (fun _ => True) (DplusSet_empty _)
    (DplusSet_pre _) (DplusSet_ext _) (v.primeFactors.filter (fun p : ℕ => (p : ℝ) < S.u0))
    (fun _ _ => trivial)
  have := (Int.cast_le (R := ℝ)).2 key
  push_cast at this
  unfold roughLow
  convert this using 2

/-- **Lower low sieve**: `∑_{b ∣ v} λ⁻_low(b) ≤ 1_{(v, P(u)) = 1}`. -/
theorem lamLowMinus_sum_le (hS : S.Good) {v : ℕ} (hv : v ≠ 0) :
    ∑ b ∈ v.divisors, S.lamLowMinus b ≤ roughLow S.u0 v := by
  classical
  rw [sum_divisors_eq_sum_powerset hv (fun p : ℕ => (p : ℝ) < S.u0) S.lamLowMinus
    (fun d hd => lamLowMinus_support hd)]
  have hprime : ∀ T ∈ (v.primeFactors.filter (fun p : ℕ => (p : ℝ) < S.u0)).powerset,
      (∀ p ∈ T, p.Prime) ∧ ∀ p ∈ T, (p : ℝ) < S.u0 := by
    intro T hT
    have h := Finset.mem_powerset.1 hT
    exact ⟨fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 (h hp)).1,
      fun p hp => (Finset.mem_filter.1 (h hp)).2⟩
  rw [Finset.sum_congr rfl (fun T hT => lamLowMinus_prod (hprime T hT).1 (hprime T hT).2)]
  have hU : ∀ p ∈ v.primeFactors.filter (fun p : ℕ => (p : ℝ) < S.u0), (p : ℝ) ^ 2 ≤ S.Dlow := by
    intro p hp
    have h1 := (Finset.mem_filter.1 hp).2
    have h0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have := u0_sq_le_Dlow hS
    nlinarith
  have key := rosser_lower (DminusSet S.Dlow) (fun p : ℕ => (p : ℝ) ^ 2 ≤ S.Dlow)
    (DminusSet_pre _) (DminusSet_ext _) (v.primeFactors.filter (fun p : ℕ => (p : ℝ) < S.u0)) hU
  have := (Int.cast_le (R := ℝ)).2 key
  push_cast at this
  unfold roughLow
  convert this using 2

/-- **Level of `λ⁺_low`**: support in `b ≤ D_low`. -/
theorem lamLowPlus_level (hS : S.Good) {b : ℕ} (h : S.lamLowPlus b ≠ 0) : (b : ℝ) ≤ S.Dlow := by
  unfold lamLowPlus at h
  split_ifs at h with hc
  · obtain ⟨hsq, -, hD⟩ := hc
    rw [← Nat.prod_primeFactors_of_squarefree hsq]
    push_cast
    by_cases hne : b.primeFactors.Nonempty
    · obtain ⟨p, hp, hev, hle⟩ := exists_odd_position_witness (fun q : ℕ => (q : ℝ))
        b.primeFactors hne (fun x hx => by dsimp only; exact_mod_cast (Nat.prime_of_mem_primeFactors hx).one_lt.le)
        (fun x _ y _ hxy => by dsimp only; exact_mod_cast hxy)
      have h1 := hD p hp hev
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
      have h0 : 0 ≤ ∏ q ∈ above b.primeFactors p, (q : ℝ) := Finset.prod_nonneg (fun _ _ => by positivity)
      have : (∏ q ∈ above b.primeFactors p, (q : ℝ)) * (p : ℝ) ^ 2 ≤
          (∏ q ∈ above b.primeFactors p, (q : ℝ)) * (p : ℝ) ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ h0
        exact pow_le_pow_right₀ hp1 (by norm_num)
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.prod_empty]
      exact Dlow_ge_one hS
  · exact absurd rfl h

/-- **Level of `λ⁻_low`**: support in `b ≤ D_low`. -/
theorem lamLowMinus_level (hS : S.Good) {b : ℕ} (h : S.lamLowMinus b ≠ 0) :
    (b : ℝ) ≤ S.Dlow := by
  unfold lamLowMinus at h
  split_ifs at h with hc
  · obtain ⟨hsq, -, hD⟩ := hc
    rw [← Nat.prod_primeFactors_of_squarefree hsq]
    push_cast
    by_cases hne : b.primeFactors.Nonempty
    · obtain ⟨p, hp, hpos, hle⟩ := exists_even_position_witness (fun q : ℕ => (q : ℝ))
        b.primeFactors hne (fun x hx => by dsimp only; exact_mod_cast (Nat.prime_of_mem_primeFactors hx).one_lt.le)
        (fun x _ y _ hxy => by dsimp only; exact_mod_cast hxy)
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
      have h0 : 0 ≤ ∏ q ∈ above b.primeFactors p, (q : ℝ) :=
        Finset.prod_nonneg (fun _ _ => by positivity)
      rcases hpos with hodd | hemp
      · have h1 := hD.1 p hp hodd
        have : (∏ q ∈ above b.primeFactors p, (q : ℝ)) * (p : ℝ) ^ 2 ≤
            (∏ q ∈ above b.primeFactors p, (q : ℝ)) * (p : ℝ) ^ 3 := by
          apply mul_le_mul_of_nonneg_left _ h0
          exact pow_le_pow_right₀ hp1 (by norm_num)
        linarith
      · have h1 := hD.2 p hp hemp
        rw [hemp, Finset.prod_empty, one_mul] at hle
        linarith
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.prod_empty]
      exact Dlow_ge_one hS
  · exact absurd rfl h

theorem kappa_level (hS : S.Good) {J b : ℕ} (h : S.kappa J b ≠ 0) : (b : ℝ) ≤ S.Dlow := by
  unfold kappa at h
  split_ifs at h
  · exact lamLowPlus_level hS h
  · exact lamLowMinus_level hS h

end ScalarParams

end Erdos287.Physical.Sieve
