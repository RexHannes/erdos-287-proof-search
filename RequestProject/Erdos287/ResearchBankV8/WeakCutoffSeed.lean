import RequestProject.Erdos287.ResearchBankV8.Saturation

/-!
# Erdős #287 — Research Bank V8 §2D: the weak-cutoff explicit seed family

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

For `k ≥ 1` put

  `P = 2^(6k)`,  `M = P + 2`,  `T = M/2`,  `A = M/3`,

and on `[A, M]` let `x_n = 1` iff `n ∣ L_T = lcm(1,…,T)` (this is the canonical saturation of
the all-zero word, `Saturation.saturate`).  Kernel-proved here:

* `seed_three_dvd_M`, `seed_two_dvd_M`, `seed_T_eq` — integrality: `3 ∣ M`, `T = 2^(6k−1)+1`;
* `seed_endpoints_selected` — `A ∣ L_T` and `M ∣ L_T`;
* `nondvd_lcmUpTo_isPrimePow` — **classification**: if `1 ≤ n ≤ 2T` and `n ∤ L_T`, then `n` is a
  prime power with `n > T`;
* `seed_P_not_dvd`, `seed_even_zero_eq_P` — the unique even problematic power is `P`;
* `seed_P_sub_one_not_primePow` — `P − 1 = (2^(3k)−1)(2^(3k)+1)` with coprime factors;
* `seed_P_add_one_not_primePow` — `P + 1 = (b+1)(b²−b+1)`, `b = 2^(2k)`, with coprime factors;
* `seed_noAdjZero` — no adjacent zeros on `[A, M]`;
* `seed_denomEntry` — denominator-entry into `L_T`.

Banked as `WEAK_CUTOFF_ENTRY_EXISTENCE` (**weak cutoff `T = M/2` only**).  The PNT-type
statements `|Z| = o(M)` and `S → log 3` are the uninhabited interfaces `SeedZeroSetSublinear`,
`SeedMassTendsToLogThree`.  **Firewall** (`weak_cutoff_does_not_transfer`): the construction at
`T = M/2` does not transfer to `T = M/(2H)`: at `M = 66`, `H = 2` the zeros `31, 32` are adjacent.
-/

open scoped BigOperators

namespace Erdos287
namespace ResearchBankV8
namespace WeakCutoffSeed

open Saturation

/-! ## 1.  `lcm(1,…,T)` -/

/-- `L_T = lcm(1, …, T)`. -/
def lcmUpTo (T : ℕ) : ℕ := (Finset.Icc 1 T).lcm id

theorem dvd_lcmUpTo {n T : ℕ} (h1 : 1 ≤ n) (hT : n ≤ T) : n ∣ lcmUpTo T :=
  Finset.dvd_lcm (s := Finset.Icc 1 T) (f := id) (Finset.mem_Icc.2 ⟨h1, hT⟩)

theorem lcmUpTo_ne_zero (T : ℕ) : lcmUpTo T ≠ 0 := by
  unfold lcmUpTo
  rw [Ne, Finset.lcm_eq_zero_iff]
  simp

/-- A prime power dividing an lcm of nonzero numbers divides one of them. -/
theorem prime_pow_dvd_finset_lcm {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    ∀ S : Finset ℕ, (∀ s ∈ S, s ≠ 0) → p ^ a ∣ S.lcm id → ∃ s ∈ S, p ^ a ∣ s := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ h
    simp only [Finset.lcm_empty] at h
    have := Nat.le_of_dvd one_pos h
    have := Nat.one_lt_pow (by omega : a ≠ 0) hp.one_lt
    omega
  | insert s S hs ih =>
    intro hS h
    rw [Finset.lcm_insert] at h
    have hs0 : s ≠ 0 := hS s (Finset.mem_insert_self _ _)
    have hS0 : S.lcm id ≠ 0 := by
      rw [Ne, Finset.lcm_eq_zero_iff]
      intro ⟨x, hx, hx0⟩
      exact hS x (Finset.mem_insert_of_mem hx) hx0
    change p ^ a ∣ Nat.lcm s (S.lcm id) at h
    rw [hp.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero hs0 hS0),
      Nat.factorization_lcm hs0 hS0, Finsupp.sup_apply] at h
    rcases le_max_iff.1 h with h' | h'
    · exact ⟨s, Finset.mem_insert_self _ _, (hp.pow_dvd_iff_le_factorization hs0).2 h'⟩
    · obtain ⟨t, ht, htd⟩ := ih (fun x hx => hS x (Finset.mem_insert_of_mem hx))
        ((hp.pow_dvd_iff_le_factorization hS0).2 h')
      exact ⟨t, Finset.mem_insert_of_mem ht, htd⟩

/-- A prime power dividing `L_T` is at most `T`. -/
theorem prime_pow_le_of_dvd_lcmUpTo {p a T : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (h : p ^ a ∣ lcmUpTo T) : p ^ a ≤ T := by
  obtain ⟨s, hs, hsd⟩ := prime_pow_dvd_finset_lcm hp ha (Finset.Icc 1 T)
    (fun s hs => by simp at hs; omega) h
  simp only [Finset.mem_Icc] at hs
  exact (Nat.le_of_dvd (by omega) hsd).trans hs.2

/-- **Classification.**  If `1 ≤ n ≤ 2T` and `n ∤ L_T`, then `n > T` and `n` is a prime power. -/
theorem nondvd_lcmUpTo_isPrimePow {n T : ℕ} (hn : 1 ≤ n) (hn2 : n ≤ 2 * T)
    (hnd : ¬ n ∣ lcmUpTo T) : T < n ∧ IsPrimePow n := by
  have hTn : T < n := by
    by_contra h; exact hnd (dvd_lcmUpTo hn (by omega))
  refine ⟨hTn, ?_⟩
  have hn2' : 2 ≤ n := by omega
  set p := n.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpn : p ∣ n := Nat.minFac_dvd n
  set u := p ^ n.factorization p with hu
  set w := n / p ^ n.factorization p with hw
  have huw : u * w = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hcop : Nat.Coprime u w :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp (by omega))
  clear_value u w
  have hfac : 1 ≤ n.factorization p :=
    (hp.dvd_iff_one_le_factorization (by omega)).1 hpn
  have hu2 : 2 ≤ u := by
    have := Nat.one_lt_pow (by omega : n.factorization p ≠ 0) hp.one_lt
    omega
  by_cases hw1 : w = 1
  · refine ⟨p, n.factorization p, hp.prime, by omega, ?_⟩
    rw [hw1, mul_one, hu] at huw; exact huw
  · exfalso
    have hw0 : w ≠ 0 := by rintro h; simp [h] at huw; omega
    have hw2 : 2 ≤ w := by omega
    have huT : u ≤ T := by nlinarith
    have hwT : w ≤ T := by nlinarith
    exact hnd (huw ▸ hcop.mul_dvd_of_dvd_of_dvd (dvd_lcmUpTo (by omega) huT)
      (dvd_lcmUpTo (by omega) hwT))

/-! ## 2.  Two coprime factors exclude prime powers -/

/-- A product of two coprime factors, each `≥ 2`, is not a prime power. -/
theorem not_isPrimePow_of_coprime_mul {x y : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hc : Nat.Coprime x y) : ¬ IsPrimePow (x * y) := by
  rintro ⟨p, m, hp, hm, hpm⟩
  rw [← Nat.prime_iff] at hp
  have hxd : x ∣ p ^ m := hpm ▸ dvd_mul_right x y
  have hyd : y ∣ p ^ m := hpm ▸ dvd_mul_left y x
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hxd
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hyd
  have hi : i ≠ 0 := by rintro rfl; simp at hx
  have hj : j ≠ 0 := by rintro rfl; simp at hy
  have h1 : p ∣ Nat.gcd (p ^ i) (p ^ j) :=
    Nat.dvd_gcd (dvd_pow_self p hi) (dvd_pow_self p hj)
  rw [hc] at h1
  exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one h1) |>.elim

/-! ## 3.  The seed family -/

variable (k : ℕ)

/-- `P = 2^(6k)`. -/
def P : ℕ := 2 ^ (6 * k)
/-- `M = P + 2`. -/
def M : ℕ := P k + 2
/-- `T = M / 2`. -/
def T : ℕ := M k / 2
/-- `A = M / 3`. -/
def A : ℕ := M k / 3

/-- The seed word: `x_n = 1` iff `n ∣ L_T` — the canonical saturation of the all-zero word. -/
def seed : ℕ → Bool := saturate (lcmUpTo (T k)) (fun _ => false)

theorem seed_eq_true_iff (n : ℕ) : seed k n = true ↔ n ∣ lcmUpTo (T k) := by
  unfold seed saturate; split_ifs with h <;> simp [h]

theorem P_eq (hk : 1 ≤ k) : P k = 2 * 2 ^ (6 * k - 1) := by
  unfold P
  rw [← pow_succ']
  congr 1; omega

theorem seed_two_dvd_M (hk : 1 ≤ k) : 2 ∣ M k := by
  unfold M P
  rw [show 6 * k = (6 * k - 1) + 1 by omega, pow_succ]; omega

/-- **`A` is an integer**: `3 ∣ M`. -/
theorem seed_three_dvd_M : 3 ∣ M k := by
  unfold M P
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, pow_mul, Nat.pow_mod]
  norm_num

/-- `T = 2^(6k−1) + 1`. -/
theorem seed_T_eq (hk : 1 ≤ k) : T k = 2 ^ (6 * k - 1) + 1 := by
  unfold T M; rw [P_eq k hk]; omega

theorem seed_M_eq_two_T (hk : 1 ≤ k) : M k = 2 * T k := by
  unfold M; rw [seed_T_eq k hk, P_eq k hk]; ring

theorem seed_T_odd (hk : 1 ≤ k) : ¬ 2 ∣ T k := by
  rw [seed_T_eq k hk, show 6 * k - 1 = (6 * k - 2) + 1 by omega, pow_succ]; omega

theorem seed_A_pos : 1 ≤ A k := by
  unfold A M; have : 1 ≤ P k := Nat.one_le_two_pow; omega

theorem seed_A_le_T : A k ≤ T k := by
  unfold A T; omega

theorem seed_T_ge_two (hk : 1 ≤ k) : 2 ≤ T k := by
  rw [seed_T_eq k hk]
  have : 2 ^ 1 ≤ 2 ^ (6 * k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- **Endpoint selection**: `A ∣ L_T` and `M ∣ L_T`. -/
theorem seed_endpoints_selected (hk : 1 ≤ k) : seed k (A k) = true ∧ seed k (M k) = true := by
  rw [seed_eq_true_iff, seed_eq_true_iff]
  refine ⟨dvd_lcmUpTo (seed_A_pos k) (seed_A_le_T k), ?_⟩
  rw [seed_M_eq_two_T k hk]
  have hc : Nat.Coprime 2 (T k) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (seed_T_odd k hk)
  exact hc.mul_dvd_of_dvd_of_dvd (dvd_lcmUpTo (by norm_num) (seed_T_ge_two k hk))
    (dvd_lcmUpTo (by have := seed_T_ge_two k hk; omega) le_rfl)

/-- `P ∤ L_T`: the power `P` is a genuine zero. -/
theorem seed_P_not_dvd (hk : 1 ≤ k) : ¬ P k ∣ lcmUpTo (T k) := by
  intro h
  have := prime_pow_le_of_dvd_lcmUpTo Nat.prime_two (by omega : 1 ≤ 6 * k) h
  rw [seed_T_eq k hk] at this
  have h2 := P_eq k hk
  unfold P at h2
  have : 2 ^ 1 ≤ 2 ^ (6 * k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem seed_P_mem : A k ≤ P k ∧ P k ≤ M k := by
  unfold A M; omega

/-- **The unique even problematic power is `P`.** -/
theorem seed_even_zero_eq_P (hk : 1 ≤ k) {n : ℕ} (hA : A k ≤ n) (hM : n ≤ M k)
    (hnd : ¬ n ∣ lcmUpTo (T k)) (h2 : 2 ∣ n) : n = P k := by
  have h1 : 1 ≤ n := (seed_A_pos k).trans hA
  obtain ⟨hTn, p, a, hp, ha, rfl⟩ :=
    nondvd_lcmUpTo_isPrimePow h1 (seed_M_eq_two_T k hk ▸ hM) hnd
  rw [← Nat.prime_iff] at hp
  have hp2 : p = 2 :=
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  subst hp2
  rw [seed_T_eq k hk] at hTn
  have hM' : 2 ^ a ≤ 2 ^ (6 * k) + 2 := by unfold M P at hM; exact hM
  have hlo : 6 * k - 1 < a := by
    by_contra h
    have : 2 ^ a ≤ 2 ^ (6 * k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hhi : a ≤ 6 * k := by
    by_contra h
    have : 2 ^ (6 * k + 1) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ] at this
    have : 4 ≤ 2 ^ (6 * k) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (6 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  unfold P; congr 1; omega

/-- `P − 1 = (2^(3k)−1)(2^(3k)+1)`. -/
theorem seed_P_sub_one_factor : P k - 1 = (2 ^ (3 * k) - 1) * (2 ^ (3 * k) + 1) := by
  unfold P
  rw [show 6 * k = 3 * k * 2 by ring, pow_mul]
  obtain ⟨c, hc⟩ : ∃ c, 2 ^ (3 * k) = c + 1 := ⟨2 ^ (3 * k) - 1, by
    have := Nat.one_le_two_pow (n := 3 * k); omega⟩
  rw [hc]
  simp only [Nat.add_sub_cancel]
  ring_nf
  omega

/-- **`P − 1` is not a prime power.** -/
theorem seed_P_sub_one_not_primePow (hk : 1 ≤ k) : ¬ IsPrimePow (P k - 1) := by
  rw [seed_P_sub_one_factor]
  have h8 : 8 ≤ 2 ^ (3 * k) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (3 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have heven : 2 ∣ 2 ^ (3 * k) := dvd_pow_self 2 (by omega)
  apply not_isPrimePow_of_coprime_mul (by omega) (by omega)
  have : 2 ^ (3 * k) + 1 = 2 + (2 ^ (3 * k) - 1) := by omega
  rw [this, Nat.coprime_add_self_right]
  exact (Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega))

/-- `P + 1 = (b+1)(b²−b+1)` with `b = 2^(2k)`, written as `(b+1)((b+1)(b−2)+3)`. -/
theorem seed_P_add_one_factor (hk : 1 ≤ k) :
    P k + 1 = (2 ^ (2 * k) + 1) * ((2 ^ (2 * k) + 1) * (2 ^ (2 * k) - 2) + 3) := by
  unfold P
  rw [show 6 * k = 2 * k * 3 by ring, pow_mul]
  obtain ⟨c, hc⟩ : ∃ c, 2 ^ (2 * k) = c + 2 := ⟨2 ^ (2 * k) - 2, by
    have : 2 ^ 1 ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega⟩
  rw [hc]
  simp only [Nat.add_sub_cancel]
  ring

/-- **`P + 1` is not a prime power.** -/
theorem seed_P_add_one_not_primePow (hk : 1 ≤ k) : ¬ IsPrimePow (P k + 1) := by
  rw [seed_P_add_one_factor k hk]
  set b := 2 ^ (2 * k) with hb
  have hb4 : 4 ≤ b := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb3 : b % 3 = 1 := by
    rw [hb, pow_mul, Nat.pow_mod]; norm_num
  apply not_isPrimePow_of_coprime_mul (by omega) (by nlinarith)
  apply Nat.coprime_of_dvd
  intro q hq hq1 hq2
  have h3 : q ∣ 3 := (Nat.dvd_add_right (dvd_mul_of_dvd_left hq1 _)).1 hq2
  have hq3 : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h3
  subst hq3
  omega

/-- **No adjacent zeros on `[A, M]`.** -/
theorem seed_noAdjZero (hk : 1 ≤ k) : NoAdjZero (Finset.Icc (A k) (M k)) (seed k) := by
  intro n hn hn1
  simp only [Finset.mem_Icc] at hn hn1
  by_contra hcon
  push_neg at hcon
  simp only [ne_eq, Bool.not_eq_true, ] at hcon
  have z0 : ¬ n ∣ lcmUpTo (T k) := by rw [← seed_eq_true_iff]; simp [hcon.1]
  have z1 : ¬ (n + 1) ∣ lcmUpTo (T k) := by rw [← seed_eq_true_iff]; simp [hcon.2]
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hnP := seed_even_zero_eq_P k hk hn.1 hn.2 z0 ⟨m, by omega⟩
    have h1 : 1 ≤ n + 1 := by omega
    have := (nondvd_lcmUpTo_isPrimePow h1 (seed_M_eq_two_T k hk ▸ hn1.2) z1).2
    rw [hnP] at this
    exact seed_P_add_one_not_primePow k hk this
  · have hnP := seed_even_zero_eq_P k hk (by omega) hn1.2 z1 ⟨m + 1, by omega⟩
    have h1 : 1 ≤ n := (seed_A_pos k).trans hn.1
    have := (nondvd_lcmUpTo_isPrimePow h1 (seed_M_eq_two_T k hk ▸ hn.2) z0).2
    rw [show n = P k - 1 by omega] at this
    exact seed_P_sub_one_not_primePow k hk this

/-- **Denominator-entry into `L_T`.** -/
theorem seed_denomEntry : DenomEntry (Finset.Icc (A k) (M k)) (seed k) (lcmUpTo (T k)) :=
  integral_of_dvd_sum _ _ fun n hn => by
    simp only [selected, Finset.mem_filter] at hn
    exact (seed_eq_true_iff k n).1 hn.2

/-- **`WEAK_CUTOFF_ENTRY_EXISTENCE`** — the complete elementary package at the weak cutoff
`T = M/2`, for every `k ≥ 1`. -/
theorem weak_cutoff_entry_existence (hk : 1 ≤ k) :
    3 ∣ M k ∧ T k = 2 ^ (6 * k - 1) + 1 ∧ M k = 2 * T k ∧
    seed k (A k) = true ∧ seed k (M k) = true ∧
    NoAdjZero (Finset.Icc (A k) (M k)) (seed k) ∧
    DenomEntry (Finset.Icc (A k) (M k)) (seed k) (lcmUpTo (T k)) :=
  ⟨seed_three_dvd_M k, seed_T_eq k hk, seed_M_eq_two_T k hk,
   (seed_endpoints_selected k hk).1, (seed_endpoints_selected k hk).2, seed_noAdjZero k hk,
   seed_denomEntry k⟩

/-! ## 4.  External asymptotic interfaces (uninhabited) -/

/-- **External interface — NOT proved.**  The zero set of the seed on `[A, M]` has size `o(M)`
(a PNT-type prime-power count). -/
def SeedZeroSetSublinear : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀,
    ((forbidden (Finset.Icc (A k) (M k)) (seed k)).card : ℝ) ≤ ε * (M k : ℝ)

/-- **External interface — NOT proved.**  The selected reciprocal mass tends to `log 3`. -/
def SeedMassTendsToLogThree : Prop :=
  Filter.Tendsto (fun k => ((∑ n ∈ selected (Finset.Icc (A k) (M k)) (seed k), (1 : ℚ) / n : ℚ)
    : ℝ)) Filter.atTop (nhds (Real.log 3))

/-! ## 5.  Firewall: `T = M/2` does not transfer to `T = M/(2H)` -/

/-- At `M = 66` (the `k = 1` member) with `H = 2`, i.e. cutoff `T' = 66/4 = 16`, the saturated
word has the **adjacent zeros** `31, 32` in `[A, M] = [22, 66]`.  So the weak-cutoff
construction does not imply the corresponding statement at `T = M/(2H)`. -/
theorem weak_cutoff_does_not_transfer :
    M 1 = 66 ∧ A 1 = 22 ∧ T 1 = 33 ∧ M 1 / (2 * 2) = 16 ∧
    ¬ 31 ∣ lcmUpTo 16 ∧ ¬ 32 ∣ lcmUpTo 16 ∧
    ¬ NoAdjZero (Finset.Icc 22 66) (saturate (lcmUpTo 16) (fun _ => false)) := by
  have h31 : ¬ 31 ∣ lcmUpTo 16 := fun h => by
    have := prime_pow_le_of_dvd_lcmUpTo (p := 31) (a := 1) (by norm_num) le_rfl (by simpa using h)
    omega
  have h32 : ¬ 32 ∣ lcmUpTo 16 := fun h => by
    have := prime_pow_le_of_dvd_lcmUpTo (p := 2) (a := 5) Nat.prime_two (by norm_num)
      (by simpa using h)
    omega
  refine ⟨by decide, by decide, by decide, by decide, h31, h32, ?_⟩
  intro hno
  rcases hno 31 (by simp) (by simp) with h | h <;> simp [saturate, h31, h32] at h

end WeakCutoffSeed
end ResearchBankV8
end Erdos287
