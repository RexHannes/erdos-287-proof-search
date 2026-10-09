import RequestProject.Erdos287.Direct.RawMask

/-!
# Route D — exact LCM / cofactor-carry algebra

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

This module formalises the exact arithmetic of the running denominators:

* `LN N = lcm(1, …, N)` and the exact prime-power divisibility criterion
  `p^e ∣ LN N ↔ p^e ≤ N` (`prime_pow_dvd_LN`);
* the jump `J_N = L_N / L_{N-1}`, proved to be `p` when `N = p^r` is a prime power and `1`
  otherwise (`LN_succ_eq`, `JN_prime_pow`, `JN_of_not_isPrimePow`, `JN_eq_div`);
* the exact layer quotients `T_q ↦ C_q` (valid exactly when `q ∣ T_q`) and the fibrewise
  aggregation `C_N = ∑_{⌊M/q⌋ = N} C_q`, proved as an exact partition identity
  (`carry_aggregate`);
* the descending exact recurrence `z_{N-1} = (z_N − C_N)/J_N` together with its exact
  divisibility side condition (`descending_recurrence`, `descending_step_iff`).

**No complexity claim is made.**  The recurrence is an exact identity; nothing here states
or implies that evaluating it is a polynomial-time algorithm.
-/

open scoped BigOperators

namespace Erdos287
namespace Direct

/-! ## D.13  `L_N = lcm(1, …, N)` -/

/-- `LN N = lcm(1, 2, …, N)`, with `LN 0 = 1`. -/
def LN : ℕ → ℕ
  | 0 => 1
  | (n + 1) => Nat.lcm (LN n) (n + 1)

@[simp] theorem LN_zero : LN 0 = 1 := rfl

theorem LN_succ (n : ℕ) : LN (n + 1) = Nat.lcm (LN n) (n + 1) := rfl

theorem LN_ne_zero : ∀ n : ℕ, LN n ≠ 0
  | 0 => by simp
  | (n + 1) => by
      rw [LN_succ]
      exact Nat.lcm_ne_zero (LN_ne_zero n) (Nat.succ_ne_zero n)

theorem LN_pos (n : ℕ) : 0 < LN n := Nat.pos_of_ne_zero (LN_ne_zero n)

theorem LN_dvd_succ (n : ℕ) : LN n ∣ LN (n + 1) := by
  rw [LN_succ]; exact Nat.dvd_lcm_left _ _

/-- Every positive `k ≤ N` divides `L_N`. -/
theorem dvd_LN {k N : ℕ} (hk : 0 < k) (h : k ≤ N) : k ∣ LN N := by
  induction N with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_ge k (n + 1) with hlt | hge
      · exact dvd_trans (ih (by omega)) (LN_dvd_succ n)
      · have hkn : k = n + 1 := by omega
        subst hkn
        rw [LN_succ]; exact Nat.dvd_lcm_right _ _

/-- **`prime_pow_dvd_LN`.**  `KERNEL-PROVED`.  For a prime `p` and `e ≥ 1`,
`p^e ∣ lcm(1,…,N)` holds exactly when `p^e ≤ N`. -/
theorem prime_pow_dvd_LN {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 1 ≤ e) :
    ∀ N : ℕ, (p ^ e ∣ LN N ↔ p ^ e ≤ N) := by
  intro N
  induction N with
  | zero =>
      simp only [LN_zero, Nat.le_zero]
      have hpe : 1 < p ^ e := Nat.one_lt_pow (by omega) hp.one_lt
      constructor
      · intro h
        have := Nat.le_of_dvd one_pos h
        omega
      · intro h; omega
  | succ n ih =>
      rw [LN_succ]
      constructor
      · intro h
        have hLN : LN n ≠ 0 := LN_ne_zero n
        have hn1 : (n + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero n
        have hlcm0 : Nat.lcm (LN n) (n + 1) ≠ 0 := Nat.lcm_ne_zero hLN hn1
        rw [Nat.Prime.pow_dvd_iff_le_factorization hp hlcm0,
          Nat.factorization_lcm hLN hn1] at h
        simp only [Finsupp.sup_apply, le_sup_iff] at h
        rcases h with h | h
        · rw [← Nat.Prime.pow_dvd_iff_le_factorization hp hLN] at h
          exact le_trans (ih.1 h) (by omega)
        · rw [← Nat.Prime.pow_dvd_iff_le_factorization hp hn1] at h
          exact Nat.le_of_dvd (by omega) h
      · intro h
        rcases Nat.lt_or_ge (p ^ e) (n + 1) with hlt | hge
        · exact dvd_trans (ih.2 (by omega)) (Nat.dvd_lcm_left _ _)
        · have hpe : p ^ e = n + 1 := by omega
          rw [hpe]
          exact Nat.dvd_lcm_right _ _

/-! ## D.14  The jump `J_N = L_N / L_{N-1}` -/

open Classical in
/-- The jump factor `J_N`: the prime `p` if `N = p^r` is a prime power, and `1` otherwise. -/
noncomputable def JN (N : ℕ) : ℕ := if IsPrimePow N then N.minFac else 1

theorem JN_of_not_isPrimePow {N : ℕ} (h : ¬ IsPrimePow N) : JN N = 1 := by
  rw [JN, if_neg h]

/-- **`JN_prime_pow`.**  `KERNEL-PROVED`.  `J_{p^k} = p` for a prime `p` and `k ≥ 1`. -/
theorem JN_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) : JN (p ^ k) = p := by
  have hpp : IsPrimePow (p ^ k) := (isPrimePow_nat_iff _).2 ⟨p, k, hp, by omega, rfl⟩
  rw [JN, if_pos hpp, hp.pow_minFac (by omega)]

/-- **`LN_succ_eq`.**  `KERNEL-PROVED`.  The exact one-step growth of `lcm(1,…,N)`:
`L_N = J_N · L_{N-1}`. -/
theorem LN_succ_eq (n : ℕ) (hn : 1 ≤ n) : LN (n + 1) = JN (n + 1) * LN n := by
  by_cases hpp : IsPrimePow (n + 1)
  · obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff (n + 1)).1 hpp
    have hJ : JN (n + 1) = p := by rw [← hpk, JN_prime_pow hp (by omega)]
    -- `p^(k-1) ∣ L_n`, because `p^(k-1) ≤ n`
    have hlt : p ^ (k - 1) < p ^ k := Nat.pow_lt_pow_right hp.one_lt (by omega)
    have hle : p ^ (k - 1) ≤ n := by omega
    have hdvd1 : p ^ (k - 1) ∣ LN n := by
      rcases Nat.eq_zero_or_pos (k - 1) with h0 | h0
      · rw [h0]; simp
      · exact (prime_pow_dvd_LN hp h0 n).2 hle
    -- the gcd is exactly `p^(k-1)`
    have hgcd : Nat.gcd (LN n) (p ^ k) = p ^ (k - 1) := by
      obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow hp).1 (Nat.gcd_dvd_right (LN n) (p ^ k))
      have hjdvd : p ^ j ∣ LN n := hj ▸ Nat.gcd_dvd_left (LN n) (p ^ k)
      have hjle : j ≤ k - 1 := by
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · omega
        · have hjn : p ^ j ≤ n := (prime_pow_dvd_LN hp hj0 n).1 hjdvd
          by_contra hcon
          have : p ^ k ≤ p ^ j := Nat.pow_le_pow_right hp.one_le (by omega)
          omega
      have hge : p ^ (k - 1) ∣ p ^ j := hj ▸ Nat.dvd_gcd hdvd1 (pow_dvd_pow p (by omega))
      have : k - 1 ≤ j := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hge
      rw [hj]
      congr 1
      omega
    have hmul := Nat.gcd_mul_lcm (LN n) (p ^ k)
    rw [hgcd] at hmul
    have hsplit : p ^ k = p ^ (k - 1) * p := by
      rw [← pow_succ]
      congr 1
      omega
    have hcancel : p ^ (k - 1) * Nat.lcm (LN n) (p ^ k) = p ^ (k - 1) * (p * LN n) := by
      rw [hmul, hsplit]; ring
    have hppos : 0 < p ^ (k - 1) := Nat.pow_pos hp.pos
    have hlcm : Nat.lcm (LN n) (p ^ k) = p * LN n :=
      Nat.eq_of_mul_eq_mul_left hppos hcancel
    rw [LN_succ, hJ, ← hpk, hlcm]
  · -- not a prime power: `n+1` divides `L_n`, so the LCM does not grow
    have hN2 : 2 ≤ n + 1 := by omega
    have hN0 : (n + 1 : ℕ) ≠ 0 := by omega
    have hN1 : (n + 1 : ℕ) ≠ 1 := by omega
    set p := (n + 1).minFac with hpdef
    have hp : p.Prime := Nat.minFac_prime hN1
    have hpdvd : p ∣ n + 1 := Nat.minFac_dvd _
    set k := (n + 1).factorization p with hkdef
    have hk : 0 < k := hp.factorization_pos_of_dvd hN0 hpdvd
    set b := (n + 1) / p ^ k with hbdef
    have hab : p ^ k * b = n + 1 := Nat.ordProj_mul_ordCompl_eq_self (n + 1) p
    have hcop : Nat.Coprime (p ^ k) b := (Nat.coprime_ordCompl hp hN0).pow_left k
    have hb1 : b ≠ 1 := by
      intro hb
      rw [hb, mul_one] at hab
      exact hpp ((isPrimePow_nat_iff _).2 ⟨p, k, hp, hk, hab⟩)
    have hb0 : b ≠ 0 := by
      intro hb; rw [hb, mul_zero] at hab; omega
    have hb2 : 2 ≤ b := (Nat.two_le_iff b).2 ⟨hb0, hb1⟩
    have ha2 : 2 ≤ p ^ k := by
      calc 2 ≤ p := hp.two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ k := Nat.pow_le_pow_right hp.one_le hk
    have hale : p ^ k ≤ n := by
      have h2 : p ^ k * 2 ≤ p ^ k * b := Nat.mul_le_mul_left _ hb2
      omega
    have hble : b ≤ n := by
      have h2 : 2 * b ≤ p ^ k * b := Nat.mul_le_mul_right _ ha2
      omega
    have hdvdN : (n + 1) ∣ LN n := by
      rw [← hab]
      exact hcop.mul_dvd_of_dvd_of_dvd (dvd_LN (by omega) hale) (dvd_LN (by omega) hble)
    rw [LN_succ, JN_of_not_isPrimePow hpp, one_mul]
    exact Nat.dvd_antisymm (Nat.lcm_dvd dvd_rfl hdvdN) (Nat.dvd_lcm_left _ _)

/-- **`JN_eq_div`.**  `KERNEL-PROVED`.  `J_N` really is the quotient `L_N / L_{N-1}`. -/
theorem JN_eq_div (n : ℕ) (hn : 1 ≤ n) : JN (n + 1) = LN (n + 1) / LN n := by
  rw [LN_succ_eq n hn, Nat.mul_div_assoc _ dvd_rfl, Nat.div_self (LN_pos n), mul_one]

/-! ## D.15  Exact layer quotients and their fibrewise aggregation -/

/-- The exact layer carry `C_q = T_q / q`, meaningful exactly when `q ∣ T_q`. -/
def layerCarry (T q : ℤ) : ℤ := T / q

/-- **`layerCarry_exact`.**  `KERNEL-PROVED`.  When `q ∣ T_q` the layer carry reproduces
`T_q` exactly. -/
theorem layerCarry_exact {T q : ℤ} (h : q ∣ T) : q * layerCarry T q = T := by
  rw [layerCarry, Int.mul_ediv_cancel' h]

/-- **`layerCarry_not_exact_without_dvd`.**  `KERNEL-PROVED` firewall.  Without the
divisibility hypothesis the layer quotient is *not* exact: `q = 2`, `T = 1`. -/
theorem layerCarry_not_exact_without_dvd : (2 : ℤ) * layerCarry 1 2 ≠ 1 := by decide

/-- The aggregated carry of the layer `⌊M/q⌋ = N`. -/
def aggregateCarry (M : ℕ) (Q : Finset ℕ) (Cq : ℕ → ℤ) (N : ℕ) : ℤ :=
  ∑ q ∈ Q.filter (fun q => M / q = N), Cq q

/-- **`carry_aggregate`.**  `KERNEL-PROVED`.  The exact aggregate identity: summing the layer
carries over the fibres `⌊M/q⌋ = N` recovers the total carry. -/
theorem carry_aggregate (M : ℕ) (Q : Finset ℕ) (Cq : ℕ → ℤ) (Ns : Finset ℕ)
    (hmaps : ∀ q ∈ Q, M / q ∈ Ns) :
    ∑ N ∈ Ns, aggregateCarry M Q Cq N = ∑ q ∈ Q, Cq q :=
  Finset.sum_fiberwise_of_maps_to hmaps Cq

/-! ## D.16  The descending exact recurrence -/

/-- **`descending_recurrence`.**  `KERNEL-PROVED`.  If `z_N = J_N · z_{N-1} + C_N` with
`J_N ≠ 0`, then `J_N ∣ z_N − C_N` and `z_{N-1} = (z_N − C_N)/J_N`. -/
theorem descending_recurrence {z zprev C J : ℤ} (hJ : J ≠ 0) (h : z = J * zprev + C) :
    J ∣ (z - C) ∧ (z - C) / J = zprev := by
  have hz : z - C = J * zprev := by rw [h]; ring
  refine ⟨⟨zprev, hz⟩, ?_⟩
  rw [hz, Int.mul_ediv_cancel_left _ hJ]

/-- **`descending_step_iff`.**  `KERNEL-PROVED`.  The exact solvability criterion of one
descending step. -/
theorem descending_step_iff {z C J : ℤ} (hJ : J ≠ 0) :
    (∃ zprev : ℤ, z = J * zprev + C) ↔ J ∣ (z - C) := by
  constructor
  · rintro ⟨zprev, h⟩; exact (descending_recurrence hJ h).1
  · rintro ⟨t, ht⟩; exact ⟨t, by omega⟩

end Direct
end Erdos287
