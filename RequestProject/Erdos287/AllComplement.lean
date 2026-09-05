import Mathlib
import RequestProject.Erdos287.BsrcWeights

/-!
# Erdős #287 effectivity — the all-complement discrete identity (§3)

```
SQUAREFREE-SUPPORTED DIVISOR SUM : KERNEL-PROVED
ALL-COMPLEMENT DISCRETE          : KERNEL-PROVED
```

For every `d ≠ 0` and `n ≠ 0`,

    B(d) · ∑_{k ∣ n, (k,d) = 1} β(k)  =  B(d·n).

The proof is by **finite prime-factor products** only: the divisor sum is
squarefree-supported, hence equals `∏_{p ∣ n} (1 + β_d(p))`, and at an odd prime
`p ∤ d` this local factor is exactly `(p−1)/(p−2)`.  No infinite Euler product is
used anywhere.

The oddness of `d` is not needed (the prime `2` never contributes: `β` is supported
on odd arguments and `B0` skips `p = 2`); the requested odd-`d` form is recorded as
`allComplement_discrete_odd`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §3.1  Products of distinct primes -/

/-- A product of distinct primes is squarefree. -/
theorem squarefree_prod_primes {t : Finset ℕ} (h : ∀ p ∈ t, p.Prime) :
    Squarefree (∏ p ∈ t, p) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hp : a.Prime := h a (Finset.mem_insert_self a s)
      have hs : ∀ p ∈ s, p.Prime := fun p hp' => h p (Finset.mem_insert_of_mem hp')
      have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
        rw [Nat.Prime.coprime_iff_not_dvd hp]
        intro hdvd
        obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime hp).exists_mem_finset_dvd hdvd
        have hqa : q = a := ((hs q hq).dvd_iff_eq hp.ne_one).1 hpq
        exact ha (hqa ▸ hq)
      rw [Finset.prod_insert ha]
      exact (Nat.squarefree_mul hcop).2 ⟨hp.squarefree, ih hs⟩

/-! ## §3.2  Squarefree-supported divisor sums are finite prime products -/

/-- **Squarefree-supported divisor sum.**  If `g` vanishes off the squarefree numbers and
is multiplicative on products of distinct primes, then `∑_{k ∣ n} g k = ∏_{p ∣ n}(1 + g p)`.
This is the only combinatorial input of the all-complement identity. -/
theorem sum_divisors_of_squarefreeSupported {n : ℕ} (hn : n ≠ 0) (g : ℕ → ℚ)
    (hg0 : ∀ k, ¬ Squarefree k → g k = 0)
    (hgprod : ∀ t : Finset ℕ, (∀ p ∈ t, p.Prime) → g (∏ p ∈ t, p) = ∏ p ∈ t, g p) :
    ∑ k ∈ n.divisors, g k = ∏ p ∈ n.primeFactors, (1 + g p) := by
  classical
  have hfilter : ∑ k ∈ n.divisors, g k = ∑ k ∈ n.divisors with Squarefree k, g k := by
    refine (Finset.sum_filter_of_ne ?_).symm
    intro k _ hk
    by_contra hsq
    exact hk (hg0 k hsq)
  rw [hfilter, Nat.sum_divisors_filter_squarefree hn, Nat.factors_eq,
    show ((n.primeFactorsList : Multiset ℕ)).toFinset = n.primeFactors from Nat.toFinset_factors n]
  have : ∀ t ∈ n.primeFactors.powerset, g (t.val.prod) = ∏ p ∈ t, g p := by
    intro t ht
    rw [Finset.prod_val]
    exact hgprod t fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_powerset.1 ht hp)
  rw [Finset.sum_congr rfl this]
  rw [show (∏ p ∈ n.primeFactors, (1 + g p)) = ∏ p ∈ n.primeFactors, (g p + 1) from
    Finset.prod_congr rfl (fun p _ => add_comm _ _)]
  simpa using (Finset.prod_add g (fun _ => (1 : ℚ)) n.primeFactors).symm

/-! ## §3.3  The coprime-restricted local weight -/

/-- `β` restricted to arguments coprime to `d`. -/
def betaCop (d k : ℕ) : ℚ := if Nat.Coprime k d then beta k else 0

lemma betaCop_eq_zero_of_not_squarefree {d k : ℕ} (h : ¬ Squarefree k) : betaCop d k = 0 := by
  unfold betaCop; split <;> simp [beta_eq_zero_of_not_squarefree h]

/-- `β_d` at a prime: it is `1/(p−2)` for odd `p ∤ d`, and `0` otherwise. -/
lemma betaCop_prime {d p : ℕ} (hp : p.Prime) :
    betaCop d p = if p ≠ 2 ∧ ¬ p ∣ d then 1 / ((p : ℚ) - 2) else 0 := by
  unfold betaCop
  by_cases hdvd : p ∣ d
  · have : ¬ Nat.Coprime p d := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]; exact not_not_intro hdvd
    simp [this, hdvd]
  · have hcop : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hp).2 hdvd
    by_cases h2 : p = 2
    · subst h2
      simp [beta_eq_zero_of_even dvd_rfl]
    · simp [hcop, h2, hdvd, beta_prime hp h2]

/-- `β_d` is multiplicative on products of distinct primes. -/
lemma betaCop_prod_primes (d : ℕ) {t : Finset ℕ} (h : ∀ p ∈ t, p.Prime) :
    betaCop d (∏ p ∈ t, p) = ∏ p ∈ t, betaCop d p := by
  classical
  by_cases hgood : ∀ p ∈ t, p ≠ 2 ∧ ¬ p ∣ d
  · have hsq : Squarefree (∏ p ∈ t, p) := squarefree_prod_primes h
    have hodd : ¬ (2 ∣ ∏ p ∈ t, p) := by
      intro hdvd
      obtain ⟨q, hq, hpq⟩ := (Nat.prime_two.prime).exists_mem_finset_dvd hdvd
      exact (hgood q hq).1 (((h q hq).dvd_iff_eq (Nat.prime_two.ne_one)).1 hpq)
    have hcop : Nat.Coprime (∏ p ∈ t, p) d := by
      exact Nat.Coprime.prod_left fun p hp =>
        (Nat.Prime.coprime_iff_not_dvd (h p hp)).2 (hgood p hp).2
    rw [betaCop, if_pos hcop, beta_of_odd_squarefree hsq hodd, Nat.primeFactors_prod h,
      Finset.prod_congr rfl (fun p hp => betaCop_prime (h p hp))]
    rw [Finset.prod_congr rfl (fun p hp => if_pos (hgood p hp))]
    rw [one_div, ← Finset.prod_inv_distrib]
    simp [one_div]
  · push_neg at hgood
    obtain ⟨q, hq, hbad⟩ := hgood
    have hqbad : betaCop d q = 0 := by
      rw [betaCop_prime (h q hq)]
      by_cases h2 : q = 2
      · simp [h2]
      · simp [h2, hbad h2]
    have hright : ∏ p ∈ t, betaCop d p = 0 :=
      Finset.prod_eq_zero hq hqbad
    have hleft : betaCop d (∏ p ∈ t, p) = 0 := by
      have hdvd : q ∣ ∏ p ∈ t, p := Finset.dvd_prod_of_mem _ hq
      by_cases h2 : q = 2
      · subst h2
        rw [betaCop]; split <;> simp [beta_eq_zero_of_even hdvd]
      · have hqd : q ∣ d := hbad h2
        have : ¬ Nat.Coprime (∏ p ∈ t, p) d := by
          intro hcop
          have : q ∣ Nat.gcd (∏ p ∈ t, p) d := Nat.dvd_gcd hdvd hqd
          rw [Nat.Coprime] at hcop
          rw [hcop] at this
          exact (h q hq).one_lt.ne' (Nat.dvd_one.1 this)
        simp [betaCop, this]
    rw [hleft, hright]

/-! ## §3.4  The all-complement discrete identity -/

/-- **`allComplement_discrete`.**  `KERNEL-PROVED`.  For all `d, n ≠ 0`,

    B(d) · ∑_{k ∣ n, (k,d)=1} β(k) = B(d·n).

Proved by finite prime-factor products; no infinite Euler product is involved. -/
theorem allComplement_discrete (B1 : ℚ) {d n : ℕ} (hd0 : d ≠ 0) (hn0 : n ≠ 0) :
    B B1 d * ∑ k ∈ n.divisors, betaCop d k = B B1 (d * n) := by
  classical
  set T : Finset ℕ := oddPrimeFactors n \ oddPrimeFactors d with hT
  -- Step 1: the divisor sum is a finite product over the primes of `n`.
  have hsum : ∑ k ∈ n.divisors, betaCop d k = ∏ p ∈ n.primeFactors, (1 + betaCop d p) :=
    sum_divisors_of_squarefreeSupported hn0 _
      (fun k hk => betaCop_eq_zero_of_not_squarefree hk)
      (fun t ht => betaCop_prod_primes d ht)
  -- Step 2: only the odd primes of `n` not dividing `d` contribute.
  have hTsub : T ⊆ n.primeFactors := by
    intro p hp
    exact (mem_oddPrimeFactors.1 (Finset.mem_sdiff.1 hp).1).2
  have hprod : ∏ p ∈ n.primeFactors, (1 + betaCop d p) = ∏ p ∈ T, (((p : ℚ) - 1) / ((p : ℚ) - 2)) := by
    rw [← Finset.prod_subset hTsub (fun p hp hpT => ?_)]
    · refine Finset.prod_congr rfl fun p hp => ?_
      have hmem := Finset.mem_sdiff.1 hp
      have hprime : p.Prime := oddPrimeFactors_prime hmem.1
      have h2 : p ≠ 2 := oddPrimeFactors_ne_two hmem.1
      have hnd : ¬ p ∣ d := by
        intro hdvd
        exact hmem.2 (mem_oddPrimeFactors.2 ⟨h2, Nat.mem_primeFactors.2 ⟨hprime, hdvd, hd0⟩⟩)
      rw [betaCop_prime hprime, if_pos ⟨h2, hnd⟩]
      have := sub_two_ne_zero hprime h2
      field_simp
      ring
    · -- primes of `n` outside `T` carry local factor `1`
      have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      rw [betaCop_prime hprime]
      by_cases h2 : p = 2
      · simp [h2]
      · have hdvd : p ∣ d := by
          by_contra hnd
          exact hpT (Finset.mem_sdiff.2 ⟨mem_oddPrimeFactors.2 ⟨h2, hp⟩,
            fun hmem => hnd (Nat.dvd_of_mem_primeFactors (mem_oddPrimeFactors.1 hmem).2)⟩)
        simp [hdvd]
  -- Step 3: `B0(d·n) = B0(d) · ∏_T`.
  have hB0 : B0 (d * n) = B0 d * ∏ p ∈ T, (((p : ℚ) - 1) / ((p : ℚ) - 2)) := by
    rw [B0, B0, oddPrimeFactors_mul hd0 hn0, ← Finset.union_sdiff_self_eq_union, ← hT,
      Finset.prod_union (Finset.disjoint_sdiff)]
  rw [hsum, hprod, B, B, hB0]
  ring

/-- **`allComplement_discrete_odd`.**  The identity in the requested odd-`d` form. -/
theorem allComplement_discrete_odd (B1 : ℚ) {d n : ℕ} (hd : Odd d) (hn0 : n ≠ 0) :
    B B1 d * ∑ k ∈ n.divisors, betaCop d k = B B1 (d * n) :=
  allComplement_discrete B1 (by rintro rfl; simp [Nat.odd_iff] at hd) hn0

end Effectivity
end Erdos287
