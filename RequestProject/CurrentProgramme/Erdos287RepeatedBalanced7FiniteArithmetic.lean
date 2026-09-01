import RequestProject.CurrentProgramme.Erdos287K0SP2FourClassPartition
import RequestProject.CurrentProgramme.Erdos287RepeatedPrimePhysicalSource

/-!
# Repeated-Balanced7 finite arithmetic: the depth-3 divisor identity

`REPEATED BALANCED7 FINITE ARITHMETIC : KERNEL-PROVED`

This module is **append-only**.

It proves the divisor-count identity behind the repeated-Balanced7 coefficient
table.  For a squarefree row `P` with exactly `r` distinct prime divisors, the
depth-`k` truncated Möbius sum

```
M^{(k)}(P) = ∑_{e ∣ P, ω(e) ≤ k} μ(e)
```

equals `∑_{j ≤ k} (−1)^j C(r, j)`; at the strict-cell depth `k = 3` this is the
banked value `Hrepeat r = −C(r−1, 3)` of `Erdos287RepeatedPrimePhysicalSource`.

The finite coefficient table is banked explicitly:

```
r = 7 → −20,   r = 6 → −10,   r = 5 → −4,   r = 4 → −1,   1 ≤ r ≤ 3 → 0.
```

**Firewall.**  The asymptotic `X^{6/7}` count of repeated-Balanced7 rows is
**not** formalised here; it remains a named paper/external input
(`RepeatedBalanced7CountInput`, left uninhabited).  Only the finite divisor
identity and the finite table are kernel theorems.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos287
namespace RepeatedBalanced7

/-! ## §1.  Möbius on a product of distinct primes -/

/-- `μ(∏_{p ∈ s} p) = (−1)^{|s|}` for a finite set `s` of distinct primes. -/
theorem moebius_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    moebius (∏ p ∈ s, p) = (-1) ^ s.card := by
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      have hap : a.Prime := hs a (by simp)
      have ht : ∀ p ∈ t, p.Prime := fun p hp => hs p (by simp [hp])
      have hcop : Nat.Coprime a (∏ p ∈ t, p) :=
        Nat.Coprime.prod_right fun i hi =>
          (Nat.coprime_primes hap (ht i hi)).2 (by rintro rfl; exact ha hi)
      rw [isMultiplicative_moebius.map_mul_of_coprime hcop, ih ht, moebius_apply_prime hap]
      ring

/-- A product of distinct primes is squarefree. -/
theorem squarefree_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.prod_insert ha]
      have hap : a.Prime := hs a (by simp)
      have ht : ∀ p ∈ t, p.Prime := fun p hp => hs p (by simp [hp])
      have hcop : Nat.Coprime a (∏ p ∈ t, p) :=
        Nat.Coprime.prod_right fun i hi =>
          (Nat.coprime_primes hap (ht i hi)).2 (by rintro rfl; exact ha hi)
      exact Nat.squarefree_mul_iff.2 ⟨hcop, hap.squarefree, ih ht⟩

/-- `μ(e) = (−1)^{ω(e)}` for squarefree `e`. -/
theorem moebius_eq_neg_one_pow_omega {e : ℕ} (h : Squarefree e) :
    moebius e = (-1) ^ e.primeFactors.card := by
  have := moebius_prod_primes e.primeFactors fun p hp => Nat.prime_of_mem_primeFactors hp
  rwa [Nat.prod_primeFactors_of_squarefree h] at this

/-! ## §2.  The depth-truncated divisor sum -/

/-- **`depthMoebius n k = ∑_{e ∣ n, ω(e) ≤ k} μ(e)`**, the depth-`k` truncated Möbius
sum over the divisor lattice of `n`. -/
def depthMoebius (n k : ℕ) : ℤ :=
  ∑ e ∈ n.divisors.filter (fun e => e.primeFactors.card ≤ k), (moebius e : ℤ)

/-- The alternating-subset sum on a finite set `s`, truncated at cardinality `k`. -/
theorem alternating_subset_sum (s : Finset ℕ) (k : ℕ) :
    ∑ t ∈ s.powerset.filter (fun t => t.card ≤ k), (-1 : ℤ) ^ t.card
      = ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * (s.card.choose j : ℤ) := by
  have hEq : s.powerset.filter (fun t => t.card ≤ k)
      = (Finset.range (k + 1)).biUnion (fun j => Finset.powersetCard j s) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨t.card, by omega, h1, rfl⟩
    · rintro ⟨j, hj, h1, rfl⟩; exact ⟨h1, by omega⟩
  rw [hEq, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl ?_
    intro j _
    have hcard : ∀ t ∈ Finset.powersetCard j s, (-1 : ℤ) ^ t.card = (-1 : ℤ) ^ j :=
      fun t ht => by rw [(Finset.mem_powersetCard.1 ht).2]
    rw [Finset.sum_congr rfl hcard, Finset.sum_const, Finset.card_powersetCard]
    simp [mul_comm]
  · intro a _ b _ hab
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_powersetCard]
    rintro t ⟨-, rfl⟩ ⟨-, h⟩
    exact hab h

/-- **The divisor-lattice transfer.**  For a squarefree `n`, the depth-`k` Möbius sum over
the divisors of `n` equals the truncated alternating subset sum over the prime support. -/
theorem depthMoebius_eq_subset_sum {n : ℕ} (hn : Squarefree n) (k : ℕ) :
    depthMoebius n k
      = ∑ t ∈ n.primeFactors.powerset.filter (fun t => t.card ≤ k), (-1 : ℤ) ^ t.card := by
  have hn0 : n ≠ 0 := hn.ne_zero
  have hs : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  refine Finset.sum_nbij' (i := fun e => e.primeFactors) (j := fun t => ∏ p ∈ t, p)
    ?_ ?_ ?_ ?_ ?_
  · intro e he
    simp only [Finset.mem_filter, Nat.mem_divisors] at he
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Nat.primeFactors_mono he.1.1 hn0, he.2⟩
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_powerset] at ht
    have hts : ∀ p ∈ t, p.Prime := fun p hp => hs p (ht.1 hp)
    simp only [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, hn0⟩, ?_⟩
    · calc ∏ p ∈ t, p ∣ ∏ p ∈ n.primeFactors, p :=
            Finset.prod_dvd_prod_of_subset _ _ _ ht.1
        _ = n := Nat.prod_primeFactors_of_squarefree hn
    · rw [Nat.primeFactors_prod hts]; exact ht.2
  · intro e he
    simp only [Finset.mem_filter, Nat.mem_divisors] at he
    exact Nat.prod_primeFactors_of_squarefree (hn.squarefree_of_dvd he.1.1)
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_powerset] at ht
    exact Nat.primeFactors_prod fun p hp => hs p (ht.1 hp)
  · intro e he
    simp only [Finset.mem_filter, Nat.mem_divisors] at he
    exact moebius_eq_neg_one_pow_omega (hn.squarefree_of_dvd he.1.1)

/-- **The depth-`k` divisor-count identity.**  For squarefree `n` with `ω(n) = r`,
`M^{(k)}(n) = ∑_{j ≤ k} (−1)^j C(r, j)`. -/
theorem depthMoebius_eq_alternating {n : ℕ} (hn : Squarefree n) (k : ℕ) :
    depthMoebius n k
      = ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * (n.primeFactors.card.choose j : ℤ) := by
  rw [depthMoebius_eq_subset_sum hn k, alternating_subset_sum]

/-! ## §3.  The strict-cell depth `3` and the banked coefficient table -/

open Erdos287.RepeatedPrime

/-- **`depthMoebius_three_eq_Hrepeat`.**  `KERNEL-PROVED`.

At the strict-cell truncation depth `3`, the truncated Möbius coefficient of a squarefree
row with `r` distinct primes is the banked finite value `Hrepeat r`. -/
theorem depthMoebius_three_eq_Hrepeat {n : ℕ} (hn : Squarefree n) :
    depthMoebius n 3 = Hrepeat n.primeFactors.card := by
  rw [depthMoebius_eq_alternating hn 3, Hrepeat_eq_range_four]

/-- **`depthMoebius_three_eq_neg_choose`.**  `KERNEL-PROVED`.

The closed form `M^{(3)}(P) = −C(r−1, 3)` for a squarefree row with `r ≥ 1` distinct
primes. -/
theorem depthMoebius_three_eq_neg_choose {n : ℕ} (hn : Squarefree n)
    (hr : 1 ≤ n.primeFactors.card) :
    depthMoebius n 3 = -(((n.primeFactors.card - 1).choose 3 : ℕ) : ℤ) := by
  rw [depthMoebius_three_eq_Hrepeat hn, Hrepeat_eq_neg_choose hr]

/-- **`depthMoebius_three_table`.**  `KERNEL-PROVED`.

The banked finite coefficient table at strict-cell depth `3`. -/
theorem depthMoebius_three_table {n : ℕ} (hn : Squarefree n) :
    (n.primeFactors.card = 7 → depthMoebius n 3 = -20) ∧
    (n.primeFactors.card = 6 → depthMoebius n 3 = -10) ∧
    (n.primeFactors.card = 5 → depthMoebius n 3 = -4) ∧
    (n.primeFactors.card = 4 → depthMoebius n 3 = -1) ∧
    (1 ≤ n.primeFactors.card → n.primeFactors.card ≤ 3 → depthMoebius n 3 = 0) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h1 h2 => ?_⟩ <;>
    rw [depthMoebius_three_eq_Hrepeat hn]
  · rw [h]; exact Hrepeat_seven
  · rw [h]; exact Hrepeat_six
  · rw [h]; exact Hrepeat_five
  · rw [h]; exact Hrepeat_four
  · exact Hrepeat_table.2.2.2.2 _ h1 h2

/-- The `r = 0` edge case is recorded explicitly: the empty row has `M^{(3)}(1) = 1`,
not `0`. -/
theorem depthMoebius_three_one : depthMoebius 1 3 = 1 := by
  rw [depthMoebius_three_eq_Hrepeat squarefree_one]
  simpa using Hrepeat_zero

/-! ## §4.  The asymptotic count is an external input, and is left uninhabited -/

/-- **`RepeatedBalanced7CountInput`** — `PAPER/EXTERNAL ANALYTIC / UNINHABITED`.

The `X^{6/7}`-type upper bound for the number of repeated-Balanced7 rows below `X`.
It is *not* proved in this repository and nothing here inhabits it; it is carried as an
explicit parameter wherever a downstream negligibility claim would need it. -/
structure RepeatedBalanced7CountInput where
  /-- The implied constant. -/
  c : ℝ
  /-- The exponent budget, `θ < 1`. -/
  theta : ℝ
  /-- The exponent is a genuine saving. -/
  theta_lt_one : theta < 1
  /-- The counting bound, as an explicit hypothesis about an abstract counting function. -/
  count : ℕ → ℝ
  /-- The bound itself.  **Not proved here.** -/
  bound : ∀ X : ℕ, 1 ≤ X → count X ≤ c * (X : ℝ) ^ theta

end RepeatedBalanced7
end Erdos287
