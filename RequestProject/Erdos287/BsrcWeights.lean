import Mathlib

/-!
# Erdős #287 effectivity — physical `B_src` normalisation (§2)

```
PHYSICAL B1 NORMALIZATION : KERNEL-PROVED
B0 MULTIPLICATIVITY       : KERNEL-PROVED
beta MULTIPLICATIVITY     : KERNEL-PROVED
B1-ONCE FIREWALL          : KERNEL-PROVED
```

The physical normalisation carries the global constant `B1` **once**:

    B0(n) = ∏_{p ∣ n, p > 2} (p−1)/(p−2),      B(n) = B1 · B0(n),

    β(k)  = μ(k)² · 1_{2 ∤ k} / ∏_{p ∣ k} (p − 2).

`B0` and `β` are multiplicative on coprime arguments; `B` is **not** — the
correct typed relation is `B1 · B(ab) = B(a)·B(b)`, and
`B1_onceFirewall` records the concrete failure of the "one `B1` per prime
factor" normalisation.

Everything in this file is finite: products range over `Nat.primeFactors`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos287
namespace Effectivity

/-! ## §2.1  Definitions -/

/-- The odd prime factors of `n`. -/
def oddPrimeFactors (n : ℕ) : Finset ℕ := n.primeFactors.erase 2

lemma mem_oddPrimeFactors {n p : ℕ} :
    p ∈ oddPrimeFactors n ↔ p ≠ 2 ∧ p ∈ n.primeFactors := by
  simp [oddPrimeFactors]

lemma oddPrimeFactors_prime {n p : ℕ} (hp : p ∈ oddPrimeFactors n) : p.Prime :=
  Nat.prime_of_mem_primeFactors (mem_oddPrimeFactors.1 hp).2

lemma oddPrimeFactors_ne_two {n p : ℕ} (hp : p ∈ oddPrimeFactors n) : p ≠ 2 :=
  (mem_oddPrimeFactors.1 hp).1

/-- For `p` an odd prime, `(p : ℚ) − 2 ≠ 0`. -/
lemma sub_two_ne_zero {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : ((p : ℚ) - 2) ≠ 0 := by
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast h3
  intro h; linarith [sub_eq_zero.1 h]

/-- `B0(n) = ∏_{p ∣ n, p > 2} (p−1)/(p−2)`, the normalised local factor. -/
def B0 (n : ℕ) : ℚ := ∏ p ∈ oddPrimeFactors n, (((p : ℚ) - 1) / ((p : ℚ) - 2))

/-- `B(n) = B1 · B0(n)`: the physical source weight, with the global constant `B1`
appearing **exactly once**. -/
def B (B1 : ℚ) (n : ℕ) : ℚ := B1 * B0 n

/-- `β(k) = μ(k)² 1_{2∤k} / ∏_{p ∣ k}(p−2)`. -/
def beta (k : ℕ) : ℚ :=
  (if Squarefree k ∧ ¬ (2 ∣ k) then (1 : ℚ) else 0) / ∏ p ∈ k.primeFactors, ((p : ℚ) - 2)

@[simp] lemma B0_one : B0 1 = 1 := by simp [B0, oddPrimeFactors]

@[simp] lemma B_one (B1 : ℚ) : B B1 1 = B1 := by simp [B]

@[simp] lemma beta_one : beta 1 = 1 := by simp [beta]

@[simp] lemma beta_zero : beta 0 = 0 := by
  simp [beta]

lemma beta_eq_zero_of_even {k : ℕ} (h : 2 ∣ k) : beta k = 0 := by
  simp [beta, h]

lemma beta_eq_zero_of_not_squarefree {k : ℕ} (h : ¬ Squarefree k) : beta k = 0 := by
  simp [beta, h]

/-- On an odd squarefree argument `β` is the reciprocal of `∏ (p−2)`. -/
lemma beta_of_odd_squarefree {k : ℕ} (hsq : Squarefree k) (hodd : ¬ (2 ∣ k)) :
    beta k = 1 / ∏ p ∈ k.primeFactors, ((p : ℚ) - 2) := by
  simp [beta, hsq, hodd]

/-- `β` at an odd prime. -/
lemma beta_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : beta p = 1 / ((p : ℚ) - 2) := by
  rw [beta_of_odd_squarefree hp.squarefree (by
        intro h
        exact h2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm),
    hp.primeFactors, Finset.prod_singleton]

/-- `B0` at an odd prime. -/
lemma B0_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    B0 p = ((p : ℚ) - 1) / ((p : ℚ) - 2) := by
  rw [B0, oddPrimeFactors, hp.primeFactors, Finset.erase_eq_of_notMem (by simpa using Ne.symm h2),
    Finset.prod_singleton]

/-! ## §2.2  Multiplicativity -/

lemma oddPrimeFactors_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    oddPrimeFactors (a * b) = oddPrimeFactors a ∪ oddPrimeFactors b := by
  simp [oddPrimeFactors, Nat.primeFactors_mul ha hb, Finset.erase_union_distrib]

/-- **`B0_mul`.** `B0` is multiplicative on coprime nonzero arguments. -/
theorem B0_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b) :
    B0 (a * b) = B0 a * B0 b := by
  rw [B0, B0, B0, oddPrimeFactors_mul ha hb, Finset.prod_union]
  refine Finset.disjoint_left.2 fun p hpa hpb => ?_
  exact (Finset.disjoint_left.1 hab.disjoint_primeFactors
    (mem_oddPrimeFactors.1 hpa).2) (mem_oddPrimeFactors.1 hpb).2

/-- **`beta_mul`.** `β` is multiplicative on coprime nonzero arguments. -/
theorem beta_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b) :
    beta (a * b) = beta a * beta b := by
  have hprod : ∏ p ∈ (a * b).primeFactors, ((p : ℚ) - 2)
      = (∏ p ∈ a.primeFactors, ((p : ℚ) - 2)) * ∏ p ∈ b.primeFactors, ((p : ℚ) - 2) := by
    rw [Nat.primeFactors_mul ha hb, Finset.prod_union hab.disjoint_primeFactors]
  by_cases hsq : Squarefree (a * b)
  · have hsa : Squarefree a := hsq.of_mul_left
    have hsb : Squarefree b := hsq.of_mul_right
    by_cases h2 : 2 ∣ a * b
    · rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h | h
      · rw [beta_eq_zero_of_even h2, beta_eq_zero_of_even h, zero_mul]
      · rw [beta_eq_zero_of_even h2, beta_eq_zero_of_even h, mul_zero]
    · have h2a : ¬ (2 ∣ a) := fun h => h2 (h.mul_right b)
      have h2b : ¬ (2 ∣ b) := fun h => h2 (Dvd.dvd.mul_left h a)
      rw [beta_of_odd_squarefree hsq h2, beta_of_odd_squarefree hsa h2a,
        beta_of_odd_squarefree hsb h2b, hprod]
      field_simp
  · have : ¬ Squarefree a ∨ ¬ Squarefree b := by
      by_contra hcon
      push_neg at hcon
      exact hsq ((Nat.squarefree_mul hab).2 ⟨hcon.1, hcon.2⟩)
    rcases this with h | h
    · rw [beta_eq_zero_of_not_squarefree hsq, beta_eq_zero_of_not_squarefree h, zero_mul]
    · rw [beta_eq_zero_of_not_squarefree hsq, beta_eq_zero_of_not_squarefree h, mul_zero]

/-- **`B_mul_typed`.** `B` is *not* multiplicative: the physical relation on coprime
arguments is `B1 · B(ab) = B(a)·B(b)`, i.e. `B1` occurs once. -/
theorem B_mul_typed (B1 : ℚ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b) :
    B1 * B B1 (a * b) = B B1 a * B B1 b := by
  simp only [B, B0_mul ha hb hab]; ring

/-! ## §2.3  The `B1`-once firewall -/

lemma primeFactors_fifteen : (15 : ℕ).primeFactors = {3, 5} := by
  have h : (15 : ℕ) = 3 * 5 := by norm_num
  rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
  rfl

lemma oddPrimeFactors_fifteen : oddPrimeFactors 15 = {3, 5} := by
  rw [oddPrimeFactors, primeFactors_fifteen]
  decide

@[simp] lemma B0_fifteen : B0 15 = 8 / 3 := by
  rw [B0, oddPrimeFactors_fifteen]; norm_num

/-- **`B1_onceFirewall`.** `KERNEL-PROVED`.  Encoding `B1` once per prime factor is a
genuinely different (wrong) normalisation: at `n = 15` the two disagree for every
`B1 ∉ {0, 1}`. -/
theorem B1_onceFirewall (B1 : ℚ) (h0 : B1 ≠ 0) (h1 : B1 ≠ 1) :
    B B1 15 ≠ B1 ^ 2 * B0 15 := by
  rw [B, B0_fifteen]
  intro h
  have key : B1 * (B1 - 1) = 0 := by nlinarith [h]
  rcases mul_eq_zero.1 key with h' | h'
  · exact h0 h'
  · exact h1 (by linarith [sub_eq_zero.1 h'])

/-- `B0` ignores the prime `2`: powers of two carry no odd local factor. -/
@[simp] theorem B0_two_pow (k : ℕ) : B0 (2 ^ k) = 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [B0, oddPrimeFactors, Nat.primeFactors_prime_pow hk.ne' Nat.prime_two]
    simp

end Effectivity
end Erdos287
