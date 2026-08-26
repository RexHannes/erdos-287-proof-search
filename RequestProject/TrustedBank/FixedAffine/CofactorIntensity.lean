import Mathlib
import RequestProject.TrustedBank.Erdos287.BoundedCofactor

/-!
# Trusted bank — Bank G: cofactor intensity optimality (finite proxy)

For an admissible coprime pair `(d, e)` with `d e` even we set `n = d e` and consider
the finite rational intensity proxy

`J n = (1/n) * ∏_{odd primes p ∣ n} (p-1)/(p-2)`,

which is exactly the finite arithmetic content of the singular-series comparison
(Bank F: an odd prime dividing `d e` contributes the correction factor `(p-1)/(p-2)`,
and the density carries the overall factor `1/n`).

We prove `J n ≤ J 2 = 1/2` for every even `n`, with equality only for `n = 2`, and
translate `n = 2` with `gcd (d, e) = 1` into `{d, e} = {1, 2}`.

No infinite Euler product is used.
-/

open scoped BigOperators

namespace TrustedBank
namespace CofactorIntensity

/-- The odd prime divisors of `n`. -/
def oddPrimeFactors (n : ℕ) : Finset ℕ := n.primeFactors.filter (fun p => p ≠ 2)

/-- The finite rational intensity proxy
`J n = (1/n) ∏_{odd p ∣ n} (p-1)/(p-2)`. -/
def J (n : ℕ) : ℚ := (1 / (n : ℚ)) * ∏ p ∈ oddPrimeFactors n, (((p : ℚ) - 1) / ((p : ℚ) - 2))

lemma three_le_of_mem_oddPrimeFactors {n p : ℕ} (hp : p ∈ oddPrimeFactors n) : 3 ≤ p := by
  simp only [oddPrimeFactors, Finset.mem_filter, Nat.mem_primeFactors] at hp
  obtain ⟨⟨hprime, _, _⟩, hne⟩ := hp
  have := hprime.two_le
  omega

lemma prime_of_mem_oddPrimeFactors {n p : ℕ} (hp : p ∈ oddPrimeFactors n) : p.Prime := by
  simp only [oddPrimeFactors, Finset.mem_filter, Nat.mem_primeFactors] at hp
  exact hp.1.1

lemma dvd_of_mem_oddPrimeFactors {n p : ℕ} (hp : p ∈ oddPrimeFactors n) : p ∣ n := by
  simp only [oddPrimeFactors, Finset.mem_filter, Nat.mem_primeFactors] at hp
  exact hp.1.2.1

/-- Pointwise: for an odd prime `p ≥ 3`, `(p-1)/(p-2) < p`. -/
lemma factor_lt_prime {p : ℕ} (hp : 3 ≤ p) : ((p : ℚ) - 1) / ((p : ℚ) - 2) < (p : ℚ) := by
  have hp3 : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
  have h2 : (0 : ℚ) < (p : ℚ) - 2 := by linarith
  rw [div_lt_iff₀ h2]
  nlinarith

/-- `2 · ∏_{odd p ∣ n} p ∣ n` for even `n`, hence `2 · ∏ ≤ n`. -/
lemma two_mul_prod_le {n : ℕ} (hn : 2 ∣ n) (hpos : 0 < n) :
    2 * ∏ p ∈ oddPrimeFactors n, p ≤ n := by
  have hdvd : (∏ p ∈ oddPrimeFactors n, p) ∣ n := by
    refine dvd_trans ?_ (Nat.prod_primeFactors_dvd n)
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
  have hcop : Nat.Coprime 2 (∏ p ∈ oddPrimeFactors n, p) := by
    refine Nat.Coprime.prod_right ?_
    intro p hp
    have hprime := prime_of_mem_oddPrimeFactors hp
    have h3 := three_le_of_mem_oddPrimeFactors hp
    exact (Nat.coprime_primes Nat.prime_two hprime).mpr (by omega)
  have : 2 * (∏ p ∈ oddPrimeFactors n, p) ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hn hdvd
  exact Nat.le_of_dvd hpos this

/-- **Bank G.1 — `J 2 = 1/2`.** -/
theorem J_two : J 2 = 1 / 2 := by
  have h : oddPrimeFactors 2 = ∅ := by
    simp [oddPrimeFactors, Nat.Prime.primeFactors Nat.prime_two]
  simp [J, h]

/-- **Bank G.2 — the optimality bound** `J n ≤ 1/2` for every even `n > 0`. -/
theorem J_le_half {n : ℕ} (hn : 2 ∣ n) (hpos : 0 < n) : J n ≤ 1 / 2 := by
  have hn0 : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hpos
  have hprod : ∏ p ∈ oddPrimeFactors n, (((p : ℚ) - 1) / ((p : ℚ) - 2))
      ≤ ∏ p ∈ oddPrimeFactors n, (p : ℚ) := by
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have h3 := three_le_of_mem_oddPrimeFactors hp
      have hp3 : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast h3
      have h2 : (0 : ℚ) < (p : ℚ) - 2 := by linarith
      apply div_nonneg <;> linarith
    · exact (factor_lt_prime (three_le_of_mem_oddPrimeFactors hp)).le
  have hle : 2 * ∏ p ∈ oddPrimeFactors n, p ≤ n := two_mul_prod_le hn hpos
  have hleQ : 2 * ∏ p ∈ oddPrimeFactors n, ((p : ℚ)) ≤ (n : ℚ) := by
    have : ((2 * ∏ p ∈ oddPrimeFactors n, p : ℕ) : ℚ) ≤ ((n : ℕ) : ℚ) := by exact_mod_cast hle
    push_cast at this
    exact this
  have hJ : J n ≤ (1 / (n : ℚ)) * ∏ p ∈ oddPrimeFactors n, (p : ℚ) := by
    unfold J
    exact mul_le_mul_of_nonneg_left hprod (by positivity)
  calc J n ≤ (1 / (n : ℚ)) * ∏ p ∈ oddPrimeFactors n, (p : ℚ) := hJ
    _ ≤ (1 / (n : ℚ)) * ((n : ℚ) / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = 1 / 2 := by field_simp

/-- **Bank G.3 — strictness.**  For an even `n ≠ 2`, the intensity is strictly smaller. -/
theorem J_lt_half {n : ℕ} (hn : 2 ∣ n) (hpos : 0 < n) (hne : n ≠ 2) : J n < 1 / 2 := by
  have hn0 : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hpos
  by_cases hS : (oddPrimeFactors n).Nonempty
  · -- some odd prime divides `n`: the product inequality is strict
    have hprod : ∏ p ∈ oddPrimeFactors n, (((p : ℚ) - 1) / ((p : ℚ) - 2))
        < ∏ p ∈ oddPrimeFactors n, (p : ℚ) := by
      obtain ⟨p₀, hp₀⟩ := hS
      refine Finset.prod_lt_prod (fun p hp => ?_) (fun p hp => ?_) ⟨p₀, hp₀, ?_⟩
      · have h3 := three_le_of_mem_oddPrimeFactors hp
        have hp3 : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast h3
        have h2 : (0 : ℚ) < (p : ℚ) - 2 := by linarith
        apply div_pos <;> linarith
      · exact (factor_lt_prime (three_le_of_mem_oddPrimeFactors hp)).le
      · exact factor_lt_prime (three_le_of_mem_oddPrimeFactors hp₀)
    have hle : 2 * ∏ p ∈ oddPrimeFactors n, p ≤ n := two_mul_prod_le hn hpos
    have hleQ : 2 * ∏ p ∈ oddPrimeFactors n, ((p : ℚ)) ≤ (n : ℚ) := by
      have : ((2 * ∏ p ∈ oddPrimeFactors n, p : ℕ) : ℚ) ≤ ((n : ℕ) : ℚ) := by exact_mod_cast hle
      push_cast at this
      exact this
    have h1 : J n < (1 / (n : ℚ)) * ∏ p ∈ oddPrimeFactors n, (p : ℚ) := by
      unfold J
      exact mul_lt_mul_of_pos_left hprod (by positivity)
    calc J n < (1 / (n : ℚ)) * ∏ p ∈ oddPrimeFactors n, (p : ℚ) := h1
      _ ≤ (1 / (n : ℚ)) * ((n : ℚ) / 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ = 1 / 2 := by field_simp
  · -- no odd prime divides `n`, so `n` is a power of two and `n ≥ 4`
    rw [Finset.not_nonempty_iff_eq_empty] at hS
    have h4 : 4 ≤ n := by
      rcases Nat.lt_or_ge n 4 with h | h
      · interval_cases n <;> simp_all
      · exact h
    have h4Q : (4 : ℚ) ≤ (n : ℚ) := by exact_mod_cast h4
    unfold J
    rw [hS, Finset.prod_empty, mul_one]
    rw [div_lt_div_iff₀ hn0 (by norm_num)]
    linarith

/-- **Bank G.4 — `J n ≤ J 2` with equality only at `n = 2`.** -/
theorem J_le_J_two {n : ℕ} (hn : 2 ∣ n) (hpos : 0 < n) : J n ≤ J 2 := by
  rw [J_two]; exact J_le_half hn hpos

/-- **Bank G.5 — equality characterisation.** -/
theorem J_eq_J_two_iff {n : ℕ} (hn : 2 ∣ n) (hpos : 0 < n) : J n = J 2 ↔ n = 2 := by
  constructor
  · intro h
    by_contra hne
    have := J_lt_half hn hpos hne
    rw [J_two] at h
    linarith
  · rintro rfl; rfl

/-! ## Translation back to the cofactor pair -/

open BoundedCofactor

/-- **Bank G.6 — `d e = 2` with `d, e > 0` forces `{d, e} = {1, 2}`.** -/
theorem de_eq_two (B : Bez) (h : B.d * B.e = 2) :
    (B.d = 1 ∧ B.e = 2) ∨ (B.d = 2 ∧ B.e = 1) := by
  have hd := B.hd
  have he := B.he
  have hd2 : B.d ≤ 2 := by nlinarith
  interval_cases (B.d) <;> omega

end CofactorIntensity
end TrustedBank
