import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V22 §2: the fixed finite exceptional prime set

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`excSet K base slopes` is the fixed finite set `E` of primes consisting of

* all primes `≤ 2K + 2`;
* the primes dividing the base;
* the primes dividing the slopes;
* the primes dividing the nonzero slope differences.

`P_E = ∏_{p ∈ E} p`.  **This is an AUXILIARY presieve only**: `excSet` takes no `W0` argument and
the historical `W0` is not modified; `P_E` is a fixed positive integer and is never set to `1`.

Kernel-proved (LEAN BANK): `mem_excSet_prime`, `small_prime_mem`, `base_prime_mem`,
`slope_prime_mem`, `diff_prime_mem`, `P_E_pos`, `not_dvd_P_E_of_not_mem`,
`good_prime_gt` (a prime outside `E` exceeds `2K+2`), `coprime_P_E_iff`.
-/

namespace Erdos287
namespace ResearchBankV22
namespace ExceptionalPrimeSet

/-- The fixed exceptional prime set `E`. -/
def excSet (K base : ℕ) (slopes : Finset ℕ) : Finset ℕ :=
  (Finset.range (2 * K + 3)).filter Nat.Prime ∪ base.primeFactors ∪
    slopes.biUnion Nat.primeFactors ∪
    (slopes ×ˢ slopes).biUnion fun ab => (Int.natAbs ((ab.1 : ℤ) - ab.2)).primeFactors

/-- `P_E = ∏_{p ∈ E} p`. -/
def P_E (K base : ℕ) (slopes : Finset ℕ) : ℕ := ∏ p ∈ excSet K base slopes, p

variable {K base : ℕ} {slopes : Finset ℕ}

theorem mem_excSet_prime {p : ℕ} (hp : p ∈ excSet K base slopes) : p.Prime := by
  simp only [excSet, Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion,
    Nat.mem_primeFactors] at hp
  rcases hp with ((⟨-, h⟩ | ⟨h, -⟩) | ⟨_, -, h, -⟩) | ⟨_, -, h, -⟩ <;> exact h

theorem small_prime_mem {p : ℕ} (hp : p.Prime) (hle : p ≤ 2 * K + 2) :
    p ∈ excSet K base slopes := by
  simp only [excSet, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
  exact Or.inl (Or.inl (Or.inl ⟨by omega, hp⟩))

theorem base_prime_mem {p : ℕ} (hp : p.Prime) (hd : p ∣ base) (hb : base ≠ 0) :
    p ∈ excSet K base slopes := by
  simp only [excSet, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inr (Nat.mem_primeFactors.2 ⟨hp, hd, hb⟩)))

theorem slope_prime_mem {p a : ℕ} (ha : a ∈ slopes) (hp : p.Prime) (hd : p ∣ a) (ha0 : a ≠ 0) :
    p ∈ excSet K base slopes := by
  simp only [excSet, Finset.mem_union, Finset.mem_biUnion]
  exact Or.inl (Or.inr ⟨a, ha, Nat.mem_primeFactors.2 ⟨hp, hd, ha0⟩⟩)

theorem diff_prime_mem {p a b : ℕ} (ha : a ∈ slopes) (hb : b ∈ slopes) (hp : p.Prime)
    (hd : (p : ℤ) ∣ (a : ℤ) - b) (hab : a ≠ b) : p ∈ excSet K base slopes := by
  simp only [excSet, Finset.mem_union, Finset.mem_biUnion]
  refine Or.inr ⟨(a, b), Finset.mem_product.2 ⟨ha, hb⟩, Nat.mem_primeFactors.2 ⟨hp, ?_, ?_⟩⟩
  · exact Int.natCast_dvd.1 hd
  · simp only [ne_eq, Int.natAbs_eq_zero]; omega

theorem P_E_pos : 0 < P_E K base slopes :=
  Finset.prod_pos fun _ hp => (mem_excSet_prime hp).pos

theorem not_dvd_P_E_of_not_mem {p : ℕ} (hp : p.Prime) (hE : p ∉ excSet K base slopes) :
    ¬ p ∣ P_E K base slopes := by
  intro h
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 h
  have hq' := mem_excSet_prime hq
  rw [(Nat.prime_dvd_prime_iff_eq hp hq').1 hpq] at hE
  exact hE hq

/-- A good prime (outside `E`) exceeds `2K + 2`. -/
theorem good_prime_gt {p : ℕ} (hp : p.Prime) (hE : p ∉ excSet K base slopes) : 2 * K + 2 < p := by
  by_contra h
  exact hE (small_prime_mem hp (by omega))

/-- `gcd(n, P_E) = 1` iff no prime of `E` divides `n`. -/
theorem coprime_P_E_iff (n : ℕ) :
    Nat.Coprime n (P_E K base slopes) ↔ ∀ p ∈ excSet K base slopes, ¬ p ∣ n := by
  unfold P_E
  rw [Nat.coprime_prod_right_iff]
  refine forall₂_congr fun _ hp => ?_
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (mem_excSet_prime hp)]

end ExceptionalPrimeSet
end ResearchBankV22
end Erdos287
