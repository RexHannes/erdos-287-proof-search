import Mathlib

/-!
# Anchored V4 — normalized prime-power height and the `2·lcm` lattice

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Strictly append-only V4 layer.  Anchored V2 and Anchored V3 are frozen: nothing in this layer
edits, renames, re-proves or weakens any statement of those layers.

This module defines

* `L t = lcm (1, …, t)` (`Nat.lcm` over `Finset.Icc 1 t`);
* the **normalized prime-power height**
  `normHeight n = max 1 (sup over p ∣ n of heightAt n p)` where
  `heightAt n 2 = 2 ^ (v₂ n - 1)` and `heightAt n p = p ^ (v_p n)` for odd `p`;

and proves the exact characterization

`normalizedHeight_le_iff_dvd_two_lcm : n ∣ 2 * L t ↔ normHeight n ≤ t`   (`n ≠ 0`, `1 ≤ t`).

The factor `2` is essential and is *not* cosmetic: `two_factor_essential` exhibits `32 ∣ 2 * L 16`
together with `¬ (32 ∣ L 16)`, and `normalizedHeight_not_le_iff_dvd_lcm` records that the
un-doubled variant `n ∣ L t ↔ normHeight n ≤ t` is **false**.
-/

namespace Erdos287
namespace AnchoredV4

/-- `L t = lcm (1, 2, …, t)`. -/
def L (t : ℕ) : ℕ := (Finset.Icc 1 t).lcm id

@[simp] lemma L_zero : L 0 = 1 := by decide

lemma L_ne_zero (t : ℕ) : L t ≠ 0 := by simp [L, Finset.lcm_eq_zero_iff]

lemma L_pos (t : ℕ) : 0 < L t := Nat.pos_of_ne_zero (L_ne_zero t)

/-- `L` is monotone for divisibility. -/
lemma L_dvd_L {a b : ℕ} (h : a ≤ b) : L a ∣ L b := by
  refine Finset.lcm_dvd ?_
  intro j hj
  simp only [Finset.mem_Icc] at hj
  exact Finset.dvd_lcm (by simp only [Finset.mem_Icc]; omega)

/-- Every `j ∈ [1, t]` divides `L t`. -/
lemma dvd_L {j t : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ t) : j ∣ L t :=
  Finset.dvd_lcm (by simp only [Finset.mem_Icc]; exact ⟨h1, h2⟩)

/-- A prime power divides `Nat.lcm a b` iff it divides one of the two arguments. -/
lemma pow_dvd_lcm_iff {p k a b : ℕ} (hp : p.Prime) (ha : a ≠ 0) (hb : b ≠ 0) :
    p ^ k ∣ Nat.lcm a b ↔ p ^ k ∣ a ∨ p ^ k ∣ b := by
  rw [hp.pow_dvd_iff_le_factorization ha, hp.pow_dvd_iff_le_factorization hb,
    hp.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero ha hb), Nat.factorization_lcm ha hb]
  simp

/-- A nontrivial prime power divides a finite `lcm` iff it divides one of the members. -/
lemma prime_pow_dvd_finset_lcm_iff {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (s : Finset ℕ)
    (h0 : ∀ j ∈ s, j ≠ 0) : p ^ k ∣ s.lcm id ↔ ∃ j ∈ s, p ^ k ∣ j := by
  classical
  induction s using Finset.induction with
  | empty => simpa using ⟨hp.ne_one, by omega⟩
  | insert a s ha ih =>
      have hane : a ≠ 0 := h0 a (by simp)
      have hs0 : ∀ j ∈ s, j ≠ 0 := fun j hj => h0 j (by simp [hj])
      have hlcm0 : s.lcm id ≠ 0 := by
        simp only [ne_eq, Finset.lcm_eq_zero_iff, id_eq,
          not_exists, not_and]
        intro j hj
        exact hs0 j hj
      rw [Finset.lcm_insert]
      have hcast : (lcm (id a) (s.lcm id) : ℕ) = Nat.lcm a (s.lcm id) := rfl
      rw [hcast, pow_dvd_lcm_iff hp hane hlcm0, ih hs0]
      simp

/-- **Exact `p`-adic description of `L t`**: a nontrivial prime power divides `lcm (1, …, t)`
exactly when it is at most `t`. -/
lemma prime_pow_dvd_L_iff {p k t : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    p ^ k ∣ L t ↔ p ^ k ≤ t := by
  rw [L, prime_pow_dvd_finset_lcm_iff hp hk _ (by intro j hj; simp only [Finset.mem_Icc] at hj; omega)]
  constructor
  · rintro ⟨j, hj, hdvd⟩
    simp only [Finset.mem_Icc] at hj
    exact le_trans (Nat.le_of_dvd (by omega) hdvd) hj.2
  · intro h
    exact ⟨p ^ k, by simp only [Finset.mem_Icc]; exact ⟨Nat.one_le_pow _ _ hp.pos, h⟩, dvd_rfl⟩

/-- The normalized prime-power component of `n` at the prime `p`: the full component `p ^ v_p n`
at an odd prime, and the **halved** component `2 ^ (v₂ n - 1)` at `p = 2`. -/
def heightAt (n p : ℕ) : ℕ :=
  if p = 2 then 2 ^ (n.factorization 2 - 1) else p ^ (n.factorization p)

/-- The **normalized prime-power height** of `n`. -/
def normHeight (n : ℕ) : ℕ := max 1 (n.primeFactors.sup (heightAt n))

@[simp] lemma heightAt_two (n : ℕ) : heightAt n 2 = 2 ^ (n.factorization 2 - 1) := by
  simp [heightAt]

lemma heightAt_odd {n p : ℕ} (hp : p ≠ 2) : heightAt n p = p ^ (n.factorization p) := by
  simp [heightAt, hp]

lemma one_le_normHeight (n : ℕ) : 1 ≤ normHeight n := le_max_left _ _

@[simp] lemma normHeight_one : normHeight 1 = 1 := by simp [normHeight]

/-- The normalized height is the maximum of `1` and the normalized prime-power components. -/
lemma normHeight_le_iff {n t : ℕ} :
    normHeight n ≤ t ↔ 1 ≤ t ∧ ∀ p ∈ n.primeFactors, heightAt n p ≤ t := by
  simp [normHeight, Finset.sup_le_iff]

lemma factorization_two_mul_L (p t : ℕ) :
    (2 * L t).factorization p = (if p = 2 then 1 else 0) + (L t).factorization p := by
  rw [Nat.factorization_mul (by norm_num) (L_ne_zero t)]
  simp [Nat.Prime.factorization Nat.prime_two, Finsupp.single_apply, eq_comm]

/-- Componentwise form of the main theorem at one prime divisor. -/
lemma factorization_le_two_mul_L_iff {n p t : ℕ} (hn : n ≠ 0) (hp : p.Prime) (hpn : p ∣ n)
    (ht : 1 ≤ t) :
    n.factorization p ≤ (2 * L t).factorization p ↔ heightAt n p ≤ t := by
  have ha1 : 1 ≤ n.factorization p := Nat.Prime.factorization_pos_of_dvd hp hn hpn
  rw [factorization_two_mul_L]
  by_cases hp2 : p = 2
  · subst hp2
    rw [heightAt_two, if_pos rfl]
    rcases Nat.eq_or_lt_of_le ha1 with h1 | h2
    · rw [← h1]; simp [ht]
    · have hk : 1 ≤ n.factorization 2 - 1 := by omega
      rw [← prime_pow_dvd_L_iff Nat.prime_two hk,
        Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (L_ne_zero t)]
      omega
  · rw [heightAt_odd hp2, if_neg hp2, Nat.zero_add, ← prime_pow_dvd_L_iff hp ha1,
      Nat.Prime.pow_dvd_iff_le_factorization hp (L_ne_zero t)]

/-- **Main theorem of the module.**  For `n ≠ 0` and `1 ≤ t`,

`n ∣ 2 * L t ↔ normHeight n ≤ t`.

The factor `2` on the right of the divisibility is essential; see `two_factor_essential`. -/
theorem normalizedHeight_le_iff_dvd_two_lcm {n t : ℕ} (hn : n ≠ 0) (ht : 1 ≤ t) :
    n ∣ 2 * L t ↔ normHeight n ≤ t := by
  rw [← Nat.factorization_le_iff_dvd hn (Nat.mul_ne_zero two_ne_zero (L_ne_zero t)), Finsupp.le_iff]
  simp only [Nat.support_factorization, normHeight, max_le_iff, Finset.sup_le_iff]
  constructor
  · intro h
    exact ⟨ht, fun p hp => (factorization_le_two_mul_L_iff hn (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp) ht).1 (h p hp)⟩
  · rintro ⟨-, h⟩ p hp
    exact (factorization_le_two_mul_L_iff hn (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp) ht).2 (h p hp)

/-- Monotonicity of the `2 L`-lattice in the height parameter. -/
lemma dvd_two_L_mono {n a b : ℕ} (hab : a ≤ b) (h : n ∣ 2 * L a) : n ∣ 2 * L b :=
  h.trans (mul_dvd_mul_left 2 (L_dvd_L hab))

/-! ## The factor of two is essential -/

lemma L_sixteen_factorization_two : (L 16).factorization 2 = 4 := by
  have h1 : (2 : ℕ) ^ 4 ∣ L 16 := (prime_pow_dvd_L_iff Nat.prime_two (by norm_num)).2 (by norm_num)
  have h2 : ¬ ((2 : ℕ) ^ 5 ∣ L 16) := by
    intro h
    have := (prime_pow_dvd_L_iff Nat.prime_two (by norm_num)).1 h
    norm_num at this
  have h1' := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (L_ne_zero 16)).1 h1
  have h2' : ¬ (5 ≤ (L 16).factorization 2) := fun h =>
    h2 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (L_ne_zero 16)).2 h)
  omega

/-- **The factor `2` is essential.**  `32 = 2 ^ 5` has normalized height `16` and divides
`2 * L 16`, but it does not divide `L 16`. -/
theorem two_factor_essential : (32 : ℕ) ∣ 2 * L 16 ∧ ¬ ((32 : ℕ) ∣ L 16) := by
  constructor
  · have h16 : (16 : ℕ) ∣ L 16 := dvd_L (by norm_num) (by norm_num)
    have : (2 : ℕ) * 16 ∣ 2 * L 16 := mul_dvd_mul_left 2 h16
    simpa using this
  · intro h
    have : (2 : ℕ) ^ 5 ∣ L 16 := by norm_num at h ⊢; exact h
    have := (prime_pow_dvd_L_iff Nat.prime_two (by norm_num)).1 this
    norm_num at this

/-- **The un-doubled statement is false.**  There is no valid variant of the main theorem with
`n ∣ L t` in place of `n ∣ 2 * L t`. -/
theorem normalizedHeight_not_le_iff_dvd_lcm :
    ¬ (∀ n t : ℕ, n ≠ 0 → 1 ≤ t → (n ∣ L t ↔ normHeight n ≤ t)) := by
  intro h
  have hmain := (normalizedHeight_le_iff_dvd_two_lcm (n := 32) (t := 16) (by norm_num)
    (by norm_num)).1 two_factor_essential.1
  exact two_factor_essential.2 ((h 32 16 (by norm_num) (by norm_num)).2 hmain)

end AnchoredV4
end Erdos287
