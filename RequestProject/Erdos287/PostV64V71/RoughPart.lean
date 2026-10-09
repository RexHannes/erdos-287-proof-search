import RequestProject.Erdos287.PostV64V71.DeterminantBox

/-!
# Erdős #287 — V70 all-multiple neighbour LCM and its rough part

**Status: BANK (LEAN PROVED).**

For an exception set `E` (`y = ⌊M/H⌋`):

* `goodMultiples M H E = {kq : 1 ≤ k ≤ H, y < q ≤ M prime, q ∉ E, M/2 < kq < 3M/4}`;
* `neighbourSet M H E = {kq - 1, kq + 1 : kq ∈ goodMultiples}`;
* `LambdaX M H E = lcm(neighbourSet)` (`Λ_x(M, E)`);
* `roughPrimes`, `roughPart` — the prime factors `r > y` of `Λ_x` and `R_x = ∏ r^{v_r(Λ_x)}`.

Results:

* `factorization_lcm_le` — `v_p(lcm s) ≤ m` if `v_p(n) ≤ m` for all `n ∈ s` (nonzero);
* `roughPrimes_subset_exceptional` — for the actual `E = E_H(M)` of a hypothetical
  counterexample, every rough prime factor of `Λ_x` lies in `E_H` (it divides a *selected*
  forced neighbour, so it cannot be good);
* `roughPart_dvd_Xi` — **`R_x(M, E_H) ∣ Ξ_H`** (assuming `M < (y+1)²`, so `v_r(Λ_x) ≤ 1`);
* `log_roughPart_lt` — conditionally on `log Ξ_H < B`, `log R_x < B`.
-/

open scoped BigOperators

namespace Erdos287.PostV64V71

open Erdos287

/-- Good multiples `kq` (relative to `E`) in the V70 window `M/2 < kq < 3M/4`. -/
def goodMultiples (M H : ℕ) (E : Finset ℕ) : Finset ℕ :=
  ((Finset.Icc 1 H ×ˢ Finset.Ioc (M / H) M).filter
    (fun p => p.2.Prime ∧ p.2 ∉ E ∧ M < 2 * (p.1 * p.2) ∧ 4 * (p.1 * p.2) < 3 * M)).image
    (fun p => p.1 * p.2)

/-- The forced-neighbour set `{kq ± 1}`. -/
def neighbourSet (M H : ℕ) (E : Finset ℕ) : Finset ℕ :=
  (goodMultiples M H E).image (· - 1) ∪ (goodMultiples M H E).image (· + 1)

/-- `Λ_x(M, E) = lcm{kq ± 1}`. -/
def LambdaX (M H : ℕ) (E : Finset ℕ) : ℕ := (neighbourSet M H E).lcm id

/-- The rough primes `r > ⌊M/H⌋` dividing `Λ_x`. -/
def roughPrimes (M H : ℕ) (E : Finset ℕ) : Finset ℕ :=
  (LambdaX M H E).primeFactors.filter (M / H < ·)

/-- The rough part `R_x = ∏_{r ∈ roughPrimes} r^{v_r(Λ_x)}`. -/
def roughPart (M H : ℕ) (E : Finset ℕ) : ℕ :=
  ∏ r ∈ roughPrimes M H E, r ^ (LambdaX M H E).factorization r

theorem mem_goodMultiples {M H : ℕ} {E : Finset ℕ} {n : ℕ} :
    n ∈ goodMultiples M H E ↔ ∃ k q, (1 ≤ k ∧ k ≤ H) ∧ (M / H < q ∧ q ≤ M) ∧ q.Prime ∧ q ∉ E ∧
      M < 2 * (k * q) ∧ 4 * (k * q) < 3 * M ∧ k * q = n := by
  simp only [goodMultiples, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc, Finset.mem_Ioc, Prod.exists]
  constructor
  · rintro ⟨k, q, ⟨⟨hk, hq⟩, hp, hE, h1, h2⟩, rfl⟩; exact ⟨k, q, hk, hq, hp, hE, h1, h2, rfl⟩
  · rintro ⟨k, q, hk, hq, hp, hE, h1, h2, rfl⟩; exact ⟨k, q, ⟨⟨hk, hq⟩, hp, hE, h1, h2⟩, rfl⟩

/-- `v_p(lcm s) ≤ m` whenever every (nonzero) `n ∈ s` has `v_p(n) ≤ m`. -/
theorem factorization_lcm_le (s : Finset ℕ) (p m : ℕ) (h0 : ∀ n ∈ s, n ≠ 0)
    (h : ∀ n ∈ s, n.factorization p ≤ m) : (s.lcm id).factorization p ≤ m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.lcm_insert]
    have ha0 : a ≠ 0 := h0 a (Finset.mem_insert_self a s)
    have hs0 : s.lcm id ≠ 0 := by
      rw [Ne, Finset.lcm_eq_zero_iff]
      intro hz
      exact h0 0 (Finset.mem_insert_of_mem (by simpa using hz)) rfl
    have := Nat.factorization_lcm ha0 hs0
    show (Nat.lcm a (s.lcm id)).factorization p ≤ m
    rw [this, Finsupp.sup_apply]
    exact sup_le (h a (Finset.mem_insert_self a s))
      (ih (fun n hn => h0 n (Finset.mem_insert_of_mem hn))
        (fun n hn => h n (Finset.mem_insert_of_mem hn)))

theorem neighbourSet_pos {M H : ℕ} {E : Finset ℕ} {n : ℕ} (hn : n ∈ neighbourSet M H E) :
    n ≠ 0 := by
  simp only [neighbourSet, Finset.mem_union, Finset.mem_image] at hn
  rcases hn with ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩
  · obtain ⟨k, q, -, -, -, -, h1, h2, rfl⟩ := mem_goodMultiples.1 hm
    omega
  · omega

namespace Gap2CE

variable (ce : Erdos287.Gap2CE)

/-- Every forced neighbour (relative to `E_H`) is a selected denominator. -/
theorem neighbourSet_subset_A (hM : 4 ≤ ce.M) {H : ℕ} (hH : 0 < H) :
    neighbourSet ce.M H (exceptionalPrimes ce.M H) ⊆ ce.A := by
  intro n hn
  simp only [neighbourSet, Finset.mem_union, Finset.mem_image] at hn
  have key : ∀ m ∈ goodMultiples ce.M H (exceptionalPrimes ce.M H), m - 1 ∈ ce.A ∧ m + 1 ∈ ce.A := by
    intro m hm
    obtain ⟨k, q, -, hq, hp, hE, h1, h2, rfl⟩ := mem_goodMultiples.1 hm
    have hXi : ¬ q ∣ Xi H := fun h => hE (mem_exceptionalPrimes.2 ⟨hq, hp, h⟩)
    exact forced_neighbours_selected ce hM hp (lt_mul_of_div_lt hH hq.1) hXi h1 h2
  rcases hn with ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩
  · exact (key m hm).1
  · exact (key m hm).2

/-- **Rough primes of `Λ_x(M, E_H)` are exceptional.** -/
theorem roughPrimes_subset_exceptional (hM : 4 ≤ ce.M) {H : ℕ} (hH : 0 < H) :
    roughPrimes ce.M H (exceptionalPrimes ce.M H) ⊆ exceptionalPrimes ce.M H := by
  intro r hr
  simp only [roughPrimes, Finset.mem_filter, Nat.mem_primeFactors] at hr
  obtain ⟨⟨hrp, hrdvd, -⟩, hry⟩ := hr
  -- `r` divides some neighbour `n`
  obtain ⟨n, hn, hrn⟩ : ∃ n ∈ neighbourSet ce.M H (exceptionalPrimes ce.M H), r ∣ n := by
    by_contra hc
    push_neg at hc
    have := factorization_lcm_le _ r 0 (fun n hn => neighbourSet_pos hn)
      (fun n hn => (Nat.factorization_eq_zero_of_not_dvd (hc n hn)).le)
    have h1 := (hrp.dvd_iff_one_le_factorization (by
      intro h0; unfold LambdaX at h0; rw [Finset.lcm_eq_zero_iff] at h0
      obtain ⟨x, hx, hx0⟩ := h0
      exact neighbourSet_pos hx hx0)).1 hrdvd
    unfold LambdaX at h1
    omega
  have hnA := neighbourSet_subset_A ce hM hH hn
  have hnM : n ≤ ce.M := le_M ce hnA
  have hrM : r ≤ ce.M := le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero (neighbourSet_pos hn)) hrn) hnM
  have hrXi : r ∣ Xi H := by
    by_contra hc
    exact all_good_multiples_omitted ce hrp (lt_mul_of_div_lt hH hry) hc hrn hnA
  exact mem_exceptionalPrimes.2 ⟨⟨hry, hrM⟩, hrp, hrXi⟩

/-- **`R_x(M, E_H) ∣ Ξ_H`** for a hypothetical counterexample (`M ≥ 4`, `H ≥ 1`,
`M < (⌊M/H⌋+1)²`). -/
theorem roughPart_dvd_Xi (hM : 4 ≤ ce.M) {H : ℕ} (hH : 0 < H)
    (hy : ce.M < (ce.M / H + 1) ^ 2) :
    roughPart ce.M H (exceptionalPrimes ce.M H) ∣ Xi H := by
  set E := exceptionalPrimes ce.M H
  have hsub := roughPrimes_subset_exceptional ce hM hH
  -- exponents are `≤ 1`
  have hexp : ∀ r ∈ roughPrimes ce.M H E, (LambdaX ce.M H E).factorization r ≤ 1 := by
    intro r hr
    have hr' := Finset.mem_filter.1 hr
    have hrp : r.Prime := (Nat.mem_primeFactors.1 hr'.1).1
    refine factorization_lcm_le _ r 1 (fun n hn => neighbourSet_pos hn) fun n hn => ?_
    by_contra hc
    push_neg at hc
    have h2 : r ^ 2 ∣ n :=
      (hrp.pow_dvd_iff_le_factorization (neighbourSet_pos hn)).2 hc
    have hnA := neighbourSet_subset_A ce hM hH hn
    have hnM : n ≤ ce.M := le_M ce hnA
    have hle : r ^ 2 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero (neighbourSet_pos hn)) h2
    have : (ce.M / H + 1) ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hr'.2 2
    omega
  calc roughPart ce.M H E ∣ ∏ r ∈ roughPrimes ce.M H E, r := by
        unfold roughPart
        exact Finset.prod_dvd_prod_of_dvd _ _ fun r hr =>
          (pow_dvd_pow r (hexp r hr)).trans (by rw [pow_one])
    _ ∣ ∏ r ∈ E, r := Finset.prod_dvd_prod_of_subset _ _ _ hsub
    _ ∣ Xi H := prod_exceptionalPrimes_dvd_Xi _ _

/-- Conditionally on `log Ξ_H < B`: `log R_x(M, E_H) < B`. -/
theorem log_roughPart_lt (hM : 4 ≤ ce.M) {H : ℕ} (hH : 0 < H)
    (hy : ce.M < (ce.M / H + 1) ^ 2) {B : ℝ} (hXi : Real.log (Xi H) < B) :
    Real.log (roughPart ce.M H (exceptionalPrimes ce.M H)) < B := by
  refine lt_of_le_of_lt ?_ hXi
  have hd := roughPart_dvd_Xi ce hM hH hy
  have hpos : 0 < roughPart ce.M H (exceptionalPrimes ce.M H) :=
    Nat.pos_of_dvd_of_pos hd (Xi_pos H)
  apply Real.log_le_log (by exact_mod_cast hpos)
  exact_mod_cast Nat.le_of_dvd (Xi_pos H) hd

end Gap2CE

end Erdos287.PostV64V71
