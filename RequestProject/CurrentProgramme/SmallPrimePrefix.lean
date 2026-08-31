import Mathlib
import RequestProject.CurrentProgramme.SmallQ34LSCompiler

/-!
# CurrentProgramme (post-Balanced7 pass) §12–§15 — the small-prime-prefix Type-II packet

This module is **finite/arithmetic algebra only**.

* §12 — the small-prime cutoff `z₀ = X^{1/420}` (matching the hard `δ = 1/21` ledger of the
  Balanced7 repair, divided by the sieve parameter `20`), and the exact *smooth/rough*
  factorisation `n = d · m` with `P⁺(d) < z` and `P⁻(m) ≥ z`: existence
  (`smoothPart_mul_roughPart`, `smoothPart_smooth`, `roughPart_rough`) and **uniqueness**
  (`smoothRough_unique`).
* §13 — the firewall for the `Ω(d) ≥ 3` prefix: after removing a two-prime divisor from a
  `z`-smooth `d` with `Ω(d) ≥ 3`, the cofactor still carries a prime `< z`
  (`smoothPrefix_three_firewall`).  So the `Ω(d) ≥ 3` part cannot be discharged by a
  two-prime removal.
* §14 — the **truncated Möbius** function `M_y(n) = ∑_{e ∣ n, e ≤ y} μ(e)` and the exact
  obstruction `truncMoebius_not_prefix_factorisable`: `M_y(d·m)` is *not* a function of the
  smooth prefix `d` alone.  This is why the Type-II packet cannot be split naively.
* §15 — the literal residual sum `rGeThreePrefix` and its uninhabited analytic socket
  `ThreeSmallPrimePrefixTypeIIInput`
  (`287-K0-SP2-THREE-SMALLPRIME-PREFIX-TYPEII45`, `ANALYTIC_OPEN`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace PostBalanced7Pro

open ArithmeticFunction

/-! ## §12.1  The small-prime cutoff -/

/-- The small-prime cutoff `z₀ = X^{1/420}`. -/
noncomputable def zZero (X : ℝ) : ℝ := X ^ ((1 : ℝ) / 420)

/-- **`zZero_pos`.**  `LEAN_PROVED`. -/
theorem zZero_pos {X : ℝ} (hX : 0 < X) : 0 < zZero X := Real.rpow_pos_of_pos hX _

/-- **`zZero_pow`.**  `LEAN_PROVED`.  `z₀^420 = X`. -/
theorem zZero_pow {X : ℝ} (hX : 0 ≤ X) : zZero X ^ (420 : ℕ) = X := by
  rw [zZero, ← Real.rpow_natCast (X ^ ((1 : ℝ) / 420)) 420, ← Real.rpow_mul hX]
  norm_num

/-! ## §12.2  Smooth and rough parts -/

/-- `d` is `z`-smooth: every prime factor is below the cutoff. -/
def IsSmoothBelow (z d : ℕ) : Prop := ∀ p ∈ d.primeFactors, p < z

/-- `m` is `z`-rough: every prime factor is at least the cutoff. -/
def IsRoughAbove (z m : ℕ) : Prop := ∀ p ∈ m.primeFactors, z ≤ p

/-- The `z`-smooth part of `n`. -/
def smoothPart (z n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => p < z), p ^ n.factorization p

/-- The `z`-rough part of `n`. -/
def roughPart (z n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => ¬ p < z), p ^ n.factorization p

/-- A prime dividing a product of prime powers is one of the base primes. -/
private theorem prime_mem_of_dvd_prod_pow {S : Finset ℕ} (hS : ∀ q ∈ S, Nat.Prime q)
    {e : ℕ → ℕ} {p : ℕ} (hp : Nat.Prime p) (h : p ∣ ∏ q ∈ S, q ^ e q) : p ∈ S := by
  rw [Prime.dvd_finset_prod_iff hp.prime] at h
  obtain ⟨q, hq, hpq⟩ := h
  have hpd : p ∣ q := hp.prime.dvd_of_dvd_pow hpq
  rwa [(Nat.prime_dvd_prime_iff_eq hp (hS q hq)).mp hpd]

private theorem prod_pow_ne_zero {S : Finset ℕ} (hS : ∀ q ∈ S, Nat.Prime q) (e : ℕ → ℕ) :
    (∏ q ∈ S, q ^ e q) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun q hq => ?_
  exact pow_ne_zero _ (hS q hq).pos.ne'

/-- **`smoothPart_ne_zero`.**  `LEAN_PROVED`. -/
theorem smoothPart_ne_zero (z n : ℕ) : smoothPart z n ≠ 0 :=
  prod_pow_ne_zero (fun _ hq => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1) _

/-- **`roughPart_ne_zero`.**  `LEAN_PROVED`. -/
theorem roughPart_ne_zero (z n : ℕ) : roughPart z n ≠ 0 :=
  prod_pow_ne_zero (fun _ hq => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1) _

/-- **`smoothPart_mul_roughPart`.**  `LEAN_PROVED`.

Existence of the smooth/rough factorisation `n = d · m`. -/
theorem smoothPart_mul_roughPart {n : ℕ} (hn : n ≠ 0) (z : ℕ) :
    smoothPart z n * roughPart z n = n := by
  rw [smoothPart, roughPart, Finset.prod_filter_mul_prod_filter_not]
  have h := Nat.factorization_prod_pow_eq_self hn
  rwa [Finsupp.prod, Nat.support_factorization] at h

/-- **`smoothPart_smooth`.**  `LEAN_PROVED`. -/
theorem smoothPart_smooth (z n : ℕ) : IsSmoothBelow z (smoothPart z n) := by
  intro p hp
  have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hdvd : p ∣ smoothPart z n := Nat.dvd_of_mem_primeFactors hp
  have hmem : p ∈ n.primeFactors.filter (fun p => p < z) :=
    prime_mem_of_dvd_prod_pow
      (fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1) hpp hdvd
  exact (Finset.mem_filter.mp hmem).2

/-- **`roughPart_rough`.**  `LEAN_PROVED`. -/
theorem roughPart_rough (z n : ℕ) : IsRoughAbove z (roughPart z n) := by
  intro p hp
  have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hdvd : p ∣ roughPart z n := Nat.dvd_of_mem_primeFactors hp
  have hmem : p ∈ n.primeFactors.filter (fun p => ¬ p < z) :=
    prime_mem_of_dvd_prod_pow
      (fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1) hpp hdvd
  exact not_lt.mp (Finset.mem_filter.mp hmem).2

/-- **`coprime_smooth_rough`.**  `LEAN_PROVED`.  A smooth number and a rough number share no
prime, hence are coprime. -/
theorem coprime_smooth_rough {z d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0)
    (hs : IsSmoothBelow z d) (hr : IsRoughAbove z m) : Nat.Coprime d m := by
  by_contra hc
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hc
  have hpd : p ∣ d := hpg.trans (Nat.gcd_dvd_left d m)
  have hpm : p ∣ m := hpg.trans (Nat.gcd_dvd_right d m)
  have h1 : p < z := hs p (Nat.mem_primeFactors.mpr ⟨hp, hpd, hd⟩)
  have h2 : z ≤ p := hr p (Nat.mem_primeFactors.mpr ⟨hp, hpm, hm⟩)
  omega

/-- **`smoothRough_unique`.**  `LEAN_PROVED`.

**Uniqueness of the small-prime-prefix decomposition.**  If `d₁ m₁ = d₂ m₂` with both `dᵢ`
`z`-smooth and both `mᵢ` `z`-rough (and all factors nonzero), then `d₁ = d₂` and `m₁ = m₂`. -/
theorem smoothRough_unique {z d₁ m₁ d₂ m₂ : ℕ}
    (hd₁ : d₁ ≠ 0) (hm₁ : m₁ ≠ 0) (hd₂ : d₂ ≠ 0) (hm₂ : m₂ ≠ 0)
    (hs₁ : IsSmoothBelow z d₁) (hr₁ : IsRoughAbove z m₁)
    (hs₂ : IsSmoothBelow z d₂) (hr₂ : IsRoughAbove z m₂)
    (heq : d₁ * m₁ = d₂ * m₂) : d₁ = d₂ ∧ m₁ = m₂ := by
  have h12 : d₁ ∣ d₂ := by
    have : d₁ ∣ d₂ * m₂ := ⟨m₁, heq.symm⟩
    exact (coprime_smooth_rough hd₁ hm₂ hs₁ hr₂).dvd_of_dvd_mul_right this
  have h21 : d₂ ∣ d₁ := by
    have : d₂ ∣ d₁ * m₁ := ⟨m₂, heq⟩
    exact (coprime_smooth_rough hd₂ hm₁ hs₂ hr₁).dvd_of_dvd_mul_right this
  have hd : d₁ = d₂ := Nat.dvd_antisymm h12 h21
  subst hd
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd₁) heq⟩

/-- **`smoothPart_dvd`.**  `LEAN_PROVED`. -/
theorem smoothPart_dvd {n : ℕ} (hn : n ≠ 0) (z : ℕ) : smoothPart z n ∣ n :=
  ⟨roughPart z n, (smoothPart_mul_roughPart hn z).symm⟩

/-! ## §13  The `Ω(d) ≥ 3` firewall -/

/-- The prefix has at most two prime factors (with multiplicity). -/
def PrefixAtMostTwo (z n : ℕ) : Prop := cardFactors (smoothPart z n) ≤ 2

/-- The prefix has at least three prime factors (with multiplicity). -/
def PrefixAtLeastThree (z n : ℕ) : Prop := 3 ≤ cardFactors (smoothPart z n)

/-- **`prefix_dichotomy`.**  `LEAN_PROVED`.  The two prefix classes are exhaustive and
mutually exclusive. -/
theorem prefix_dichotomy (z n : ℕ) :
    (PrefixAtMostTwo z n ∨ PrefixAtLeastThree z n) ∧
      ¬ (PrefixAtMostTwo z n ∧ PrefixAtLeastThree z n) := by
  unfold PrefixAtMostTwo PrefixAtLeastThree
  constructor
  · omega
  · rintro ⟨h1, h2⟩; omega

/-- **`smoothPrefix_three_firewall`.**  `LEAN_PROVED`.

Removing a two-prime divisor `e` from a `z`-smooth `d` with `Ω(d) ≥ 3` never exhausts the
small primes: the cofactor `f` still has a prime factor `< z`.  Hence the `Ω(d) ≥ 3` prefix
class is *not* reducible to a two-prime removal. -/
theorem smoothPrefix_three_firewall {z d e f : ℕ}
    (he : e ≠ 0) (hf : f ≠ 0) (hs : IsSmoothBelow z d)
    (hdef : d = e * f) (hΩ : 3 ≤ cardFactors d) (hΩe : cardFactors e = 2) :
    ∃ p, Nat.Prime p ∧ p < z ∧ p ∣ f := by
  have hd : d ≠ 0 := by simp [hdef, he, hf]
  have hsum : cardFactors d = cardFactors e + cardFactors f := by
    rw [hdef]; exact cardFactors_mul he hf
  have hfge : 1 ≤ cardFactors f := by omega
  have hfne : f ≠ 1 := by
    intro h; rw [h] at hfge; simp at hfge
  obtain ⟨p, hp, hpf⟩ := Nat.exists_prime_and_dvd hfne
  refine ⟨p, hp, ?_, hpf⟩
  have hpd : p ∣ d := hpf.trans ⟨e, by rw [hdef]; ring⟩
  exact hs p (Nat.mem_primeFactors.mpr ⟨hp, hpd, hd⟩)

/-! ## §14  The truncated Möbius obstruction -/

open Classical in
/-- The truncated Möbius function `M_y(n) = ∑_{e ∣ n, e ≤ y} μ(e)`. -/
noncomputable def truncMoebius (y : ℝ) (n : ℕ) : ℤ :=
  ∑ e ∈ n.divisors.filter (fun e : ℕ => (e : ℝ) ≤ y), (moebius e : ℤ)

/-- **`truncMoebius_two_two`.**  `LEAN_PROVED`.  `M_2(2) = μ(1) + μ(2) = 0`. -/
theorem truncMoebius_two_two : truncMoebius 2 2 = 0 := by
  have hd : (2 : ℕ).divisors = {1, 2} := by decide
  rw [truncMoebius, hd, Finset.sum_filter]
  rw [show ({1, 2} : Finset ℕ) = insert 1 {2} from rfl, Finset.sum_insert (by decide),
    Finset.sum_singleton]
  norm_num [moebius_apply_prime Nat.prime_two]

/-- **`truncMoebius_two_three`.**  `LEAN_PROVED`.  `M_2(3) = μ(1) = 1`. -/
theorem truncMoebius_two_three : truncMoebius 2 3 = 1 := by
  have hd : (3 : ℕ).divisors = {1, 3} := by decide
  rw [truncMoebius, hd, Finset.sum_filter]
  rw [show ({1, 3} : Finset ℕ) = insert 1 {3} from rfl, Finset.sum_insert (by decide),
    Finset.sum_singleton]
  norm_num

/-- **`truncMoebius_not_prefix_factorisable`.**  `LEAN_PROVED`.

The truncated Möbius weight of `d · m` is **not** a function of the smooth prefix `d` alone:
with `d = 1`, the values at `m = 2` and `m = 3` differ.  Consequently the Type-II packet does
not factor through the prefix, and the `Ω(d) ≥ 3` residual is genuinely a joint obligation. -/
theorem truncMoebius_not_prefix_factorisable :
    ¬ ∃ F : ℕ → ℤ, ∀ d m : ℕ, truncMoebius 2 (d * m) = F d := by
  rintro ⟨F, hF⟩
  have h2 := hF 1 2
  have h3 := hF 1 3
  rw [one_mul, truncMoebius_two_two] at h2
  rw [one_mul, truncMoebius_two_three] at h3
  omega

/-! ## §15  The residual Type-II sum and its socket -/

open Classical in
/-- The literal residual sum over the `Ω(d) ≥ 3` prefix class. -/
noncomputable def rGeThreePrefix (z X : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ (Finset.range X).filter (fun n => PrefixAtLeastThree z n), w n

/-- **`rGeThreePrefix_zero_weight`.**  `LEAN_PROVED`.  A sanity check on the literal
definition. -/
theorem rGeThreePrefix_zero_weight (z X : ℕ) : rGeThreePrefix z X (fun _ => 0) = 0 := by
  simp [rGeThreePrefix]

open Classical in
/-- **`rGeThreePrefix_split`.**  `LEAN_PROVED`.

The `Ω(d) ≥ 3` residual and the `Ω(d) ≤ 2` main term reassemble the full range sum: the
prefix split spends nothing twice. -/
theorem rGeThreePrefix_split (z X : ℕ) (w : ℕ → ℝ) :
    rGeThreePrefix z X w +
        ∑ n ∈ (Finset.range X).filter (fun n => ¬ PrefixAtLeastThree z n), w n =
      ∑ n ∈ Finset.range X, w n :=
  Finset.sum_filter_add_sum_filter_not _ _ _

/-- **`ThreeSmallPrimePrefixTypeIIInput`** —
`EXTERNAL / ANALYTIC / UNINHABITED`.  Label
`287-K0-SP2-THREE-SMALLPRIME-PREFIX-TYPEII45`, status `ANALYTIC_OPEN`.

The literal obligations of the outstanding Type-II estimate for the `Ω(d) ≥ 3`
small-prime-prefix class. -/
structure ThreeSmallPrimePrefixTypeIIInput
    (z X : ℕ) (w : ℕ → ℝ) (Xr eps : ℝ) : Prop where
  /-- The scale is nontrivial and the declared saving is genuine. -/
  scale : 3 ≤ Xr ∧ 0 < eps
  /-- The discrete range matches the analytic scale. -/
  range_matches : (X : ℝ) = Xr
  /-- The cutoff is the small-prime cutoff `z₀ = X^{1/420}`. -/
  cutoff_is_zZero : (z : ℝ) ≤ zZero Xr
  /-- The Type-II bound for the `Ω(d) ≥ 3` class. -/
  typeII_bound : |rGeThreePrefix z X w| ≤ eps * Xr / Real.log Xr

/-- **`threeSmallPrimePrefix_not_automatic`.**  `LEAN_PROVED`.

The socket is a genuine restriction and is not inhabited by the finite algebra above. -/
theorem threeSmallPrimePrefix_not_automatic :
    ∃ (z X : ℕ) (w : ℕ → ℝ) (Xr eps : ℝ), ¬ ThreeSmallPrimePrefixTypeIIInput z X w Xr eps := by
  refine ⟨0, 0, (fun _ => 0), 0, 0, ?_⟩
  intro h
  have h2 : (3 : ℝ) ≤ 0 := h.scale.1
  linarith

end PostBalanced7Pro
end Erdos287
