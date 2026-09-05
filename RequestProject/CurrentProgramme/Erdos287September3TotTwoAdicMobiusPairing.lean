import Mathlib

/-!
# Erdős #287 — September-3 bank, §B: the 2-adic Möbius source pairing

```
2-ADIC MÖBIUS PAIR COEFFICIENT      : KERNEL-PROVED
ODD-DIVISOR TOT SOURCE IDENTITY     : KERNEL-PROVED
TOT SOURCE SPLIT  T = T⁰ − T²       : KERNEL-PROVED
TERMWISE-TRIANGLE LOSS WITNESS      : KERNEL-PROVED
ANALYTIC PRIME DISTRIBUTION         : NOT ASSERTED ANYWHERE IN THIS FILE
```

This module is **append-only** and **independent of any analytic input**.  It contains no
prime-distribution statement, no Maynard/Bombieri–Vinogradov/Wright/Bordignon–Lee input,
and it does not bear on Erdős #287.

## What is formalised

For the physical `Tot` source, the small-prime Möbius prefix `m₁` occurs, on the physical
range, either as an odd `a` or as `2 * a` with the same odd `a`, and

    μ(2 * a) = − μ(a)          (`moebius_two_mul_odd`),

because `2` and an odd `a` are coprime.  The large-prime suffix `m₂` is odd on the intended
physical range, since its least prime factor exceeds `2` (`odd_of_all_prime_factors_gt_two`);
hence `d = a * m₂` is odd (`odd_mul_of_odd_odd`).

The *exact* paired coefficient identity — stated **before** any triangle inequality — is the
odd-divisor form

    ∑_{m ∣ n, m ≤ Y, 4 ∤ m} σ(m)
      = ∑_{d ∣ n, d odd} κ(d) · ( 1_{d ≤ Y} − 1_{2d ∣ n} · 1_{2d ≤ Y} )

(`oddDivisorTotSourceIdentity`), where the only properties of the source coefficient `σ`
that are used are the two **explicit** pairing hypotheses

    σ(d)   =   κ(d)      for odd `d`,
    σ(2d)  = − κ(d)      for odd `d`,

both of which are *verified* for the canonical Möbius coefficient
`sigmaEps`/`kappaEps` in `sigmaEps_odd` and `sigmaEps_two_mul_odd`.  Nothing load-bearing is
hidden inside an unconstrained structure: the pairing theorem takes these two equations as
hypotheses, and the canonical construction discharges them.

The cutoff `Y` is a *supplied* natural number (the abstract split datum standing for
`n ^ γ`); no real exponentiation, and in particular no analytic estimate, is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace September3TwoAdicPairing

/-! ## §B.1  The 2-adic Möbius pair coefficient -/

/-- **`moebius_two_mul_odd`.**  `KERNEL-PROVED`.  For odd `a`, `μ(2a) = −μ(a)`.
This is the exact sign relation that the source pairing consumes. -/
theorem moebius_two_mul_odd (a : ℕ) (ha : Odd a) :
    ArithmeticFunction.moebius (2 * a) = - ArithmeticFunction.moebius a := by
  have hcop : Nat.Coprime 2 a := Nat.coprime_two_left.mpr ha
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  ring

/-- **`odd_of_all_prime_factors_gt_two`.**  `KERNEL-PROVED`.  A positive integer all of whose
prime factors exceed `2` is odd.  This is the (elementary) reason the large-prime suffix
`m₂` is odd on the physical range. -/
theorem odd_of_all_prime_factors_gt_two (m : ℕ)
    (h : ∀ p : ℕ, p.Prime → p ∣ m → 2 < p) : Odd m := by
  rcases Nat.even_or_odd m with he | ho
  · exact absurd (h 2 Nat.prime_two he.two_dvd) (by omega)
  · exact ho

/-- **`odd_mul_of_odd_odd`.**  `KERNEL-PROVED`.  `d = a · m₂` is odd when both factors are. -/
theorem odd_mul_of_odd_odd {a m : ℕ} (ha : Odd a) (hm : Odd m) : Odd (a * m) := ha.mul hm

/-- The **canonical source coefficient** on odd moduli: the Möbius sign of the odd modulus
times the supplied physical weight of the split.  No analytic content: `w` is an arbitrary
supplied `ℤ`-valued weight. -/
def kappaEps (w : ℕ → ℤ) (d : ℕ) : ℤ := (ArithmeticFunction.moebius d : ℤ) * w d

/-- The **canonical unpaired source coefficient**.  On the physical 2-adic range
(`v₂(m) ≤ 1`) the map `m ↦ if Even m then m / 2 else m` returns the odd part of `m`, so
`sigmaEps w m` is `μ(m)` times the weight of the odd part — exactly the physical source
coefficient before pairing. -/
def sigmaEps (w : ℕ → ℤ) (m : ℕ) : ℤ :=
  (ArithmeticFunction.moebius m : ℤ) * w (if Even m then m / 2 else m)

/-- **`sigmaEps_odd`.**  `KERNEL-PROVED`.  First explicit pairing equation. -/
theorem sigmaEps_odd (w : ℕ → ℤ) (d : ℕ) (hd : Odd d) : sigmaEps w d = kappaEps w d := by
  simp [sigmaEps, kappaEps, Nat.not_even_iff_odd.mpr hd]

/-- **`twoAdicMobiusPairCoefficient`** (= `sigmaEps_two_mul_odd`).  `KERNEL-PROVED`.
Second explicit pairing equation: doubling an odd modulus flips the sign of the canonical
coefficient and keeps the weight, because `μ(2a) = −μ(a)` and the weight sees only the odd
part. -/
theorem twoAdicMobiusPairCoefficient (w : ℕ → ℤ) (d : ℕ) (hd : Odd d) :
    sigmaEps w (2 * d) = - kappaEps w d := by
  have h2 : Even (2 * d) := ⟨d, by ring⟩
  have hdiv : 2 * d / 2 = d := by omega
  simp only [sigmaEps, kappaEps, h2, if_pos, hdiv, moebius_two_mul_odd d hd]
  ring

/-! ## §B.2  The exact paired (odd-divisor) source identity -/

/-- **`oddDivisorTotSourceIdentity`.**  `KERNEL-PROVED`.

The exact paired coefficient identity, *before* any triangle inequality:

    ∑_{m ∣ n, m ≤ Y, 4 ∤ m} σ(m)
      = ∑_{d ∣ n, d odd} κ(d) · ( 1_{d ≤ Y} − 1_{2d ∣ n} · 1_{2d ≤ Y} ).

The only hypotheses are the two explicit pairing equations `h1`, `h2`; `Y` is the supplied
split datum standing for `n ^ γ`. -/
theorem oddDivisorTotSourceIdentity (n Y : ℕ) (kappa sigma : ℕ → ℤ)
    (h1 : ∀ d, Odd d → sigma d = kappa d)
    (h2 : ∀ d, Odd d → sigma (2 * d) = - kappa d) :
    ∑ m ∈ n.divisors.filter (fun m => m ≤ Y ∧ ¬ (4 ∣ m)), sigma m
      = ∑ d ∈ n.divisors.filter (fun d => Odd d),
          kappa d * ((if d ≤ Y then (1 : ℤ) else 0)
            - (if 2 * d ∣ n then (1 : ℤ) else 0) * (if 2 * d ≤ Y then (1 : ℤ) else 0)) := by
  classical
  set S := n.divisors.filter (fun m => m ≤ Y ∧ ¬ (4 ∣ m)) with hS
  set O := n.divisors.filter (fun d => Odd d) with hO
  set T := O.filter (fun d => 2 * d ∣ n ∧ 2 * d ≤ Y) with hT
  have hOodd : ∀ d ∈ O, Odd d := by
    intro d hd; exact (Finset.mem_filter.1 hd).2
  have hoddset : S.filter (fun m => Odd m) = O.filter (fun d => d ≤ Y) := by
    ext m
    simp only [hS, hO, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd, hle⟩, hodd⟩; exact ⟨⟨hd, hodd⟩, hle.1⟩
    · rintro ⟨⟨hd, hodd⟩, hle⟩
      refine ⟨⟨hd, hle, ?_⟩, hodd⟩
      intro h4
      rcases hodd with ⟨k, hk⟩
      omega
  have hevenset : S.filter (fun m => ¬ Odd m) = T.image (fun d => 2 * d) := by
    ext m
    simp only [hS, hO, hT, Finset.mem_filter, Finset.mem_image, Nat.mem_divisors,
      Nat.not_odd_iff_even]
    constructor
    · rintro ⟨⟨⟨hd, hn0⟩, hle, h4⟩, heven⟩
      obtain ⟨k, hk⟩ := heven
      refine ⟨k, ⟨⟨⟨?_, hn0⟩, ?_⟩, ?_, ?_⟩, by omega⟩
      · exact dvd_trans ⟨2, by omega⟩ hd
      · rcases Nat.even_or_odd k with hk2 | hk2
        · exact absurd (by obtain ⟨j, hj⟩ := hk2; exact ⟨j, by omega⟩ : (4 ∣ m)) h4
        · exact hk2
      · have hmk : 2 * k = m := by omega
        rw [hmk]; exact hd
      · omega
    · rintro ⟨k, ⟨⟨⟨hk, hn0⟩, hodd⟩, hdvd, hle⟩, rfl⟩
      refine ⟨⟨⟨hdvd, hn0⟩, hle, ?_⟩, ⟨k, by ring⟩⟩
      intro h4
      obtain ⟨j, hj⟩ := hodd
      omega
  have hsplit : ∑ m ∈ S, sigma m
      = (∑ m ∈ S.filter (fun m => Odd m), sigma m)
        + ∑ m ∈ S.filter (fun m => ¬ Odd m), sigma m :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hA : ∑ m ∈ S.filter (fun m => Odd m), sigma m
      = ∑ d ∈ O, (if d ≤ Y then kappa d else 0) := by
    rw [hoddset, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d hd => ?_
    by_cases h : d ≤ Y <;> simp [h, h1 d (hOodd d hd)]
  have hinj : Set.InjOn (fun d => 2 * d) (T : Set ℕ) := by
    intro a _ b _ h
    simp only at h
    omega
  have hB : ∑ m ∈ S.filter (fun m => ¬ Odd m), sigma m
      = ∑ d ∈ O, (if (2 * d ∣ n ∧ 2 * d ≤ Y) then - kappa d else 0) := by
    rw [hevenset, Finset.sum_image hinj, hT, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d hd => ?_
    by_cases h : (2 * d ∣ n ∧ 2 * d ≤ Y) <;> simp [h, h2 d (hOodd d hd)]
  rw [hsplit, hA, hB, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases h : d ≤ Y <;> by_cases h1' : 2 * d ∣ n <;> by_cases h2' : 2 * d ≤ Y <;>
    simp [h, h1', h2']

/-- **`oddDivisorTotSourceIdentity_filtered`.**  `KERNEL-PROVED`.  The same identity with the
two indicator factors absorbed into the index sets: the paired source is the family-`0` sum
minus the family-`2` sum. -/
theorem oddDivisorTotSourceIdentity_filtered (n Y : ℕ) (kappa sigma : ℕ → ℤ)
    (h1 : ∀ d, Odd d → sigma d = kappa d)
    (h2 : ∀ d, Odd d → sigma (2 * d) = - kappa d) :
    ∑ m ∈ n.divisors.filter (fun m => m ≤ Y ∧ ¬ (4 ∣ m)), sigma m
      = (∑ d ∈ n.divisors.filter (fun d => Odd d ∧ d ≤ Y), kappa d)
        - ∑ d ∈ n.divisors.filter (fun d => Odd d ∧ (2 * d ∣ n ∧ 2 * d ≤ Y)), kappa d := by
  classical
  have e1 : ∑ d ∈ n.divisors.filter (fun d => Odd d ∧ d ≤ Y), kappa d
      = ∑ d ∈ n.divisors.filter (fun d => Odd d), (if d ≤ Y then kappa d else 0) := by
    rw [← Finset.filter_filter, Finset.sum_filter]
  have e2 : ∑ d ∈ n.divisors.filter (fun d => Odd d ∧ (2 * d ∣ n ∧ 2 * d ≤ Y)), kappa d
      = ∑ d ∈ n.divisors.filter (fun d => Odd d),
          (if (2 * d ∣ n ∧ 2 * d ≤ Y) then kappa d else 0) := by
    rw [← Finset.filter_filter, Finset.sum_filter]
  rw [oddDivisorTotSourceIdentity n Y kappa sigma h1 h2, e1, e2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases h : d ≤ Y <;> by_cases h1' : 2 * d ∣ n <;> by_cases h2' : 2 * d ≤ Y <;>
    simp [h, h1', h2']

/-! ## §B.3  The Tot-lane split `T = T⁰ − T²` for supplied physical weights -/

/-- The physical `Tot` source over a supplied finite set of `n`'s, **before** pairing:
`σ` is the supplied unpaired coefficient, `Y n` the supplied split datum at `n`, and the
inner index set is the physical 2-adic range `v₂(m) ≤ 1`. -/
def totSource (N : Finset ℕ) (Y : ℕ → ℕ) (sigma : ℕ → ℕ → ℤ) : ℤ :=
  ∑ n ∈ N, ∑ m ∈ n.divisors.filter (fun m => m ≤ Y n ∧ ¬ (4 ∣ m)), sigma n m

/-- Family `0`: `d` odd, `n = d·r`, `d ≤ Y n`. -/
def totSourceFamily0 (N : Finset ℕ) (Y : ℕ → ℕ) (kappa : ℕ → ℕ → ℤ) : ℤ :=
  ∑ n ∈ N, ∑ d ∈ n.divisors.filter (fun d => Odd d ∧ d ≤ Y n), kappa n d

/-- Family `2`: `d` odd, `n = 2·d·u`, `2·d ≤ Y n`. -/
def totSourceFamily2 (N : Finset ℕ) (Y : ℕ → ℕ) (kappa : ℕ → ℕ → ℤ) : ℤ :=
  ∑ n ∈ N, ∑ d ∈ n.divisors.filter (fun d => Odd d ∧ (2 * d ∣ n ∧ 2 * d ≤ Y n)), kappa n d

/-- **`totLaneSourceSplit`.**  `KERNEL-PROVED`.  The exact algebraic split

    T = T⁰ − T²

for supplied physical weights.  No absolute values are taken anywhere in the identity. -/
theorem totLaneSourceSplit (N : Finset ℕ) (Y : ℕ → ℕ) (kappa sigma : ℕ → ℕ → ℤ)
    (h1 : ∀ n d, Odd d → sigma n d = kappa n d)
    (h2 : ∀ n d, Odd d → sigma n (2 * d) = - kappa n d) :
    totSource N Y sigma = totSourceFamily0 N Y kappa - totSourceFamily2 N Y kappa := by
  classical
  unfold totSource totSourceFamily0 totSourceFamily2
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  exact oddDivisorTotSourceIdentity_filtered n (Y n) (kappa n) (sigma n) (h1 n) (h2 n)

/-- **`termwise_triangle_loses_pairing`.**  `KERNEL-PROVED`.  A purely algebraic witness that
bounding the source term by term (triangle inequality *inside* the 2-adic pair) is strictly
lossy: there is an instance of the pairing hypotheses whose paired sum vanishes while the
sum of absolute values of the individual terms is `2`.  Equivalently: the `μ(a)/μ(2a)`
cancellation is destroyed by a termwise bound. -/
theorem termwise_triangle_loses_pairing :
    ∃ (n Y : ℕ) (kappa sigma : ℕ → ℤ),
      (∀ d, Odd d → sigma d = kappa d) ∧
      (∀ d, Odd d → sigma (2 * d) = - kappa d) ∧
      |∑ m ∈ n.divisors.filter (fun m => m ≤ Y ∧ ¬ (4 ∣ m)), sigma m|
        < ∑ m ∈ n.divisors.filter (fun m => m ≤ Y ∧ ¬ (4 ∣ m)), |sigma m| := by
  classical
  refine ⟨2, 2, fun _ => 1, fun m => if m % 2 = 0 then -1 else 1, ?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨k, hk⟩ := hd
    simp [hk]
  · intro d _
    simp [Nat.mul_mod_right]
  · decide

end September3TwoAdicPairing
end Erdos287
