import RequestProject.Extension

/-!
# Erdős Problem #287: no counterexample with maximum denominator at most `U2`

Erdős Problem #287 asks whether, for any distinct integers `1 < n₁ < ⋯ < n_k` with
`1 = 1/n₁ + ⋯ + 1/n_k`, one must have `max (n_{i+1} - n_i) ≥ 3`.  The problem is **open**.

This file proves the finite statements

`no_Erdos287Counterexample_of_max_le_1e60`:
  no counterexample has largest element `≤ 10 ^ 60`;

`no_Erdos287Counterexample_of_max_le_U2`:
  no counterexample has largest element `≤ 3739298103962937078961175187719640178760086558841160733818922`.

The proof has three ingredients.

1. The *window lemma* `Erdos287.no_dvd_of_window`: a `p`-adic valuation argument showing that a
   reciprocal representation of `1` with all parts `≤ M` cannot contain any multiple of a prime
   power `p ^ a` whose multiplier window `⌊M / p ^ a⌋` is short enough.
2. The *bridge* `Erdos287.not_counterexample_of_windowPairSupply`: if two consecutive integers
   `x`, `x + 1` are both forbidden in this sense and `x + 1 ≤ M ≤ 2 * x`, then no counterexample
   with maximum `M` exists (the gap-at-most-two hypothesis is violated at `x`).
3. A *certified chain of prime pairs* `(q_i, P_i = 2 * q_i - 1)`, both prime, with
   `P_i < P_{i+1} ≤ 2 * P_i` and `2 * P_{last} > 10 ^ 60`, plus a handful of hand-made window
   pairs and a finite check for `M ≤ 7`, covering the whole range `2 ≤ M ≤ 10 ^ 60`.

All primality facts above `10 ^ 7` are kernel-checked Lucas certificates
(`Erdos287.prime_of_cert`), built on `lucas_primality` from Mathlib; no `native_decide`,
no new axioms, no `sorry`.

The extension past the chain (`RequestProject/Extension.lean`) uses one further blocker pair
`x = 15 * Q`, `x + 1 = 16 * P` built from two Proth primes, forbidden through windows `40` and
`42` by factorial certificates, together with the harmonic bound of
`RequestProject/Harmonic.lean`.
-/

open scoped BigOperators

namespace Erdos287

/--
**No counterexample to Erdős Problem #287 has maximum denominator at most `10 ^ 60`.**

This is a *finite* statement; the full conjecture remains open.
-/
theorem no_Erdos287Counterexample_of_max_le_1e60
    {A : Finset ℕ}
    (h : Erdos287Counterexample A)
    (hM : A.max' h.nonempty ≤ 10 ^ 60) :
    False := by
  rcases le_or_gt (A.max' h.nonempty) 7 with hle | hgt
  · exact no_counterexample_le_seven h hle
  · exact not_counterexample_of_windowPairSupply h
      (windowPairSupply_of_le (by omega) hM)

/--
No counterexample to Erdős Problem #287 has maximum denominator at most `CHAIN_CEILING`, the top
of the certified prime-pair chain.
-/
theorem no_Erdos287Counterexample_of_max_le_chainCeiling
    {A : Finset ℕ}
    (h : Erdos287Counterexample A)
    (hM : A.max' h.nonempty ≤ CHAIN_CEILING) :
    False := by
  rw [CHAIN_CEILING] at hM
  rcases le_or_gt (A.max' h.nonempty) 7 with hle | hgt
  · exact no_counterexample_le_seven h hle
  · exact not_counterexample_of_windowPairSupply h
      (windowPairSupply_of_le_chainCeiling (by omega) hM)

/--
**No counterexample to Erdős Problem #287 has maximum denominator at most**

`U2 = 3739298103962937078961175187719640178760086558841160733818922`.

Below `CHAIN_CEILING` this is the certified prime-pair chain; above it, the single blocker pair
`x = 15 * Q`, `x + 1 = 16 * P` of `RequestProject/Extension.lean` together with the harmonic
bound.  This is a *finite* statement; the full conjecture remains open.
-/
theorem no_Erdos287Counterexample_of_max_le_U2
    {A : Finset ℕ}
    (h : Erdos287Counterexample A)
    (hM : A.max' h.nonempty ≤
      3739298103962937078961175187719640178760086558841160733818922) :
    False := by
  rcases le_or_gt (A.max' h.nonempty) CHAIN_CEILING with hle | hgt
  · exact no_Erdos287Counterexample_of_max_le_chainCeiling h hle
  · exact no_counterexample_of_chainCeiling_lt_max_le_U2 h hgt (by rw [U2]; exact hM)

end Erdos287

#print axioms Erdos287.no_Erdos287Counterexample_of_max_le_1e60

#print axioms Erdos287.no_Erdos287Counterexample_of_max_le_U2
