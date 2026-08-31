import Mathlib
import RequestProject.CurrentProgramme.LevelPairReciprocalNormalForm

/-!
# Fixed-`n` prime assignment core, and the non-multiplicativity firewall — §§7–8

**Exact finite combinatorics only.**

§7.  For squarefree `n`, a unitary divisor split `n = r · (n/r)` is exactly a **two-state
choice for each prime `p ∣ n`**: put `p` into `r` or into `n/r`.  Banked:

* `unitary_split_injOn`, `unitary_split_image` — the map `t ↦ ∏_{p ∈ t} p` is a bijection from
  the powerset of `n.primeFactors` onto `n.divisors`;
* `fixed_n_two_state_product` — the fixed-`n` two-state factorisation

  ```
  ∑_{r ∣ n} (∏_{p ∣ r} L_{p,1}) (∏_{p ∣ n/r} L_{p,2}) = ∏_{p ∣ n} (L_{p,1} + L_{p,2}).
  ```

  **This is only a fixed-`n` factorisation.**  Nothing here says the resulting coefficient is
  multiplicative in `n`, and no such statement is made anywhere in this delta.

§8.  Non-multiplicativity firewall.  The research local factors involve `inverse(n/p) mod p`,
so the local weight at `p` depends on `n` and not on `p` alone.  We bank **one explicit finite
counterexample** for the model coefficient

```
K(n) = ∏_{p ∣ n} ((n/p)⁻¹ mod p),
```

namely `K(15) = 4 ≠ 1 = K(3)·K(5)`, via `localFactorK_not_multiplicative`.  No universal
negation is asserted.

Research metadata (not a Lean statement):
`SINGLE-μ(n) ZERO-FREE EULER ROUTE : NONCLOSING / NO EULER DICTIONARY.`
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators

namespace Erdos287
namespace LevelPairPrimeAssignment

/-! ## §7.1  Unitary splits are two-state prime assignments -/

/-- Distinct sets of primes have distinct products, on the powerset of `n.primeFactors`. -/
theorem unitary_split_injOn (n : ℕ) :
    Set.InjOn (fun t : Finset ℕ => ∏ p ∈ t, p) ↑n.primeFactors.powerset := by
  intro t ht t' ht' h
  have hpt : ∀ p ∈ t, Nat.Prime p := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_powerset.1 (by simpa using ht) hp)
  have hpt' : ∀ p ∈ t', Nat.Prime p := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_powerset.1 (by simpa using ht') hp)
  have h1 := Nat.primeFactors_prod hpt
  have h2 := Nat.primeFactors_prod hpt'
  rw [← h1, ← h2]
  exact congrArg Nat.primeFactors h
/-- **Two-state assignment, set form.**  `LEAN_PROVED`.

For squarefree `n`, the prime-subset products are exactly the divisors of `n`: choosing, for
each `p ∣ n`, whether `p` goes to `r` or to `n/r` enumerates the unitary divisor splits. -/
theorem unitary_split_image {n : ℕ} (hn : Squarefree n) :
    n.primeFactors.powerset.image (fun t => ∏ p ∈ t, p) = n.divisors := by
  have hn0 : n ≠ 0 := hn.ne_zero
  ext r
  simp only [Finset.mem_image, Finset.mem_powerset, Nat.mem_divisors]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨?_, hn0⟩
    calc ∏ p ∈ t, p ∣ ∏ p ∈ n.primeFactors, p := Finset.prod_dvd_prod_of_subset _ _ _ ht
      _ = n := Nat.prod_primeFactors_of_squarefree hn
  · rintro ⟨hdvd, -⟩
    exact ⟨r.primeFactors, Nat.primeFactors_mono hdvd hn0,
      Nat.prod_primeFactors_of_squarefree (hn.squarefree_of_dvd hdvd)⟩

/-! ## §7.2  The fixed-`n` two-state product -/

/-- **`DET1-LEVELPAIR-PRIMEASSIGNMENT45`.**  `LEAN_PROVED` (fixed-`n` two-state pass).

For squarefree `n` and arbitrary local state weights `L₁, L₂`,

```
∑_{r ∣ n} (∏_{p ∣ r} L₁(p)) · (∏_{p ∣ n/r} L₂(p)) = ∏_{p ∣ n} (L₁(p) + L₂(p)).
```

**Fixed `n` only.**  This is a factorisation of the `n`-th coefficient over the primes of `n`;
it does *not* assert multiplicativity of the coefficient as a function of `n`. -/
theorem fixed_n_two_state_product {R : Type*} [CommRing R] {n : ℕ} (hn : Squarefree n)
    (L1 L2 : ℕ → R) :
    ∑ r ∈ n.divisors, (∏ p ∈ r.primeFactors, L1 p) * (∏ p ∈ (n / r).primeFactors, L2 p)
      = ∏ p ∈ n.primeFactors, (L1 p + L2 p) := by
  have hn0 : n ≠ 0 := hn.ne_zero
  rw [Finset.prod_add]
  refine Finset.sum_nbij' (i := fun r => r.primeFactors) (j := fun t => ∏ p ∈ t, p) ?_ ?_ ?_ ?_ ?_
  · intro r hr
    rw [Nat.mem_divisors] at hr
    exact Finset.mem_powerset.2 (Nat.primeFactors_mono hr.1 hn0)
  · intro t ht
    rw [Finset.mem_powerset] at ht
    rw [Nat.mem_divisors]
    refine ⟨?_, hn0⟩
    calc ∏ p ∈ t, p ∣ ∏ p ∈ n.primeFactors, p := Finset.prod_dvd_prod_of_subset _ _ _ ht
      _ = n := Nat.prod_primeFactors_of_squarefree hn
  · intro r hr
    rw [Nat.mem_divisors] at hr
    exact Nat.prod_primeFactors_of_squarefree (hn.squarefree_of_dvd hr.1)
  · intro t ht
    rw [Finset.mem_powerset] at ht
    exact Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors (ht hp))
  · intro r hr
    rw [Nat.mem_divisors] at hr
    congr 1
    have hdiv : n / r = ∏ p ∈ n.primeFactors \ r.primeFactors, p := by
      rw [Nat.prod_primeFactors_sdiff_of_squarefree hn (Nat.primeFactors_mono hr.1 hn0),
        Nat.prod_primeFactors_of_squarefree (hn.squarefree_of_dvd hr.1)]
    rw [hdiv, Nat.primeFactors_prod]
    intro p hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.1 hp).1

/-! ## §8  Non-multiplicativity firewall — one explicit finite counterexample -/

/-- The model local factor of the research source: `inverse(n/p) mod p`, as an integer.  Its
value depends on `n`, not on `p` alone. -/
def localFactorK (n p : ℕ) : ℤ := (((n / p : ℕ) : ZMod p)⁻¹).val

/-- The model fixed-`n` coefficient `K(n) = ∏_{p ∣ n} inverse(n/p) mod p`. -/
def coeffK (n : ℕ) : ℤ := ∏ p ∈ n.primeFactors, localFactorK n p

private theorem primeFactors_fifteen : (15 : ℕ).primeFactors = {3, 5} := by
  simp [Nat.primeFactors]

private theorem primeFactors_three : (3 : ℕ).primeFactors = {3} := by simp [Nat.primeFactors]

private theorem primeFactors_five : (5 : ℕ).primeFactors = {5} := by simp [Nat.primeFactors]

/-- **`localFactorK_not_multiplicative`.**  `LEAN_PROVED`.

An explicit finite counterexample: for the coprime squarefree pair `n₁ = 3`, `n₂ = 5`,

```
K(15) = 4 ≠ 1 = K(3)·K(5).
```

Hence the research local factors — which contain `inverse(n/p) mod p` — admit **no** Euler
dictionary in `n`; ordinary multiplicativity is unavailable.  Only this single explicit
counterexample is claimed; no universal negation is formalised. -/
theorem localFactorK_not_multiplicative :
    coeffK 15 = 4 ∧ coeffK 3 = 1 ∧ coeffK 5 = 1 ∧ coeffK 15 ≠ coeffK 3 * coeffK 5 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [coeffK, primeFactors_fifteen, primeFactors_three, primeFactors_five, localFactorK] <;>
    decide

end LevelPairPrimeAssignment
end Erdos287
