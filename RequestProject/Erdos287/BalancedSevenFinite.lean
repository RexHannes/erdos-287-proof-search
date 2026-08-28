import Mathlib
import RequestProject.Erdos287.FixedCertificateOrderCounterguard

/-!
# V15, Parts 6, 7 and 9 — the balanced-seven finite ledger

## Part 6 — the fixed-certificate binomial coefficient

`balancedSeven_lowSum_eq_neg20` is the exact binomial identity

`∑_{j=0}^{3} (−1)^j C(7,j) = −20`,

derived from the banked general identity
`Erdos287.Counterguard.alternating_partial_binomial`
(`∑_{j≤r} (−1)^j C(k,j) = (−1)^r C(k−1,r)`, `k ≥ 1`), which is re-exported here as
`balancedSeven_alternating_partial_binomial`.

**This is a binomial/source-algebra fact only.**  It is *not* asserted that
`H(n) = −20` for any physical Ford source: the source bridge is not formalised in this
repository, so `BALANCED7_PHYSICAL_SOURCE` is **not** claimed.

Status: `BALANCED7_CERTIFICATE_BINOMIAL : PROVED_FINITE`.

## Part 7 — the repeated-prime finite router

`repeatedPrime_image_card_le_six`: for seven labelled slots, imposing at least one
coincidence `p_i = p_j` (`i ≠ j`) leaves at most six distinct label values.  This is a
finite combinatorial support statement, together with the rational exponent inequality
`6/7 < 1` (`repeatedPrime_exponent_lt_one`).

**No analytic prime-count theorem, and in particular no `O(X^{6/7+o(1)})` estimate, is
claimed.**  Negligibility does not follow from `6/7 < 1` alone.

Status: `BALANCED7-REPEATED-PRIME45 : FINITE/EXPONENT CORE PROVED`.

## Part 9 — the squarefree multiplicative encoding, finite interface only

`SquarefreeEncoding a` bundles a genuine Mathlib `ArithmeticFunction` that is
multiplicative, takes the supplied value `a p` at primes, and vanishes at prime powers of
exponent `≥ 2`.  The only theorems are the finite evaluation identities
`SquarefreeEncoding.map_prod_primes` / `map_prod_seven_primes` under pairwise coprimality,
and `SquarefreeEncoding.moebius` witnesses that the interface is inhabited (so nothing
downstream is vacuous).

**No analytic class-`C` theorem, Bombieri–Vinogradov, DGS, Pascadi statement, or exponent
of distribution is claimed anywhere.**
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ArithmeticFunction
open scoped BigOperators

namespace Erdos287
namespace BalancedSeven

/-! ## Part 6 — the balanced-seven binomial certificate -/

/-- The banked general alternating partial binomial identity, re-exported. -/
theorem balancedSeven_alternating_partial_binomial (k r : ℕ) (hk : 1 ≤ k) :
    ∑ j ∈ Finset.range (r + 1), (-1 : ℤ) ^ j * (Nat.choose k j) =
      (-1) ^ r * (Nat.choose (k - 1) r) :=
  Counterguard.alternating_partial_binomial k r hk

/-- **`balancedSeven_lowSum_eq_neg20`** — `PROVED_FINITE`.

`∑_{j=0}^{3} (−1)^j C(7,j) = −20`, from the general identity with `k = 7`, `r = 3`
(`(−1)^3 C(6,3) = −20`).  A binomial fact only: no physical Ford source is instantiated. -/
theorem balancedSeven_lowSum_eq_neg20 :
    ∑ j ∈ Finset.range 4, (-1 : ℤ) ^ j * (Nat.choose 7 j) = -20 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, balancedSeven_alternating_partial_binomial 7 3 (by norm_num)]
  decide

/-- The same number, in the banked balanced-cell notation. -/
theorem balancedSeven_lowSum_eq_counterguard :
    ∑ j ∈ Finset.range 4, (-1 : ℤ) ^ j * (Nat.choose 7 j)
      = Counterguard.balancedCellWeight 7 3 := by
  rw [Counterguard.balancedCellWeight_eq_sum]

/-! ## Part 7 — the repeated-prime finite router -/

/-- **`repeatedPrime_image_card_le_six`** — `PROVED_FINITE`.

Seven labelled slots with at least one imposed coincidence `p i = p j`, `i ≠ j`, take at
most six distinct values.  Purely combinatorial; nothing analytic is asserted. -/
theorem repeatedPrime_image_card_le_six (p : Fin 7 → ℕ) {i j : Fin 7} (hij : i ≠ j)
    (heq : p i = p j) :
    (Finset.image p Finset.univ).card ≤ 6 := by
  classical
  have hle : (Finset.image p Finset.univ).card ≤ (Finset.univ : Finset (Fin 7)).card :=
    Finset.card_image_le
  have hcard : (Finset.univ : Finset (Fin 7)).card = 7 := by simp
  rw [hcard] at hle
  by_contra hcon
  push_neg at hcon
  have heq7 : (Finset.image p Finset.univ).card = (Finset.univ : Finset (Fin 7)).card := by
    omega
  have hinj := Finset.injOn_of_card_image_eq heq7
  exact hij (hinj (by simp) (by simp) heq)

/-- The general form: any non-injective labelling of `Fin n` has at most `n − 1` values. -/
theorem repeatedLabel_image_card_lt (n : ℕ) (p : Fin n → ℕ) {i j : Fin n} (hij : i ≠ j)
    (heq : p i = p j) :
    (Finset.image p Finset.univ).card < n := by
  classical
  have hle : (Finset.image p Finset.univ).card ≤ (Finset.univ : Finset (Fin n)).card :=
    Finset.card_image_le
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  rw [hcard] at hle
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    have heqn : (Finset.image p Finset.univ).card = (Finset.univ : Finset (Fin n)).card := by
      rw [h, hcard]
    exact hij (Finset.injOn_of_card_image_eq heqn (by simp) (by simp) heq)

/-- The rational exponent inequality `6/7 < 1`.  **This alone gives no analytic bound.** -/
theorem repeatedPrime_exponent_lt_one : (6 : ℚ) / 7 < 1 := by norm_num

/-! ## Part 9 — the squarefree multiplicative encoding (finite interface) -/

/-- An abstract squarefree multiplicative encoding with prescribed prime values `a`:
a genuine multiplicative `ArithmeticFunction` whose prime values are `a p` and whose
prime-power values vanish from exponent `2` on. -/
structure SquarefreeEncoding (R : Type*) [CommRing R] (a : ℕ → R) where
  /-- The underlying arithmetic function. -/
  f : ArithmeticFunction R
  /-- It is multiplicative. -/
  isMul : f.IsMultiplicative
  /-- Its prime values are the prescribed ones. -/
  prime_val : ∀ p : ℕ, p.Prime → f p = a p
  /-- It vanishes at prime powers of exponent `≥ 2` (squarefree support). -/
  primePow_zero : ∀ p k : ℕ, p.Prime → 2 ≤ k → f (p ^ k) = 0

namespace SquarefreeEncoding

variable {R : Type*} [CommRing R] {a : ℕ → R}

/-- **Finite evaluation identity.**  On a pairwise-coprime family of primes the encoding is
the product of the prescribed prime values. -/
theorem map_prod_primes {ι : Type*} (E : SquarefreeEncoding R a) (s : Finset ι) (g : ι → ℕ)
    (hg : ∀ i ∈ s, (g i).Prime)
    (hcop : (s : Set ι).Pairwise (Function.onFun Nat.Coprime g)) :
    E.f (∏ i ∈ s, g i) = ∏ i ∈ s, a (g i) := by
  rw [E.isMul.map_prod g s hcop]
  exact Finset.prod_congr rfl fun i hi => E.prime_val (g i) (hg i hi)

/-- The seven-slot case actually used by the balanced-seven certificate. -/
theorem map_prod_seven_primes (E : SquarefreeEncoding R a) (g : Fin 7 → ℕ)
    (hg : ∀ i, (g i).Prime) (hne : ∀ i j, i ≠ j → g i ≠ g j) :
    E.f (∏ i, g i) = ∏ i, a (g i) := by
  refine E.map_prod_primes Finset.univ g (fun i _ => hg i) ?_
  intro i _ j _ hij
  exact (Nat.coprime_primes (hg i) (hg j)).2 (hne i j hij)

/-- The interface is inhabited: Mathlib's Möbius function is a squarefree multiplicative
encoding with all prime values `−1`. -/
def moebius : SquarefreeEncoding ℤ (fun _ => -1) where
  f := ArithmeticFunction.moebius
  isMul := ArithmeticFunction.isMultiplicative_moebius
  prime_val := fun _ hp => ArithmeticFunction.moebius_apply_prime hp
  primePow_zero := fun p k hp hk => by
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]

/-- Sanity check of the interface on the Möbius witness: `μ(p₁⋯p₇) = (−1)^7 = −1` for seven
distinct primes. -/
theorem moebius_seven_distinct_primes (g : Fin 7 → ℕ) (hg : ∀ i, (g i).Prime)
    (hne : ∀ i j, i ≠ j → g i ≠ g j) :
    ArithmeticFunction.moebius (∏ i, g i) = -1 := by
  have h := SquarefreeEncoding.moebius.map_prod_seven_primes g hg hne
  simpa using h

end SquarefreeEncoding

end BalancedSeven
end Erdos287
