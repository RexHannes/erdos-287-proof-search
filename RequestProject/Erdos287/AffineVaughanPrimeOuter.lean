import Mathlib
import RequestProject.Erdos287.AffineVaughanIdentity
import RequestProject.Erdos287.FixedCertificateSmoothParity

/-!
# Prime / prime-power outer router, cofactor fold, and the support no-go (V14, Parts 5–8)

## Part 5 — the outer router

The outer variable `e` of the Type-II term ranges over the support of `Λ`.  That support
splits **exactly** into primes and proper prime powers: `vonMangoldt_outer_partition`
(exhaustive) and `not_isPrimeOuter_and_isProperPrimePowerOuter` (disjoint), together with
the two converse membership lemmas.  This is a finite/structural partition, not an
estimate.

The asymptotic bound `X^{5/6+o(1)}` for the proper-prime-power outer contribution is **not
proved here and not assumed**.  `primepower_exponent_five_sixths` is only the rational
exponent ledger `1 − (1/3)/2 = 5/6` attached to the scale `Vscale = X^{1/3}`, and
`PrimePowerOuterBound` is the smallest `CONDITIONAL_INTERFACE` carrying the actual
estimate.  It is never inhabited, and it is not an `axiom`: every theorem that needs it
takes it as an explicit hypothesis.

## Part 6 — the prime-outer source variables

`AffineVaughanPrimeCell` records only the *finite source data* `d p r m n` of a Type-II
term with `d > U`, `p` prime, `p > V` and `d p r = 2mn + s`.  It contains **no** analytic
field (hostile check 13).  Only elementary consequences are proved from it.

## Part 7 — the cofactor fold

`lambdaU U q = ∑_{d ∣ q, d > U} μ(d)`, and for `q > 1`

`lambdaU U q = − truncMobius q U`

(`lambdaU_eq_neg_truncMobius`), because `∑_{d ∣ q} μ(d) = 0`.  The cutoff conventions are
kept explicitly distinct: `lambdaU` filters `U < d`, the banked `truncMobius` filters
`d ≤ T`, and the identity is exactly the statement relating them at the *same* cutoff
value.  The hypothesis `1 < q` is genuinely used (hostile check 6).

## Part 8 — the support no-go

`prime_support_obstruction_to_balanced_convolution`: a Dirichlet convolution of two
coefficient sequences supported in `[1, Q₁]` and `[1, Q₂]` vanishes at any prime `ℓ`
exceeding both `Q₁` and `Q₂`, since the only factorisations of `ℓ` are `1·ℓ` and `ℓ·1`.
Combined with `lambdaU_prime = −1` this gives
`vaughan_cofactor_balanced_factorization_impossible`.

This is a **scoped** no-go: it refutes exactly the stated balanced-support factorisation
property, and makes no claim about any other definition of well-factorability appearing in
the literature (hostile check 7).

Ledger targets:
`AFFINE287-VAUGHAN-PRIMEPOWER : CONDITIONAL_INTERFACE`,
`VAUGHAN-COFACTOR-TRUNCMOBIUS-IDENTITY287 : PROVED_ALGEBRAIC`,
`VAUGHAN-COFACTOR-WELLFACTORABLE-NOGO : PROVED_FINITE / STRUCTURAL_NO_GO`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ArithmeticFunction
open scoped BigOperators

namespace Erdos287
namespace VaughanOuter

open Erdos287.Vaughan

/-! ## Part 5 — the prime / proper-prime-power partition of the `Λ`-support -/

/-- The outer variable is a prime. -/
def IsPrimeOuter (e : ℕ) : Prop := e.Prime

/-- The outer variable is a proper prime power `p^j`, `j ≥ 2`. -/
def IsProperPrimePowerOuter (e : ℕ) : Prop := ∃ p j : ℕ, p.Prime ∧ 2 ≤ j ∧ p ^ j = e

/-- **Exhaustiveness on the `Λ`-support.** -/
theorem vonMangoldt_outer_partition {e : ℕ} (he : vonMangoldt e ≠ 0) :
    IsPrimeOuter e ∨ IsProperPrimePowerOuter e := by
  have hpp : IsPrimePow e := ArithmeticFunction.vonMangoldt_ne_zero_iff.1 he
  obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff e).1 hpp
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have : k = 1 := by omega
    subst this
    rw [pow_one] at hpk
    subst hpk
    exact Or.inl hp
  · exact Or.inr ⟨p, k, hp, hk2, hpk⟩

/-- **Disjointness.**  A prime is not a proper prime power. -/
theorem not_isPrimeOuter_and_isProperPrimePowerOuter {e : ℕ} :
    ¬ (IsPrimeOuter e ∧ IsProperPrimePowerOuter e) := by
  rintro ⟨he, p, j, hp, hj, rfl⟩
  have hdvd : p ∣ p ^ j := dvd_pow_self p (by omega)
  have hpe : p = p ^ j := ((Nat.Prime.eq_one_or_self_of_dvd he p hdvd).resolve_left hp.ne_one)
  have h1 : p ^ 1 < p ^ j := Nat.pow_lt_pow_right hp.one_lt (by omega)
  rw [pow_one] at h1
  omega

/-- Primes lie in the `Λ`-support. -/
theorem vonMangoldt_ne_zero_of_isPrimeOuter {e : ℕ} (he : IsPrimeOuter e) :
    vonMangoldt e ≠ 0 :=
  ArithmeticFunction.vonMangoldt_ne_zero_iff.2 he.isPrimePow

/-- Proper prime powers lie in the `Λ`-support. -/
theorem vonMangoldt_ne_zero_of_isProperPrimePowerOuter {e : ℕ}
    (he : IsProperPrimePowerOuter e) : vonMangoldt e ≠ 0 := by
  obtain ⟨p, j, hp, hj, rfl⟩ := he
  exact ArithmeticFunction.vonMangoldt_ne_zero_iff.2 ⟨p, j, hp.prime, by omega, rfl⟩

/-- The partition is an exact characterisation of the `Λ`-support. -/
theorem vonMangoldt_support_iff {e : ℕ} :
    vonMangoldt e ≠ 0 ↔ IsPrimeOuter e ∨ IsProperPrimePowerOuter e :=
  ⟨vonMangoldt_outer_partition, fun h => h.elim vonMangoldt_ne_zero_of_isPrimeOuter
    vonMangoldt_ne_zero_of_isProperPrimePowerOuter⟩

/-! ### The exponent ledger for the proper-prime-power outer

Rational exponent arithmetic only: no `o(1)`, no asymptotics. -/

/-- **`primepower_exponent_five_sixths`** — with `Vscale = X^{1/3}`, the heuristic
prime-power bound `X · Vscale^{−1/2}` sits at exponent `5/6`. -/
theorem primepower_exponent_five_sixths {vExp : ℚ} (h : vExp = 1 / 3) :
    1 - vExp / 2 = 5 / 6 := by
  subst h; norm_num

/-- The exponent `5/6` has the explicit saving `1/6` below the trivial exponent `1`. -/
theorem primepower_exponent_saving : (1 : ℚ) - 5 / 6 = 1 / 6 := by norm_num

/-- **`PrimePowerOuterBound`** — `CONDITIONAL_INTERFACE / OPEN_ANALYTIC`.

The actual summatory estimate for the proper-prime-power outer contribution `S` at scale
`X`, at the exponent certified by `primepower_exponent_five_sixths`.  This structure is
**never inhabited** in this project; it exists so that downstream routers can carry the
estimate as an explicit hypothesis instead of assuming it. -/
structure PrimePowerOuterBound (X C S : ℝ) : Prop where
  /-- Asymptotic regime. -/
  X_gt_one : 1 < X
  /-- Nonnegative implied constant. -/
  C_nonneg : 0 ≤ C
  /-- **The open analytic estimate.** -/
  bound : |S| ≤ C * X ^ ((5 : ℝ) / 6)

/-- The interface delivers exactly what it says, and nothing more. -/
theorem primePowerOuter_le_of_bound {X C S : ℝ} (h : PrimePowerOuterBound X C S) :
    |S| ≤ C * X ^ ((5 : ℝ) / 6) := h.bound

/-! ## Part 6 — the prime-outer source cell -/

/-- **`AffineVaughanPrimeCell`** — the finite source data of one Type-II term with prime
outer variable: `d · p · r = 2mn + s`, `d > U`, `p` prime with `p > V`.

There is deliberately **no analytic field**: this records the factorisation only. -/
structure AffineVaughanPrimeCell (U V : ℕ) where
  /-- First affine variable. -/
  m : ℕ
  /-- Second affine variable. -/
  n : ℕ
  /-- Möbius (cofactor) variable. -/
  d : ℕ
  /-- Prime outer variable. -/
  p : ℕ
  /-- Remaining cofactor. -/
  r : ℕ
  /-- Which of the two shifts `±1` is in play. -/
  sign : Vaughan.AffineSign
  m_pos : 1 ≤ m
  n_pos : 1 ≤ n
  r_pos : 1 ≤ r
  hp : p.Prime
  hd : U < d
  hpLower : V < p
  equation : d * p * r = Vaughan.affineNat sign m n

namespace AffineVaughanPrimeCell

variable {U V : ℕ} (c : AffineVaughanPrimeCell U V)

/-- The affine value of the cell. -/
def value : ℕ := Vaughan.affineNat c.sign c.m c.n

theorem value_pos : 0 < c.value := Vaughan.affineNat_pos _ c.m_pos c.n_pos

theorem prime_dvd_value : c.p ∣ c.value := by
  refine ⟨c.d * c.r, ?_⟩
  have := c.equation
  rw [value, ← this]
  ring

theorem cofactor_dvd_value : c.d * c.r ∣ c.value := by
  refine ⟨c.p, ?_⟩
  have := c.equation
  rw [value, ← this]
  ring

theorem d_pos : 0 < c.d := by
  rcases Nat.eq_zero_or_pos c.d with h | h
  · exfalso
    have := c.equation
    rw [h] at this
    have hv := Vaughan.affineNat_pos c.sign c.m_pos c.n_pos
    omega
  · exact h

/-- The value is odd, hence so is the prime outer variable: `p ≠ 2`. -/
theorem p_ne_two : c.p ≠ 2 := by
  intro h
  refine Vaughan.affineNat_odd c.sign c.m_pos c.n_pos ?_
  have := c.prime_dvd_value
  rwa [h, value] at this

theorem p_odd : ¬ 2 ∣ c.p := by
  intro h
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two c.hp).1 h
  exact c.p_ne_two this.symm

/-- The prime outer variable is at least `3` (it is odd and prime). -/
theorem three_le_p : 3 ≤ c.p := by
  have h2 := c.hp.two_le
  have := c.p_ne_two
  omega

end AffineVaughanPrimeCell

/-! ## Part 7 — the cofactor fold `q = d r` and the truncated Möbius identity -/

/-- `lambdaU U q = ∑_{d ∣ q, d > U} μ(d)`. -/
def lambdaU (U q : ℕ) : ℤ :=
  ∑ d ∈ q.divisors.filter (fun d => U < d), moebius d

/-- **`lambdaU_eq_neg_truncMobius`** — `PROVED_ALGEBRAIC`.

For `q > 1` the high part of the Möbius divisor sum is minus the low part, at the *same*
cutoff `U`.  The two cutoff conventions (`U < d` for `lambdaU`, `d ≤ U` for the banked
`truncMobius`) are related here explicitly, not silently identified. -/
theorem lambdaU_eq_neg_truncMobius {q : ℕ} (hq : 1 < q) (U : ℕ) :
    lambdaU U q = -Erdos287.SmoothParity.truncMobius q U := by
  have hsplit :
      (∑ d ∈ q.divisors.filter (fun d => d ≤ U), moebius d)
        + (∑ d ∈ q.divisors.filter (fun d => ¬ d ≤ U), moebius d)
        = ∑ d ∈ q.divisors, moebius d :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hzero : (∑ d ∈ q.divisors, moebius d) = 0 :=
    Erdos287.SmoothParity.sum_moebius_divisors_eq_zero hq
  have hfil : q.divisors.filter (fun d => ¬ d ≤ U) = q.divisors.filter (fun d => U < d) := by
    apply Finset.filter_congr
    intro d _
    simp
  rw [hfil] at hsplit
  rw [lambdaU, Erdos287.SmoothParity.truncMobius]
  omega

/-- At a prime `ℓ > U` (with `U ≥ 1`) the high Möbius part equals `−1`. -/
theorem lambdaU_prime {l U : ℕ} (hl : l.Prime) (h1 : 1 ≤ U) (h2 : U < l) :
    lambdaU U l = -1 := by
  rw [lambdaU_eq_neg_truncMobius hl.one_lt U,
    Erdos287.SmoothParity.truncMobius_prime hl h1 h2]

/-! ## Part 8 — the balanced-support no-go -/

/-- Dirichlet convolution of two integer coefficient sequences, in divisor-sum form. -/
def dconv (a b : ℕ → ℤ) (n : ℕ) : ℤ := ∑ d ∈ n.divisors, a d * b (n / d)

/-- **`prime_support_obstruction_to_balanced_convolution`** — `PROVED_FINITE`.

If `a` is supported in `[1, Q₁]` and `b` in `[1, Q₂]`, then their Dirichlet convolution
vanishes at every prime `ℓ` larger than both `Q₁` and `Q₂`: the only factorisations of a
prime are `1 · ℓ` and `ℓ · 1`, and each puts a large argument outside a support. -/
theorem prime_support_obstruction_to_balanced_convolution
    {a b : ℕ → ℤ} {Q1 Q2 l : ℕ}
    (ha : ∀ n, Q1 < n → a n = 0) (hb : ∀ n, Q2 < n → b n = 0)
    (hl : l.Prime) (h1 : Q1 < l) (h2 : Q2 < l) :
    dconv a b l = 0 := by
  have hdiv : l.divisors = {1, l} := hl.divisors
  have hne : (1 : ℕ) ≠ l := (Nat.ne_of_lt hl.one_lt)
  rw [dconv, hdiv, Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
  have e1 : l / 1 = l := Nat.div_one l
  have e2 : l / l = 1 := Nat.div_self hl.pos
  rw [e1, e2, hb l h2, ha l h1]
  ring

/-- **`vaughan_cofactor_balanced_factorization_impossible`** — `PROVED_FINITE /
STRUCTURAL_NO_GO`.

The truncated cofactor coefficient `q ↦ lambdaU U q` cannot be written as a Dirichlet
convolution of two sequences supported below a prime `ℓ > U`: it takes the value `−1`
there, while every such convolution vanishes.

Scope: this refutes exactly the *balanced support* factorisation stated in the hypotheses.
It is not a claim about every definition of well-factorability in the literature. -/
theorem vaughan_cofactor_balanced_factorization_impossible
    {a b : ℕ → ℤ} {Q1 Q2 U l : ℕ}
    (ha : ∀ n, Q1 < n → a n = 0) (hb : ∀ n, Q2 < n → b n = 0)
    (hl : l.Prime) (hU : 1 ≤ U) (hUl : U < l) (h1 : Q1 < l) (h2 : Q2 < l)
    (hfact : ∀ n, lambdaU U n = dconv a b n) : False := by
  have h := hfact l
  rw [lambdaU_prime hl hU hUl,
    prime_support_obstruction_to_balanced_convolution ha hb hl h1 h2] at h
  exact absurd h (by norm_num)

/-- The same no-go stated as a single-point incompatibility, which is all the argument
actually uses. -/
theorem lambdaU_ne_balanced_convolution_at_prime
    {a b : ℕ → ℤ} {Q1 Q2 U l : ℕ}
    (ha : ∀ n, Q1 < n → a n = 0) (hb : ∀ n, Q2 < n → b n = 0)
    (hl : l.Prime) (hU : 1 ≤ U) (hUl : U < l) (h1 : Q1 < l) (h2 : Q2 < l) :
    lambdaU U l ≠ dconv a b l := by
  rw [lambdaU_prime hl hU hUl, prime_support_obstruction_to_balanced_convolution ha hb hl h1 h2]
  norm_num

end VaughanOuter
end Erdos287
