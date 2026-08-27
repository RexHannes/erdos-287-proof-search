import Mathlib

/-!
# The exact Vaughan identity and its affine specialisation (V14, Parts 3 and 4)

## Part 3 — the exact identity

`vaughan_identity_abstract` is the identity

`Λ = Λ_{≤V} + μ_{≤U} * log − μ_{≤U} * Λ_{≤V} * ζ + μ_{>U} * Λ_{>V} * ζ`

proved in an arbitrary commutative ring from exactly two hypotheses,

* `μ * ζ = 1` (the Möbius inversion identity: `μ ⋆ 1 = ε`),
* `log = Λ * ζ` (`Λ ⋆ 1 = log`),

together with the two truncation decompositions.  `vaughan_identity_exact` is its
instance in the Dirichlet convolution ring `ArithmeticFunction ℝ` with Mathlib's genuine
`ArithmeticFunction.vonMangoldt`, `ArithmeticFunction.moebius`, `ArithmeticFunction.log`
and `ArithmeticFunction.zeta`.  Nothing is postulated coefficientwise: the identity is
derived by ring algebra from the two Mathlib theorems
`ArithmeticFunction.coe_moebius_mul_coe_zeta` and `ArithmeticFunction.vonMangoldt_mul_zeta`.

`vaughan_pointwise` is the divisor-sum form

`Λ L = I₁(U,L) + I₂(U,V,L) + II(U,V,L) + [L ≤ V] Λ L`,

and `vaughan_pointwise_of_lt` records that the last term vanishes exactly when `V < L`
(hostile check 3: the vanishing is proved *from* the size hypothesis, never assumed).

## Part 4 — the affine specialisation

`affineNat s m n` is `2mn + 1` for `s = +1` and `2mn − 1` for `s = −1`.  The `−1` case is
defined by `Nat` subtraction but is **never used through it**: `affineNat_cast` converts to
`ℤ` under `1 ≤ m`, `1 ≤ n` (hostile check 8), and every downstream statement goes through
that cast.  `vaughan_affine_pointwise` is the pointwise identity at `L = affineNat s m n`.

No analytic sum is formed here.

Ledger targets:
`AFFINE287-VAUGHAN-IDENTITY : PROVED_ALGEBRAIC`,
`AFFINE287-VAUGHAN-SOURCE-ALGEBRA : PROVED_ALGEBRAIC`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ArithmeticFunction
open scoped BigOperators

namespace Erdos287
namespace Vaughan

/-! ## Truncations -/

/-- `f` restricted to arguments `≤ U`. -/
def truncLe {R : Type*} [Zero R] (f : ArithmeticFunction R) (U : ℕ) : ArithmeticFunction R :=
  ⟨fun n => if n ≤ U then f n else 0, by simp⟩

/-- `f` restricted to arguments `> U`. -/
def truncGt {R : Type*} [Zero R] (f : ArithmeticFunction R) (U : ℕ) : ArithmeticFunction R :=
  ⟨fun n => if U < n then f n else 0, by simp⟩

@[simp] theorem truncLe_apply {R : Type*} [Zero R] (f : ArithmeticFunction R) (U n : ℕ) :
    truncLe f U n = if n ≤ U then f n else 0 := rfl

@[simp] theorem truncGt_apply {R : Type*} [Zero R] (f : ArithmeticFunction R) (U n : ℕ) :
    truncGt f U n = if U < n then f n else 0 := rfl

/-- The two truncations reconstruct `f`. -/
theorem trunc_add {R : Type*} [AddMonoid R] (f : ArithmeticFunction R) (U : ℕ) :
    f = truncLe f U + truncGt f U := by
  ext n
  simp only [ArithmeticFunction.add_apply, truncLe_apply, truncGt_apply]
  split_ifs with h1 h2 <;> first | (exfalso; omega) | simp

/-- `μ_{>U} = μ − μ_{≤U}`, the form in which the truncation is usually written. -/
theorem truncGt_eq_sub {R : Type*} [AddCommGroup R] (f : ArithmeticFunction R) (U : ℕ) :
    truncGt f U = f - truncLe f U := by
  rw [eq_sub_iff_add_eq, add_comm]
  exact (trunc_add f U).symm

/-- Pointwise subtraction in `ArithmeticFunction R`. -/
theorem sub_apply' {R : Type*} [AddCommGroup R] (f g : ArithmeticFunction R) (n : ℕ) :
    (f - g) n = f n - g n := by
  rw [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply,
    ← sub_eq_add_neg]

/-! ## The exact identity -/

/-- **`vaughan_identity_abstract`** — `PROVED_ALGEBRAIC`.

Vaughan's identity in any commutative ring, from `mu * z = 1` and `lg = Lam * z`. -/
theorem vaughan_identity_abstract {A : Type*} [CommRing A]
    (Lam mu lg z LamLe LamGt muLe muGt : A)
    (hz : mu * z = 1) (hlog : lg = Lam * z)
    (hLam : Lam = LamLe + LamGt) (hmu : mu = muLe + muGt) :
    Lam = LamLe + muLe * lg - muLe * LamLe * z + muGt * LamGt * z := by
  subst hlog; subst hLam; subst hmu
  linear_combination (-LamGt) * hz

/-- **`vaughan_identity_exact`** — `PROVED_ALGEBRAIC`.

The exact Vaughan identity for Mathlib's von Mangoldt function, as an identity of Dirichlet
convolutions. -/
theorem vaughan_identity_exact (U V : ℕ) :
    (vonMangoldt : ArithmeticFunction ℝ) =
      truncLe vonMangoldt V
        + truncLe (↑moebius : ArithmeticFunction ℝ) U * ArithmeticFunction.log
        - truncLe (↑moebius : ArithmeticFunction ℝ) U * truncLe vonMangoldt V
            * (↑zeta : ArithmeticFunction ℝ)
        + truncGt (↑moebius : ArithmeticFunction ℝ) U * truncGt vonMangoldt V
            * (↑zeta : ArithmeticFunction ℝ) :=
  vaughan_identity_abstract _ _ _ _ _ _ _ _
    ArithmeticFunction.coe_moebius_mul_coe_zeta
    ArithmeticFunction.vonMangoldt_mul_zeta.symm
    (trunc_add vonMangoldt V) (trunc_add (↑moebius : ArithmeticFunction ℝ) U)

/-! ## Pointwise divisor-sum form -/

/-- Type-I term: `∑_{d ∣ L, d ≤ U} μ(d) log(L/d)`. -/
noncomputable def I1 (U L : ℕ) : ℝ :=
  ∑ d ∈ L.divisors.filter (fun d => d ≤ U), (moebius d : ℝ) * ArithmeticFunction.log (L / d)

/-- Second Type-I term: `−∑_{d e r = L, d ≤ U, e ≤ V} μ(d) Λ(e)`. -/
noncomputable def I2 (U V L : ℕ) : ℝ :=
  -∑ d ∈ L.divisors.filter (fun d => d ≤ U),
      ∑ e ∈ (L / d).divisors.filter (fun e => e ≤ V), (moebius d : ℝ) * vonMangoldt e

/-- Type-II term: `∑_{d e r = L, d > U, e > V} μ(d) Λ(e)`. -/
noncomputable def II (U V L : ℕ) : ℝ :=
  ∑ d ∈ L.divisors.filter (fun d => U < d),
      ∑ e ∈ (L / d).divisors.filter (fun e => V < e), (moebius d : ℝ) * vonMangoldt e

/-- A triple convolution `f * g * ζ` evaluated pointwise is the nested divisor sum
`∑_{d ∣ L} ∑_{e ∣ L/d} f(d) g(e)` — i.e. the sum over `d e r = L`. -/
theorem conv_zeta_apply (f g : ArithmeticFunction ℝ) (L : ℕ) :
    (f * g * (↑zeta : ArithmeticFunction ℝ)) L
      = ∑ d ∈ L.divisors, ∑ e ∈ (L / d).divisors, f d * g e := by
  rw [mul_assoc, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun d r => f d * (g * (↑zeta : ArithmeticFunction ℝ)) r)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [ArithmeticFunction.coe_mul_zeta_apply, Finset.mul_sum]

/-- `(f * log) L = ∑_{d ∣ L} f(d) log(L/d)`. -/
theorem mul_log_apply (f : ArithmeticFunction ℝ) (L : ℕ) :
    (f * ArithmeticFunction.log) L
      = ∑ d ∈ L.divisors, f d * ArithmeticFunction.log (L / d) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun d r => f d * ArithmeticFunction.log r)]

private theorem nested_trunc_sum (p q : ℕ → Prop) [DecidablePred p] [DecidablePred q]
    (F : ℕ → ℕ → ℝ) (L : ℕ) :
    (∑ d ∈ L.divisors, ∑ e ∈ (L / d).divisors,
        (if p d then (1 : ℝ) else 0) * (if q e then (1 : ℝ) else 0) * F d e)
      = ∑ d ∈ L.divisors.filter p, ∑ e ∈ ((L / d).divisors.filter q), F d e := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_filter]
  by_cases hd : p d
  · simp only [hd, if_true, one_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases he : q e <;> simp [he]
  · simp [hd]

/-- **`vaughan_pointwise`** — `PROVED_ALGEBRAIC`.

The pointwise divisor-sum form of the exact identity. -/
theorem vaughan_pointwise (U V L : ℕ) :
    vonMangoldt L = I1 U L + I2 U V L + II U V L + (if L ≤ V then vonMangoldt L else 0) := by
  have h := congrArg (fun F : ArithmeticFunction ℝ => F L) (vaughan_identity_exact U V)
  simp only [ArithmeticFunction.add_apply, sub_apply'] at h
  rw [conv_zeta_apply, conv_zeta_apply, mul_log_apply] at h
  have e1 : (∑ d ∈ L.divisors,
      truncLe (↑moebius : ArithmeticFunction ℝ) U d * ArithmeticFunction.log (L / d)) = I1 U L := by
    rw [I1, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hd : d ≤ U <;> simp [hd]
  have e2 : (∑ d ∈ L.divisors, ∑ e ∈ (L / d).divisors,
      truncLe (↑moebius : ArithmeticFunction ℝ) U d * truncLe vonMangoldt V e)
      = -I2 U V L := by
    rw [I2, neg_neg]
    rw [← nested_trunc_sum (fun d => d ≤ U) (fun e => e ≤ V)
      (fun d e => (moebius d : ℝ) * vonMangoldt e) L]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
    by_cases hd : d ≤ U <;> by_cases he : e ≤ V <;> simp [hd, he]
  have e3 : (∑ d ∈ L.divisors, ∑ e ∈ (L / d).divisors,
      truncGt (↑moebius : ArithmeticFunction ℝ) U d * truncGt vonMangoldt V e)
      = II U V L := by
    rw [II]
    rw [← nested_trunc_sum (fun d => U < d) (fun e => V < e)
      (fun d e => (moebius d : ℝ) * vonMangoldt e) L]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
    by_cases hd : U < d <;> by_cases he : V < e <;> simp [hd, he]
  rw [e1, e2, e3] at h
  simp only [truncLe_apply] at h
  linarith [h]

/-- **`vaughan_pointwise_of_lt`** — the `Λ_{≤V}` term vanishes exactly under the size
hypothesis `V < L` (hostile check 3). -/
theorem vaughan_pointwise_of_lt {U V L : ℕ} (hV : V < L) :
    vonMangoldt L = I1 U L + I2 U V L + II U V L := by
  have h := vaughan_pointwise U V L
  rw [if_neg (by omega)] at h
  simpa using h

/-! ## Part 4 — the affine specialisation -/

/-- The two shifts `s = ±1` of the affine form `2mn + s`. -/
inductive AffineSign
  | plus
  | minus
  deriving DecidableEq, Repr

namespace AffineSign

/-- The shift as an integer. -/
def val : AffineSign → ℤ
  | plus => 1
  | minus => -1

@[simp] theorem val_plus : AffineSign.plus.val = 1 := rfl
@[simp] theorem val_minus : AffineSign.minus.val = -1 := rfl

theorem val_eq_one_or : ∀ s : AffineSign, s.val = 1 ∨ s.val = -1
  | plus => Or.inl rfl
  | minus => Or.inr rfl

theorem val_ne_zero (s : AffineSign) : s.val ≠ 0 := by
  rcases s.val_eq_one_or with h | h <;> rw [h] <;> norm_num

end AffineSign

/-- `affineNat plus m n = 2mn + 1`, `affineNat minus m n = 2mn − 1`.

The `minus` branch uses `Nat` subtraction; `affineNat_cast` below is the only interface
used downstream, and it carries the positivity hypotheses that make the subtraction
faithful. -/
def affineNat : AffineSign → ℕ → ℕ → ℕ
  | AffineSign.plus, m, n => 2 * m * n + 1
  | AffineSign.minus, m, n => 2 * m * n - 1

@[simp] theorem affineNat_plus (m n : ℕ) : affineNat AffineSign.plus m n = 2 * m * n + 1 := rfl
@[simp] theorem affineNat_minus (m n : ℕ) : affineNat AffineSign.minus m n = 2 * m * n - 1 := rfl

/-- **The `Nat`-subtraction firewall.**  For `m, n ≥ 1` the natural-number value casts to
the intended integer `2mn + s`. -/
theorem affineNat_cast (s : AffineSign) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (affineNat s m n : ℤ) = 2 * (m : ℤ) * (n : ℤ) + s.val := by
  have hmn : 0 < m * n := Nat.mul_pos hm hn
  have h2 : 2 * m * n = 2 * (m * n) := by ring
  have h : 1 ≤ 2 * m * n := by omega
  cases s with
  | plus =>
      simp only [affineNat, AffineSign.val_plus]
      push_cast
      ring
  | minus =>
      simp only [affineNat, AffineSign.val_minus]
      rw [Nat.cast_sub h]
      push_cast
      ring

theorem affineNat_pos (s : AffineSign) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    0 < affineNat s m n := by
  have hmn : 0 < m * n := Nat.mul_pos hm hn
  have h2 : 2 * m * n = 2 * (m * n) := by ring
  cases s <;> simp only [affineNat] <;> omega

/-- The affine values are odd (they are `2mn ± 1`). -/
theorem affineNat_odd (s : AffineSign) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ¬ 2 ∣ affineNat s m n := by
  have hmn : 0 < m * n := Nat.mul_pos hm hn
  have h2 : 2 * m * n = 2 * (m * n) := by ring
  cases s <;> simp only [affineNat] <;> omega

/-- **`vaughan_affine_pointwise`** — `PROVED_ALGEBRAIC`.

Vaughan's identity applied pointwise to the affine value `2mn + s`, with the `Λ_{≤V}` term
already removed under the size hypothesis `V < 2mn + s`. -/
theorem vaughan_affine_pointwise (s : AffineSign) (U V m n : ℕ)
    (hV : V < affineNat s m n) :
    vonMangoldt (affineNat s m n)
      = I1 U (affineNat s m n) + I2 U V (affineNat s m n) + II U V (affineNat s m n) :=
  vaughan_pointwise_of_lt hV

/-- The unrestricted affine form, for reference. -/
theorem vaughan_affine_pointwise_full (s : AffineSign) (U V m n : ℕ) :
    vonMangoldt (affineNat s m n)
      = I1 U (affineNat s m n) + I2 U V (affineNat s m n) + II U V (affineNat s m n)
        + (if affineNat s m n ≤ V then vonMangoldt (affineNat s m n) else 0) :=
  vaughan_pointwise U V _

end Vaughan
end Erdos287
