import Mathlib

/-!
# Erdős #287 — Type-II source: the Heath–Brown identity (Maynard, arXiv:2006.07088v1, Lemma 5.3)

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

Maynard's Lemma 5.3 is printed as

`Λ(n) = ∑_{j=1}^k (-1)^j C(k,j) ∑_{n = n_1⋯n_j m_1⋯m_j, m_i ≤ 2x^{1/k}} μ(m_1)⋯μ(m_j) log n_1`
(`n ≤ 2x`).

**Repair.** The sign `(-1)^j` is a misprint: with it the right-hand side equals `-Λ(n)`
(`maynard_printed_sign_eq_neg`), so the printed identity is false for every prime power `n`
(`maynard_printed_sign_false`, e.g. `n = 2`).  The correct sign is `(-1)^{j-1}`:

* `heathBrown` — for every `z, k` and every `n < (z+1)^k`,
  `Λ(n) = ∑_{j=1}^k (-1)^{j+1} C(k,j) (log * ζ^{j-1} * M_z^j)(n)`, with
  `M_z(m) = μ(m) 1_{m ≤ z}` the truncated Möbius function;
* `heathBrown_three` — the case `k = 3` (three truncated Möbius variables, three smooth
  variables, one of them carrying `log`), as used in Maynard's §5 and in the spec §20;
* `heathBrown_maynard_range` — Maynard's range: `n ≤ 2x`, `z = ⌊2x^{1/k}⌋` satisfies
  `n < (z+1)^k`.

All proofs are algebra in the commutative ring of arithmetic functions:
`(1 - ζ M_z)` vanishes on `n ≤ z` (Möbius inversion), so `(1 - ζ M_z)^k` vanishes below
`(z+1)^k`; expand binomially and use `Λ * ζ = log`.
-/

open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Finset ArithmeticFunction

set_option autoImplicit false

namespace Erdos287.Physical.TypeII

/-- The truncated Möbius function `M_z(m) = μ(m) 1_{m ≤ z}`. -/
noncomputable def Mz (z : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ z then (μ n : ℝ) else 0, by simp⟩

theorem Mz_apply (z n : ℕ) : Mz z n = if n ≤ z then (μ n : ℝ) else 0 := rfl

/-- `f` vanishes on `n < A`. -/
def VanishBelow (f : ArithmeticFunction ℝ) (A : ℕ) : Prop := ∀ n < A, f n = 0

theorem VanishBelow.mul {f g : ArithmeticFunction ℝ} {A B : ℕ} (hf : VanishBelow f A)
    (hg : VanishBelow g B) : VanishBelow (f * g) (A * B) := by
  intro n hn
  rw [mul_apply]
  refine Finset.sum_eq_zero (fun x hx => ?_)
  obtain ⟨hmul, -⟩ := Nat.mem_divisorsAntidiagonal.1 hx
  by_cases h1 : x.1 < A
  · rw [hf _ h1, zero_mul]
  · by_cases h2 : x.2 < B
    · rw [hg _ h2, mul_zero]
    · push_neg at h1 h2
      have := Nat.mul_le_mul h1 h2
      omega

theorem VanishBelow.pow {f : ArithmeticFunction ℝ} {A : ℕ} (hf : VanishBelow f A) (k : ℕ) :
    VanishBelow (f ^ k) (A ^ k) := by
  induction k with
  | zero =>
    intro n hn
    simp only [pow_zero] at hn ⊢
    have : n = 0 := by omega
    subst this; simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul hf

theorem vanishBelow_one_left (f : ArithmeticFunction ℝ) : VanishBelow f 1 := by
  intro n hn
  have : n = 0 := by omega
  subst this; simp

/-- `1 - ζ M_z` vanishes on `n ≤ z`. -/
theorem one_sub_zeta_Mz_vanish (z : ℕ) : VanishBelow (1 - (ζ : ArithmeticFunction ℝ) * Mz z) (z + 1) := by
  intro n hn
  rw [sub_eq_add_neg, add_apply, ArithmeticFunction.neg_apply, coe_zeta_mul_apply]
  have hsum : ∑ i ∈ n.divisors, Mz z i = ∑ i ∈ n.divisors, (μ i : ℝ) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Mz_apply, if_pos ((Nat.divisor_le hi).trans (by omega))]
  rw [hsum]
  have : ∑ i ∈ n.divisors, (μ i : ℝ) = ((μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) n := by
    rw [coe_mul_zeta_apply]; simp
  rw [this, coe_moebius_mul_coe_zeta]
  ring

theorem sum_apply' {ι : Type*} (s : Finset ι) (f : ι → ArithmeticFunction ℝ) (n : ℕ) :
    (∑ i ∈ s, f i) n = ∑ i ∈ s, f i n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, ih]

theorem natCast_mul_apply (c : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    ((c : ArithmeticFunction ℝ) * f) n = c * f n := by
  induction c with
  | zero => simp
  | succ c ih => rw [Nat.cast_succ, add_mul, one_mul, add_apply, ih]; push_cast; ring

theorem neg_one_pow_mul_apply (m : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    (((-1 : ArithmeticFunction ℝ)) ^ m * f) n = (-1 : ℝ) ^ m * f n := by
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, mul_assoc, show (-1 : ArithmeticFunction ℝ) * f = -f from neg_one_mul f, ih,
      ArithmeticFunction.neg_apply, pow_succ]
    ring

/-- **Heath–Brown's identity** (corrected sign): for `n < (z+1)^k`,
`Λ(n) = ∑_{j=1}^{k} (-1)^{j-1} C(k,j) (log * ζ^{j-1} * M_z^j)(n)` (index shifted `j ↦ j+1`). -/
theorem heathBrown (z k : ℕ) {n : ℕ} (hn : n < (z + 1) ^ k) :
    Λ n = ∑ j ∈ range k, (-1 : ℝ) ^ j * (k.choose (j + 1) : ℝ) *
      ((log : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) ^ j * Mz z ^ (j + 1)) n := by
  set g : ArithmeticFunction ℝ := (ζ : ArithmeticFunction ℝ) * Mz z with hg
  have hv : VanishBelow (Λ * (1 - g) ^ k) ((z + 1) ^ k) := by
    have := (vanishBelow_one_left Λ).mul ((one_sub_zeta_Mz_vanish z).pow k)
    rwa [one_mul] at this
  have h0 := hv n hn
  have hexp : (1 - g) ^ k = ∑ m ∈ range (k + 1),
      ((-1 : ArithmeticFunction ℝ) ^ m * g ^ m) * (k.choose m : ArithmeticFunction ℝ) := by
    rw [show (1 - g) = -g + 1 by ring, add_pow]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [one_pow, mul_one, neg_pow g m]
  rw [hexp, Finset.mul_sum, sum_apply', Finset.sum_range_succ'] at h0
  have hterm0 : (Λ * (((-1 : ArithmeticFunction ℝ) ^ 0 * g ^ 0) *
      (k.choose 0 : ArithmeticFunction ℝ))) n = Λ n := by simp
  have htermS : ∀ j, (Λ * (((-1 : ArithmeticFunction ℝ) ^ (j + 1) * g ^ (j + 1)) *
      (k.choose (j + 1) : ArithmeticFunction ℝ))) n =
      -((-1 : ℝ) ^ j * (k.choose (j + 1) : ℝ) *
        (((log : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) ^ j * Mz z ^ (j + 1)) n)) := by
    intro j
    have : Λ * (((-1 : ArithmeticFunction ℝ) ^ (j + 1) * g ^ (j + 1)) *
        (k.choose (j + 1) : ArithmeticFunction ℝ)) = (-1) ^ (j + 1) *
        ((k.choose (j + 1) : ArithmeticFunction ℝ) *
          ((log : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) ^ j * Mz z ^ (j + 1))) := by
      rw [hg, mul_pow, pow_succ' (ζ : ArithmeticFunction ℝ) j, ← vonMangoldt_mul_zeta]
      ring
    rw [this, neg_one_pow_mul_apply, natCast_mul_apply, pow_succ]
    ring
  rw [hterm0] at h0
  simp only [htermS, Finset.sum_neg_distrib] at h0
  linarith

/-- **Heath–Brown with `k = 3`**: three truncated Möbius variables and three smooth variables
(`log * ζ^{j-1} * M_z^j`, `j = 1, 2, 3`), valid for `n < (z+1)^3`. -/
theorem heathBrown_three (z : ℕ) {n : ℕ} (hn : n < (z + 1) ^ 3) :
    Λ n = 3 * ((log : ArithmeticFunction ℝ) * Mz z) n
      - 3 * ((log : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) * Mz z ^ 2) n
      + ((log : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) ^ 2 * Mz z ^ 3) n := by
  rw [heathBrown z 3 hn]
  have c1 : (3 : ℕ).choose 1 = 3 := rfl
  have c2 : (3 : ℕ).choose 2 = 3 := rfl
  have c3 : (3 : ℕ).choose 3 = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, mul_one, zero_add,
    c1, c2, c3]
  push_cast
  ring

/-- **Maynard's printed sign gives `-Λ`**: with `(-1)^j` in place of `(-1)^{j-1}` the right-hand
side of Lemma 5.3 is exactly `-Λ(n)`. -/
theorem maynard_printed_sign_eq_neg (z k : ℕ) {n : ℕ} (hn : n < (z + 1) ^ k) :
    ∑ j ∈ range k, (-1 : ℝ) ^ (j + 1) * (k.choose (j + 1) : ℝ) *
      ((log : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) ^ j * Mz z ^ (j + 1)) n = -Λ n := by
  rw [heathBrown z k hn, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [pow_succ]; ring

/-- **Negative control**: the identity as printed (sign `(-1)^j`) is false, e.g. at
`n = 2`, `k = 1`, `z = 2`. -/
theorem maynard_printed_sign_false :
    ¬ ∀ z k n : ℕ, 1 ≤ k → n < (z + 1) ^ k →
      Λ n = ∑ j ∈ range k, (-1 : ℝ) ^ (j + 1) * (k.choose (j + 1) : ℝ) *
        ((log : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) ^ j * Mz z ^ (j + 1)) n := by
  intro h
  have h2 := h 2 1 2 le_rfl (by norm_num)
  rw [maynard_printed_sign_eq_neg 2 1 (by norm_num)] at h2
  have hpos : 0 < Λ 2 := by
    rw [vonMangoldt_apply_prime Nat.prime_two]
    exact Real.log_pos (by norm_num)
  linarith

/-- **Maynard's range**: for `n ≤ 2x` and `z = ⌊2 x^{1/k}⌋`, `n < (z+1)^k` (`k ≥ 1`). -/
theorem heathBrown_maynard_range {x : ℝ} (hx : 0 < x) {k : ℕ} (hk : 1 ≤ k) {n : ℕ}
    (hn : (n : ℝ) ≤ 2 * x) : n < (⌊2 * x ^ (1 / (k : ℝ))⌋₊ + 1) ^ k := by
  have hz : 2 * x ^ (1 / (k : ℝ)) < (⌊2 * x ^ (1 / (k : ℝ))⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hpos : 0 ≤ 2 * x ^ (1 / (k : ℝ)) := by positivity
  have hpow : (2 * x ^ (1 / (k : ℝ))) ^ k = 2 ^ k * x := by
    rw [mul_pow, ← Real.rpow_natCast (x ^ (1 / (k : ℝ))), ← Real.rpow_mul hx.le,
      one_div_mul_cancel (by exact_mod_cast (show k ≠ 0 by omega)), Real.rpow_one]
  have h1 : (2 * x ^ (1 / (k : ℝ))) ^ k < ((⌊2 * x ^ (1 / (k : ℝ))⌋₊ : ℝ) + 1) ^ k :=
    pow_lt_pow_left₀ hz hpos (by omega)
  have h2 : (2 : ℝ) ≤ 2 ^ k := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have : (n : ℝ) < ((⌊2 * x ^ (1 / (k : ℝ))⌋₊ + 1 : ℕ) : ℝ) ^ k := by
    push_cast
    rw [hpow] at h1
    nlinarith
  exact_mod_cast this

end Erdos287.Physical.TypeII
