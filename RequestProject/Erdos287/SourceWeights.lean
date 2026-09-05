import Mathlib
import RequestProject.CurrentProgramme.Erdos287September4BsrcLocalMobiusCollapse

/-!
# Erdős #287 — physical source weights on odd squarefree moduli

```
BETA  MULTIPLICATIVITY                 : KERNEL-PROVED
B0    MULTIPLICATIVITY                 : KERNEL-PROVED
BSRC  (TYPED) MULTIPLICATIVITY         : KERNEL-PROVED
LAMBDA LOCAL FACTOR / MULTIPLICATIVITY : KERNEL-PROVED
LOCAL PRIME IDENTITY  β(p) − B0(p) = −1: KERNEL-PROVED
physicalBsrcMobiusCollapse45           : KERNEL-PROVED
q = 15 REGRESSION                      : KERNEL-PROVED
```

## The P0 normalisation repair

The earlier bank module
`RequestProject.CurrentProgramme.Erdos287September4BsrcLocalMobiusCollapse`
works with a **purely local** datum

    Bsrc Bloc d = ∏_{p ∣ d} Bloc p ,     beta bloc k = ∏_{p ∣ k} bloc k

together with the local normalisation hypothesis `bloc p − Bloc p = −S₂`
*at every prime `p ∣ q`*.  Under that hypothesis the divisor sum necessarily
evaluates to `S₂^{ω(q)}·μ(q)`: the **global** constant `S₂` has been inserted
into *each* local prime factor and is then multiplied over `q.primeFactors`.
That is a normalisation (type) bug relative to the physical source, **not** a
mathematical error: the abstract theorems in that module remain true, but they
describe an artificially locally-normalised model, not the physical one.

The physical source carries **one** global `S₂`:

    B0(d)     = ∏_{p ∣ d} (p−1)/(p−2)
    B_src(d)  = S₂ · B0(d)
    β(d)      = ∏_{p ∣ d} 1/(p−2)

and then, for **odd squarefree** `q`,

    ∑_{d ∣ q} μ(d) · B_src(d) · β(q/d) = S₂ · μ(q).

Note that `B_src` is *not* multiplicative in the naive sense; the correct typed
relation on coprime arguments is `B_src(ab)·S₂ = B_src(a)·B_src(b)`.

Oddness is essential for the collapse: at `p = 2` one has `(p−2) = 0`, so in `ℚ`
both local factors vanish and `β(2) − B0(2) = 0 ≠ −1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos287
namespace SourceWeights

/-! ## §1.1  Definitions -/

/-- `β(n) = ∏_{p ∣ n} 1/(p−2)`, the local source weight. -/
def beta (n : ℕ) : ℚ := ∏ p ∈ n.primeFactors, (1 / ((p : ℚ) - 2))

/-- `B0(n) = ∏_{p ∣ n} (p−1)/(p−2)`, the normalised source weight (`S₂` factored out). -/
def B0 (n : ℕ) : ℚ := ∏ p ∈ n.primeFactors, (((p : ℚ) - 1) / ((p : ℚ) - 2))

/-- `B_src(n) = S₂ · B0(n)`: the physical source weight, with **one** global `S₂`. -/
def Bsrc (S2 : ℚ) (n : ℕ) : ℚ := S2 * B0 n

/-- `λ(b) = ∏_{p ∣ b} (p−1)/(p−2)²`, the local factor produced by the gcd descent. -/
def lam (n : ℕ) : ℚ := ∏ p ∈ n.primeFactors, (((p : ℚ) - 1) / ((p : ℚ) - 2) ^ 2)

@[simp] theorem beta_one : beta 1 = 1 := by simp [beta]

@[simp] theorem B0_one : B0 1 = 1 := by simp [B0]

@[simp] theorem lam_one : lam 1 = 1 := by simp [lam]

@[simp] theorem Bsrc_one (S2 : ℚ) : Bsrc S2 1 = S2 := by simp [Bsrc]

/-! ## §1.2  Multiplicativity on coprime arguments -/

/-- Generic multiplicativity of a product over prime factors, on coprime nonzero arguments. -/
theorem prod_primeFactors_mul_of_coprime (f : ℕ → ℚ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : Nat.Coprime a b) :
    ∏ p ∈ (a * b).primeFactors, f p
      = (∏ p ∈ a.primeFactors, f p) * ∏ p ∈ b.primeFactors, f p := by
  rw [Nat.primeFactors_mul ha hb, Finset.prod_union hab.disjoint_primeFactors]

/-- **`beta_mul`.** `β(ab) = β(a)β(b)` for coprime nonzero `a, b`. -/
theorem beta_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b) :
    beta (a * b) = beta a * beta b :=
  prod_primeFactors_mul_of_coprime _ ha hb hab

/-- **`B0_mul`.** `B0(ab) = B0(a)B0(b)` for coprime nonzero `a, b`. -/
theorem B0_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b) :
    B0 (a * b) = B0 a * B0 b :=
  prod_primeFactors_mul_of_coprime _ ha hb hab

/-- **`lam_mul`.** `λ(ab) = λ(a)λ(b)` for coprime nonzero `a, b`. -/
theorem lam_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b) :
    lam (a * b) = lam a * lam b :=
  prod_primeFactors_mul_of_coprime _ ha hb hab

/-- **`Bsrc_mul_typed`.** `B_src` is *not* multiplicative: the correct typed relation on
coprime arguments is `S₂ · B_src(ab) = B_src(a) · B_src(b)`. -/
theorem Bsrc_mul_typed (S2 : ℚ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b) :
    S2 * Bsrc S2 (a * b) = Bsrc S2 a * Bsrc S2 b := by
  simp only [Bsrc, B0_mul ha hb hab]; ring

/-- **`lam_eq_B0_mul_beta`.** The descent local factor is the product of the two source
weights: `λ(b) = B0(b) · β(b)`. -/
theorem lam_eq_B0_mul_beta (n : ℕ) : lam n = B0 n * beta n := by
  rw [lam, B0, beta, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  field_simp

/-! ## §1.3  The local prime identity -/

/-- **`beta_sub_B0_prime`.** For every **odd** prime `p`, `β(p) − B0(p) = −1`. -/
theorem beta_sub_B0_prime {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) : beta p - B0 p = -1 := by
  have h2 : ((p : ℚ) - 2) ≠ 0 := by
    have : (p : ℚ) ≠ 2 := by exact_mod_cast fun h => hodd (by exact_mod_cast h)
    intro h; exact this (by linarith [sub_eq_zero.1 h])
  rw [beta, B0, hp.primeFactors, Finset.prod_singleton, Finset.prod_singleton]
  field_simp
  ring

/-- The `p = 2` obstruction: the local identity **fails** at `p = 2`, which is why the
collapse below is stated for odd `q` only. -/
theorem beta_sub_B0_two : beta 2 - B0 2 = 0 := by
  rw [beta, B0, Nat.Prime.primeFactors Nat.prime_two, Finset.prod_singleton,
    Finset.prod_singleton]
  norm_num

/-! ## §1.4  The corrected physical local Möbius collapse -/

/-- For squarefree `q`, `μ(q) = (−1)^{ω(q)}` in `ℚ`. -/
theorem moebius_ratCast_of_squarefree {q : ℕ} (hq : Squarefree q) :
    (moebius q : ℚ) = (-1) ^ q.primeFactors.card := by
  have hprime : ∀ p ∈ q.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have h := September4BsrcCollapse.moebius_prod_primes hprime
  rw [Nat.prod_primeFactors_of_squarefree hq] at h
  exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) h

private theorem B0_eq_abstract (d : ℕ) :
    B0 d = September4BsrcCollapse.Bsrc (fun p => ((p : ℚ) - 1) / ((p : ℚ) - 2)) d := rfl

private theorem beta_eq_abstract (d : ℕ) :
    beta d = September4BsrcCollapse.beta (fun p => 1 / ((p : ℚ) - 2)) d := rfl

/-- **`normalizedB0MobiusCollapse45`.** `KERNEL-PROVED`.  For odd squarefree `q`,

    ∑_{d ∣ q} μ(d) · B0(d) · β(q/d) = ∏_{p ∣ q} (β(p) − B0(p)) = (−1)^{ω(q)} = μ(q). -/
theorem normalizedB0MobiusCollapse45 {q : ℕ} (hq : Squarefree q) (hodd : Odd q) :
    ∑ d ∈ q.divisors, (moebius d : ℚ) * B0 d * beta (q / d) = (moebius q : ℚ) := by
  classical
  have hcollapse :
      ∑ d ∈ q.divisors, (moebius d : ℚ) * B0 d * beta (q / d)
        = ∏ p ∈ q.primeFactors, ((1 / ((p : ℚ) - 2)) - (((p : ℚ) - 1) / ((p : ℚ) - 2))) := by
    simpa [B0_eq_abstract, beta_eq_abstract] using
      September4BsrcCollapse.interiorLocalMobiusCollapse45
        (fun p => ((p : ℚ) - 1) / ((p : ℚ) - 2)) (fun p => 1 / ((p : ℚ) - 2)) hq
  have hlocal : ∀ p ∈ q.primeFactors,
      (1 / ((p : ℚ) - 2)) - (((p : ℚ) - 1) / ((p : ℚ) - 2)) = -1 := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hne2 : p ≠ 2 := by
      rintro rfl
      have h2 : (2 : ℕ) ∣ q := Nat.dvd_of_mem_primeFactors hp
      rw [Nat.odd_iff] at hodd
      omega
    have := beta_sub_B0_prime hprime hne2
    rwa [beta, B0, hprime.primeFactors, Finset.prod_singleton, Finset.prod_singleton] at this
  rw [hcollapse, Finset.prod_congr rfl hlocal, Finset.prod_const,
    moebius_ratCast_of_squarefree hq]

/-- **`physicalBsrcMobiusCollapse45`.** `KERNEL-PROVED`.  The corrected **physical**
identity, with a single global `S₂`:

    ∑_{d ∣ q} μ(d) · B_src(d) · β(q/d) = S₂ · μ(q)

for odd squarefree `q`. -/
theorem physicalBsrcMobiusCollapse45 (S2 : ℚ) {q : ℕ} (hq : Squarefree q) (hodd : Odd q) :
    ∑ d ∈ q.divisors, (moebius d : ℚ) * Bsrc S2 d * beta (q / d) = S2 * (moebius q : ℚ) := by
  have : ∑ d ∈ q.divisors, (moebius d : ℚ) * Bsrc S2 d * beta (q / d)
      = S2 * ∑ d ∈ q.divisors, (moebius d : ℚ) * B0 d * beta (q / d) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by simp [Bsrc]; ring
  rw [this, normalizedB0MobiusCollapse45 hq hodd]

/-! ## §1.5  The `q = 15` regression test -/

theorem primeFactors_fifteen : (15 : ℕ).primeFactors = {3, 5} := by
  have h : (15 : ℕ) = 3 * 5 := by norm_num
  rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
  rfl

theorem squarefree_fifteen : Squarefree (15 : ℕ) := by
  have h : (15 : ℕ) = 3 * 5 := by norm_num
  rw [h]
  exact (Nat.squarefree_mul (by norm_num)).2
    ⟨Nat.prime_three.squarefree, (by norm_num : Nat.Prime 5).squarefree⟩

theorem odd_fifteen : Odd (15 : ℕ) := ⟨7, by norm_num⟩

@[simp] theorem beta_three : beta 3 = 1 := by
  rw [beta, Nat.Prime.primeFactors (by norm_num), Finset.prod_singleton]; norm_num

@[simp] theorem beta_five : beta 5 = 1 / 3 := by
  rw [beta, Nat.Prime.primeFactors (by norm_num), Finset.prod_singleton]; norm_num

@[simp] theorem B0_three : B0 3 = 2 := by
  rw [B0, Nat.Prime.primeFactors (by norm_num), Finset.prod_singleton]; norm_num

@[simp] theorem B0_five : B0 5 = 4 / 3 := by
  rw [B0, Nat.Prime.primeFactors (by norm_num), Finset.prod_singleton]; norm_num

@[simp] theorem beta_fifteen : beta 15 = 1 / 3 := by
  rw [beta, primeFactors_fifteen]; norm_num

@[simp] theorem B0_fifteen : B0 15 = 8 / 3 := by
  rw [B0, primeFactors_fifteen]; norm_num

/-- **`regression_q15_normalized`.** `KERNEL-PROVED`.  The explicit `q = 15` cube identity
for the normalised weight:

    β(15) − B0(3)β(5) − B0(5)β(3) + B0(15) = 1. -/
theorem regression_q15_normalized :
    beta 15 - B0 3 * beta 5 - B0 5 * beta 3 + B0 15 = 1 := by
  norm_num

/-- **`regression_q15_physical`.** `KERNEL-PROVED`.  The physical divisor sum at `q = 15`
equals `S₂` — in agreement with `S₂ · μ(15) = S₂`, and **not** with `S₂²·μ(15)`. -/
theorem regression_q15_physical (S2 : ℚ) :
    ∑ d ∈ (15 : ℕ).divisors, (moebius d : ℚ) * Bsrc S2 d * beta (15 / d) = S2 := by
  have hmu : (moebius 15 : ℚ) = 1 := by
    rw [moebius_ratCast_of_squarefree squarefree_fifteen, primeFactors_fifteen]
    norm_num
  rw [physicalBsrcMobiusCollapse45 S2 squarefree_fifteen odd_fifteen, hmu, mul_one]

end SourceWeights
end Erdos287
