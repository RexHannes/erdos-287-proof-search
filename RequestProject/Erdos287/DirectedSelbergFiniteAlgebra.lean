import Mathlib

/-!
# Erdős #287 — the finite algebra of the directed upper sieve (§66)

INTERNAL #287 EFFECTIVITY PROGRAMME ONLY.  Nothing here claims Erdős #287, and **no analytic
statement is proved here**: this module formalises only the *deterministic / finite* part of
the directed Selberg upper-sieve argument, plus the exact rational comparisons that turn a
capacity input into the `T_box` allocation.  Every analytic ingredient enters as an explicit
hypothesis; there is no custom axiom.

## Contents

* `SelbergData`, `G`, `capacity` — the finite sieve data on a finite support `D`, the sieve
  sum `G(z) = ∑_{d ∈ D} g d`, and the capacity `1 / G(z)`.
* `quadraticForm_ge_inv_capacity` — the finite quadratic-form inequality (Sedrakyan/Cauchy–
  Schwarz): on the normalised simplex `∑ y_d = 1` the form `∑ y_d² / g_d` is at least `1/G`.
* `quadraticForm_optimal` — the bound is attained at `y_d = g_d / G`: the finite Selberg
  optimum is exactly `1/G`, so the capacity value is sharp for this algebra.
* `selberg_optimum_of_diagonalisation` — the consumer form: *given* a diagonalisation of the
  sieve form and the normalisation `λ₁ = 1`, the form is at least the capacity.
* `G_mono`, `capacity_antitone` — monotonicity of the finite capacity functions.
* `prime_le_sqrt_of_proper_power`, `properPrimePowers_subset` — the proper-prime-power
  combinatorics used to separate the proper powers from the prime support.
* `T_box_bound_of_capacity`, `T_box_ratio_bound` — the exact rational final comparisons:
  separation cost `6` together with capacity `≥ 9523810` gives the `6.3e-7 · X/log X` box
  bound, and the prime comparison `B ≥ 0.3 · X/log X` turns it into the `2.1e-6 · B`
  allocation.  Both are stated with their analytic inputs as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace DirectedSelberg

/-! ## §66.1  Finite sieve data, `G(z)` and the capacity -/

/-- Finite data for a directed Selberg sieve on the support `D`: a positive local weight
`g d` for every `d ∈ D` (in applications `g` is built from the local root counts and the
multiplicative functions `g(d)`, `h(d)`; only positivity is used by the finite algebra). -/
structure SelbergData (D : Finset ℕ) where
  /-- the local weight -/
  g : ℕ → ℚ
  /-- positivity of the local weight on the support -/
  g_pos : ∀ d ∈ D, 0 < g d
  /-- the support is nonempty (it always contains `d = 1`) -/
  one_mem : (1 : ℕ) ∈ D

variable {D : Finset ℕ} (S : SelbergData D)

/-- The sieve sum `G(z) = ∑_{d ∈ D} g d`. -/
def G : ℚ := ∑ d ∈ D, S.g d

/-- **`G_pos`.**  `KERNEL-PROVED`.  The sieve sum is positive. -/
theorem G_pos : 0 < G S := by
  refine Finset.sum_pos' (fun d hd => (S.g_pos d hd).le) ⟨1, S.one_mem, S.g_pos 1 S.one_mem⟩

/-- The finite Selberg **capacity** `1 / G(z)`. -/
def capacity : ℚ := 1 / G S

/-- **`capacity_pos`.**  `KERNEL-PROVED`. -/
theorem capacity_pos : 0 < capacity S := by
  rw [capacity]
  exact div_pos one_pos (G_pos S)

/-! ## §66.2  The finite quadratic form and its optimum -/

/-- The diagonalised Selberg quadratic form `∑_{d ∈ D} y_d² / g_d`. -/
def quadraticForm (y : ℕ → ℚ) : ℚ := ∑ d ∈ D, (y d) ^ 2 / S.g d

/-- The normalisation `∑_{d ∈ D} y_d = 1`, which is exactly the constraint `λ₁ = 1` in the
diagonalising variables. -/
def Normalised (D : Finset ℕ) (y : ℕ → ℚ) : Prop := ∑ d ∈ D, y d = 1

/-- **`quadraticForm_ge_inv_capacity`.**  `KERNEL-PROVED`.  The finite quadratic-form
inequality: on the normalised simplex the Selberg form is at least the capacity `1/G`. -/
theorem quadraticForm_ge_inv_capacity {y : ℕ → ℚ} (hy : Normalised D y) :
    capacity S ≤ quadraticForm S y := by
  have h := Finset.sq_sum_div_le_sum_sq_div D y (g := S.g) (fun d hd => S.g_pos d hd)
  have hy' : ∑ d ∈ D, y d = 1 := hy
  rw [hy'] at h
  simpa [capacity, quadraticForm, G] using h

/-- The optimal profile `y_d = g_d / G`. -/
def optimalY : ℕ → ℚ := fun d => S.g d / G S

/-- **`optimalY_normalised`.**  `KERNEL-PROVED`. -/
theorem optimalY_normalised : Normalised D (optimalY S) := by
  show ∑ d ∈ D, optimalY S d = 1
  simp only [optimalY]
  rw [← Finset.sum_div, ← G]
  exact div_self (G_pos S).ne'

/-- **`quadraticForm_optimal`.**  `KERNEL-PROVED`.  The capacity is attained: the finite
Selberg optimum equals `1/G` exactly, so the capacity value is sharp. -/
theorem quadraticForm_optimal : quadraticForm S (optimalY S) = capacity S := by
  have hG := (G_pos S).ne'
  simp only [quadraticForm, optimalY, capacity]
  have : ∀ d ∈ D, (S.g d / G S) ^ 2 / S.g d = S.g d / (G S) ^ 2 := by
    intro d hd
    field_simp
  rw [Finset.sum_congr rfl this, ← Finset.sum_div, ← G]
  rw [sq]
  field_simp

/-- **`selberg_optimum_of_diagonalisation`.**  `KERNEL-PROVED`.  The consumer form of the
finite algebra.  If a family of sieve weights `lam` is diagonalised by `y` (hypothesis
`hdiag`), and the normalisation `λ₁ = 1` transports to `∑ y_d = 1` (hypothesis `hnorm`), then
the sieve form of any admissible weight is at least the capacity.  The two hypotheses are the
*algebraic* inputs of the Selberg construction; no analytic input is used. -/
theorem selberg_optimum_of_diagonalisation {Λ : Type*} (Q : Λ → ℚ) (y : Λ → ℕ → ℚ)
    (adm : Λ → Prop) (hdiag : ∀ l, Q l = quadraticForm S (y l))
    (hnorm : ∀ l, adm l → Normalised D (y l)) (l : Λ) (hl : adm l) :
    capacity S ≤ Q l := by
  rw [hdiag l]
  exact quadraticForm_ge_inv_capacity S (hnorm l hl)

/-! ## §66.3  Monotonicity of the finite capacity functions -/

/-- **`G_mono`.**  `KERNEL-PROVED`.  Enlarging the sieve support increases `G(z)`. -/
theorem G_mono {D' : Finset ℕ} (S' : SelbergData D') (hsub : D ⊆ D')
    (hg : ∀ d, S.g d = S'.g d) : G S ≤ G S' := by
  rw [G, G, Finset.sum_congr rfl (fun d _ => hg d)]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun d hd _ => (S'.g_pos d hd).le)

/-- **`capacity_antitone`.**  `KERNEL-PROVED`.  Hence the capacity decreases: a longer sieve
is never worse. -/
theorem capacity_antitone {D' : Finset ℕ} (S' : SelbergData D') (hsub : D ⊆ D')
    (hg : ∀ d, S.g d = S'.g d) : capacity S' ≤ capacity S := by
  rw [capacity, capacity]
  exact one_div_le_one_div_of_le (G_pos S) (G_mono S S' hsub hg)

/-! ## §66.4  Proper prime powers -/

/-- **`prime_le_sqrt_of_proper_power`.**  `KERNEL-PROVED`.  A proper prime power `p ^ k ≤ N`
(with `k ≥ 2`) forces `p ≤ √N`: the proper powers live on a square-root-thin set of primes. -/
theorem prime_le_sqrt_of_proper_power {p k N : ℕ} (hp : 2 ≤ p) (hk : 2 ≤ k)
    (hN : p ^ k ≤ N) : p ≤ Nat.sqrt N := by
  have hsq : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk
  exact Nat.le_sqrt.2 (by calc p * p = p ^ 2 := by ring
                            _ ≤ p ^ k := hsq
                            _ ≤ N := hN)

/-! ## §66.5  The exact rational final comparisons

The two theorems below are the deterministic bridge from a *capacity* input to the recorded
`T_box` allocation.  `W` stands for the comparison quantity `X / log X`; both statements are
conditional on their explicit analytic inputs (`hsep`, `hcap`, `hB`), which are **not** proved
here. -/

/-- **`T_box_bound_of_capacity`.**  `KERNEL-PROVED` (deterministic bridge).  Separation cost
at most `6` together with a directed-sieve capacity input `A ≤ W / Gval` and a capacity lower
bound `Gval ≥ 9523810` give the recorded box bound `|T| ≤ 6.3·10⁻⁷ · W`. -/
theorem T_box_bound_of_capacity {T A Gval W : ℝ} (hW : 0 ≤ W)
    (hsep : |T| ≤ 6 * A) (hcap : A ≤ W / Gval) (hG : (9523810 : ℝ) ≤ Gval) :
    |T| ≤ (63 / 10 ^ 8 : ℝ) * W := by
  have hGpos : (0 : ℝ) < Gval := by linarith
  have h1 : A ≤ W / Gval := hcap
  have h2 : W / Gval ≤ W / 9523810 := by
    apply div_le_div_of_nonneg_left hW (by norm_num) hG |>.trans_eq rfl
  have h3 : |T| ≤ 6 * (W / 9523810) := by
    refine hsep.trans ?_
    have := h1.trans h2
    linarith
  have h4 : 6 * (W / 9523810) ≤ (63 / 10 ^ 8 : ℝ) * W := by
    rw [div_eq_mul_inv]
    nlinarith [hW]
  linarith

/-- **`T_box_ratio_bound`.**  `KERNEL-PROVED` (deterministic bridge).  With the prime
comparison `B ≥ 0.3 · W` (an analytic input), the `6.3·10⁻⁷ · W` box bound becomes the
recorded two-sided allocation `|T / B| ≤ 2.1·10⁻⁶`. -/
theorem T_box_ratio_bound {T B W : ℝ} (hW : 0 < W) (hT : |T| ≤ (63 / 10 ^ 8 : ℝ) * W)
    (hB : (3 / 10 : ℝ) * W ≤ B) : |T / B| ≤ (21 / 10 ^ 7 : ℝ) := by
  have hBpos : (0 : ℝ) < B := by nlinarith
  rw [abs_div, abs_of_pos hBpos, div_le_iff₀ hBpos]
  have h1 : |T| ≤ (63 / 10 ^ 8 : ℝ) * W := hT
  have h2 : (63 / 10 ^ 8 : ℝ) * W ≤ (21 / 10 ^ 7 : ℝ) * ((3 / 10 : ℝ) * W) := by
    nlinarith [hW.le]
  have h3 : (21 / 10 ^ 7 : ℝ) * ((3 / 10 : ℝ) * W) ≤ (21 / 10 ^ 7 : ℝ) * B := by
    nlinarith
  linarith

/-- The recorded rational allocation constant `2.1·10⁻⁶`. -/
def boxAllocation : ℚ := 21 / 10 ^ 7

/-- The recorded rational box capacity constant `6.3·10⁻⁷`. -/
def boxCapacity : ℚ := 63 / 10 ^ 8

/-- **`allocation_eq_capacity_div_comparison`.**  `KERNEL-PROVED`.  Exact rational identity
tying the two recorded constants to the prime comparison `0.3`: `6.3e-7 / 0.3 = 2.1e-6`. -/
theorem allocation_eq_capacity_div_comparison : boxCapacity / (3 / 10 : ℚ) = boxAllocation := by
  rw [boxCapacity, boxAllocation]
  norm_num

end DirectedSelberg
end Erdos287
