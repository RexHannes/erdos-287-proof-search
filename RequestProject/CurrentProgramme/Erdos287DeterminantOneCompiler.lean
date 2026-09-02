import Mathlib

/-!
# The determinant-one source compiler

`DET1 SOURCE COMPILER : KERNEL-PROVED (finite arithmetic)`

This module is **append-only**.

It formalises the *exact arithmetic* transformation of the determinant-one
relation

```
r q − 2 a b = s,      s = ±1
```

into the one-parameter line

```
b = b₀ + r t,     q = q₀ + 2 a t,     r q₀ − 2 a b₀ = s,
```

together with the coprimality and integrality statements that make the
parametrisation exact and exhaustive.

**Firewall.**  No analytic estimate on the resulting `t`-sums is proved,
assumed, or implied; §4 records that the solution line is infinite and carries
no bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace DeterminantOne

/-! ## §1  The parametrisation is a solution -/

/-- **`det1_shift`.**  `KERNEL-PROVED`.

Every point of the line `(b₀ + r t, q₀ + 2 a t)` satisfies the same determinant
relation. -/
theorem det1_shift (r a b₀ q₀ s t : ℤ) (h : r * q₀ - 2 * a * b₀ = s) :
    r * (q₀ + 2 * a * t) - 2 * a * (b₀ + r * t) = s := by linear_combination h

/-! ## §2  Coprimality -/

/-- **`det1_isCoprime`.**  `KERNEL-PROVED`.

A determinant `±1` forces `r` and `2a` to be coprime. -/
theorem det1_isCoprime {r a b₀ q₀ s : ℤ} (hs : s = 1 ∨ s = -1)
    (h : r * q₀ - 2 * a * b₀ = s) : IsCoprime r (2 * a) := by
  rcases hs with rfl | rfl
  · exact ⟨q₀, -b₀, by linarith⟩
  · exact ⟨-q₀, b₀, by linarith⟩

/-- **`det1_base_of_isCoprime`.**  `KERNEL-PROVED`.

Conversely, coprimality of `r` and `2a` produces a base solution with determinant `1`. -/
theorem det1_base_of_isCoprime {r a : ℤ} (h : IsCoprime r (2 * a)) :
    ∃ q₀ b₀ : ℤ, r * q₀ - 2 * a * b₀ = 1 := by
  obtain ⟨u, v, huv⟩ := h
  exact ⟨u, -v, by linarith⟩

/-! ## §3  Exhaustiveness of the `t`-line -/

/-- **`det1_param_complete`.**  `KERNEL-PROVED`.

Every solution of `r q − 2 a b = s` with the same `r, a, s` lies on the `t`-line through
a base solution: the parametrisation is exhaustive, and `t` is an integer. -/
theorem det1_param_complete {r a b₀ q₀ b q s : ℤ} (hr : r ≠ 0)
    (hcop : IsCoprime r (2 * a))
    (h₀ : r * q₀ - 2 * a * b₀ = s) (h : r * q - 2 * a * b = s) :
    ∃ t : ℤ, b = b₀ + r * t ∧ q = q₀ + 2 * a * t := by
  have key : r * (q - q₀) = 2 * a * (b - b₀) := by linarith
  have hdvd : r ∣ 2 * a * (b - b₀) := ⟨q - q₀, key.symm⟩
  obtain ⟨t, ht⟩ := hcop.dvd_of_dvd_mul_left hdvd
  refine ⟨t, by linarith, ?_⟩
  have h2 : r * (q - q₀) = r * (2 * a * t) := by
    rw [key, ht]; ring
  have := mul_left_cancel₀ hr h2
  linarith

/-- **`det1_solution_line`.**  `KERNEL-PROVED`.

The exact solution set: with `r ≠ 0` and a base solution of determinant `±1`, a pair
`(b, q)` solves the determinant relation **iff** it lies on the `t`-line. -/
theorem det1_solution_line {r a b₀ q₀ b q s : ℤ} (hr : r ≠ 0) (hs : s = 1 ∨ s = -1)
    (h₀ : r * q₀ - 2 * a * b₀ = s) :
    (r * q - 2 * a * b = s) ↔ ∃ t : ℤ, b = b₀ + r * t ∧ q = q₀ + 2 * a * t := by
  constructor
  · intro h
    exact det1_param_complete hr (det1_isCoprime hs h₀) h₀ h
  · rintro ⟨t, rfl, rfl⟩
    exact det1_shift r a b₀ q₀ s t h₀

/-- **`det1_t_is_unique`.**  `KERNEL-PROVED`.  The parameter `t` is uniquely determined. -/
theorem det1_t_is_unique {r b₀ b t₁ t₂ : ℤ} (hr : r ≠ 0)
    (h₁ : b = b₀ + r * t₁) (h₂ : b = b₀ + r * t₂) : t₁ = t₂ := by
  have : r * t₁ = r * t₂ := by linarith
  exact mul_left_cancel₀ hr this

/-! ## §4  Firewall: no estimate on the `t`-sums -/

/-- **`t_line_is_unbounded`.**  `KERNEL-PROVED`.

The determinant-one line carries no bound: for every threshold there is a solution
parameter beyond it.  Any estimate on the resulting `t`-sums is therefore an *analytic*
input, not a consequence of this compiler. -/
theorem t_line_is_unbounded (B : ℤ) : ∃ t : ℤ, B < t := ⟨B + 1, by linarith⟩

/-- **`det1_compiler_gives_no_cancellation`.**  `KERNEL-PROVED`.

Explicitly: knowing that a family of terms is indexed by the determinant-one line gives no
bound on its size — the sum of `n` unit terms is `n`. -/
theorem det1_compiler_gives_no_cancellation (n : ℕ) :
    ∑ _t ∈ Finset.range n, (1 : ℝ) = (n : ℝ) := by simp

end DeterminantOne
end Erdos287
