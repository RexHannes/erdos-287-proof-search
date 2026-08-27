import Mathlib
import RequestProject.Erdos287.AffineMuLogHardSource

/-!
# V15, Part 4 — the determinant-one affine line of the hard `μ`-log source

Pure integer algebra for the relation carried by every pair in the hard class,

`q * r − 2 * m * n = s`,  `s = ±1`,

with the sign represented by the V14 `AffineSign` convention (`AffineSign.val = ±1`), so
that no `Nat` subtraction ever occurs.

* `affine_mulog_r_ne_zero`, `affine_mulog_q_ne_zero` — nonvanishing is **proved** from the
  unit shift (the left side would otherwise be even), not assumed;
* `affine_mulog_coprime` — `gcd(r, 2m) = 1`, and the symmetric `gcd(q, 2n) = 1`;
* `affine_mulog_line_forward` — every point of the line is a solution;
* `affine_mulog_line_reverse` — every solution lies on the line;
* `affine_mulog_line_iff` — the two together, as an iff;
* `affine_mulog_line_parameter_unique` — multiplicity one for the parameter `t`.

This supersedes the need to use the V14 prime-modulus line as *the* source-minimal
determinant identity; the V14 line (`Erdos287.TwoOuter.affine_det_one_line_param`) remains
a valid alternative decomposition and is untouched.

Ledger: `AFFINE287-MULOG-LINE45 : PROVED_ALGEBRAIC`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace MuLog

open Erdos287.Vaughan

/-! ## Nonvanishing -/

/-- If `q r − 2 m n = ±1` then `r ≠ 0`: otherwise the left-hand side would be even. -/
theorem affine_mulog_r_ne_zero {q r m n s : ℤ} (h : q * r - 2 * m * n = s)
    (hs : s = 1 ∨ s = -1) : r ≠ 0 := by
  rintro rfl
  have h2 : (2 : ℤ) ∣ s := ⟨-(m * n), by linarith [h]⟩
  rcases hs with rfl | rfl <;> norm_num at h2

/-- Symmetrically, `q ≠ 0`. -/
theorem affine_mulog_q_ne_zero {q r m n s : ℤ} (h : q * r - 2 * m * n = s)
    (hs : s = 1 ∨ s = -1) : q ≠ 0 := by
  rintro rfl
  have h2 : (2 : ℤ) ∣ s := ⟨-(m * n), by linarith [h]⟩
  rcases hs with rfl | rfl <;> norm_num at h2

/-! ## Coprimality -/

/-- **`affine_mulog_coprime`** — the unit shift forces `gcd(r, 2m) = 1`. -/
theorem affine_mulog_coprime {q r m n s : ℤ} (h : q * r - 2 * m * n = s)
    (hs : s = 1 ∨ s = -1) : IsCoprime r (2 * m) := by
  rcases hs with rfl | rfl
  · exact ⟨q, -n, by linarith [h]⟩
  · exact ⟨-q, n, by linarith [h]⟩

/-- The symmetric consequence `gcd(q, 2n) = 1`. -/
theorem affine_mulog_coprime_symm {q r m n s : ℤ} (h : q * r - 2 * m * n = s)
    (hs : s = 1 ∨ s = -1) : IsCoprime q (2 * n) := by
  rcases hs with rfl | rfl
  · exact ⟨r, -m, by linarith [h]⟩
  · exact ⟨-r, m, by linarith [h]⟩

/-- The `AffineSign` form of the coprimality statement, matching the shape in which hard
pairs arise (`pairHard_affine_det_one`). -/
theorem affine_mulog_coprime_sign {q r m n : ℤ} {sg : AffineSign}
    (h : q * r - 2 * m * n = sg.val) : IsCoprime r (2 * m) :=
  affine_mulog_coprime h (sg.val_eq_one_or)

/-! ## The line -/

/-- **`affine_mulog_line_forward`** — every point of the line is a solution. -/
theorem affine_mulog_line_forward {q0 r m n0 s : ℤ} (h : q0 * r - 2 * m * n0 = s) (t : ℤ) :
    (q0 + 2 * m * t) * r - 2 * m * (n0 + r * t) = s := by
  linear_combination h

/-- **`affine_mulog_line_reverse`** — every solution lies on the line. -/
theorem affine_mulog_line_reverse {q0 q r m n0 n s : ℤ} (hs : s = 1 ∨ s = -1)
    (h0 : q0 * r - 2 * m * n0 = s) (h : q * r - 2 * m * n = s) :
    ∃ t : ℤ, q = q0 + 2 * m * t ∧ n = n0 + r * t := by
  have hr : r ≠ 0 := affine_mulog_r_ne_zero h0 hs
  have hcop : IsCoprime r (2 * m) := affine_mulog_coprime h0 hs
  have key : (q - q0) * r = 2 * m * (n - n0) := by linarith
  have hdvd : r ∣ 2 * m * (n - n0) := ⟨q - q0, by linarith [key]⟩
  have hn : r ∣ (n - n0) := hcop.dvd_of_dvd_mul_left hdvd
  obtain ⟨t, ht⟩ := hn
  refine ⟨t, ?_, by linarith [ht]⟩
  have hq : (q - q0) * r = (2 * m * t) * r := by
    rw [key, ht]; ring
  have := mul_right_cancel₀ hr hq
  linarith [this]

/-- **`affine_mulog_line_iff`** — `PROVED_ALGEBRAIC`.

For a unit shift `s = ±1` and a base solution `(q₀, n₀)`, the integer solutions of
`q r − 2 m n = s` (with `r`, `m` fixed) are **exactly** the points of the determinant-one
line. -/
theorem affine_mulog_line_iff {q0 r m n0 s : ℤ} (hs : s = 1 ∨ s = -1)
    (h0 : q0 * r - 2 * m * n0 = s) (q n : ℤ) :
    (q * r - 2 * m * n = s) ↔ ∃ t : ℤ, q = q0 + 2 * m * t ∧ n = n0 + r * t := by
  constructor
  · intro h
    exact affine_mulog_line_reverse hs h0 h
  · rintro ⟨t, rfl, rfl⟩
    exact affine_mulog_line_forward h0 t

/-- **`affine_mulog_line_parameter_unique`** — multiplicity one: the line parameter is
determined by the solution. -/
theorem affine_mulog_line_parameter_unique {q0 r m n0 s : ℤ} (hs : s = 1 ∨ s = -1)
    (h0 : q0 * r - 2 * m * n0 = s) {t t' : ℤ}
    (h : (q0 + 2 * m * t = q0 + 2 * m * t' ∧ n0 + r * t = n0 + r * t')) : t = t' := by
  have hr : r ≠ 0 := affine_mulog_r_ne_zero h0 hs
  have : r * t = r * t' := by linarith [h.2]
  exact mul_left_cancel₀ hr this

/-- The `AffineSign` package of the line description, in the exact shape produced by
`pairHard_affine_det_one`. -/
theorem affine_mulog_line_iff_sign {q0 r m n0 : ℤ} {sg : AffineSign}
    (h0 : q0 * r - 2 * m * n0 = sg.val) (q n : ℤ) :
    (q * r - 2 * m * n = sg.val) ↔ ∃ t : ℤ, q = q0 + 2 * m * t ∧ n = n0 + r * t :=
  affine_mulog_line_iff sg.val_eq_one_or h0 q n

end MuLog
end Erdos287
