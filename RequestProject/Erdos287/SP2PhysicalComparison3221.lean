import Mathlib
import RequestProject.Erdos287.AffineVaughanIdentity
import RequestProject.Erdos287.SP2DirectSourceAdapter3221

/-!
# V23, §2 — the direct SP-2 one-sign *physical* Balanced7 comparison object

`BALANCED7-SP2-PHYSICAL-COMPARISON45`

## The literal object

Reusing the direct SP-2 source layer (`SP2DirectSourceAdapter3221`), the one-sign physical
Balanced7 comparison is the literal expression

```
    −20 · ∑_{pvec} Ω(pvec) · [ Λ(2P + s) − 2B(P) ],      P = ∏_i pvec_i,
```

where

* `−20 = ∑_{j ≤ 3} (−1)^j C(7,j)` is the SP-2 alternating divisor-depth coefficient, already
  proved in `Erdos287.SP2Source.sp2_balancedSeven_coefficient_eq_neg20`;
* `pvec` ranges over the finite physical seven-prime cell;
* `Λ` is Mathlib's genuine `ArithmeticFunction.vonMangoldt`;
* `2P + s` is the V14 sign-firewalled affine argument `affineNat s 1 P` (no `Nat`
  subtraction ever appears in a statement; `affineNat_cast` is the only interface);
* `B` is the *physical* singular-series datum, carried as a field of the cell and **not**
  defined here from any Euler product.

## Independence firewall

This object is deliberately **not** defined from the factorial `q`-cell of
`FactorialEulerPolarization` / `PrincipalQCell3221`.  The two definitions stay independent;
the only bridge between them is the pointwise principal-cell equality proved separately in
`PrincipalQCell3221.lean`, and — per the independent audit verdict `CASE F —
SOURCE-MISSING` — the identification of `B` with an independently defined physical `2B(P)`
is *not* supplied here: it is the uninhabited interface
`SP2PhysicalTwoBIndependent287Input`.

Nothing in this file is analytic.  Nothing here proves Balanced7 or Erdős #287.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ArithmeticFunction
open scoped BigOperators

namespace Erdos287
namespace V23Comparison

open Erdos287.Vaughan

/-! ## §2.1  The physical cell datum -/

/-- **`SP2PhysicalCell`** — the finite data of the one-sign physical comparison.

`cell` is the finite family of seven-prime vectors, `Om` the physical weight `Ω(pvec)` and
`B` the physical singular-series datum `P ↦ B(P)`.  All three are *given*; none of them is
manufactured from the factorial `q`-cell. -/
structure SP2PhysicalCell where
  /-- The finite family of physical seven-prime vectors. -/
  cell : Finset (Fin 7 → ℕ)
  /-- The physical weight `Ω(pvec)`. -/
  Om : (Fin 7 → ℕ) → ℝ
  /-- The physical singular-series datum `B(P)`. -/
  B : ℕ → ℝ

/-- The physical modulus attached to a seven-prime vector, `P = ∏_i pvec_i`. -/
def physModulus (pv : Fin 7 → ℕ) : ℕ := ∏ i, pv i

/-- The SP-2 alternating divisor-depth coefficient, `−20`. -/
def sp2AlternatingCoefficient : ℤ := -20

/-- The coefficient really is the SP-2 depth sum `∑_{j≤3} (−1)^j C(7,j)`. -/
theorem sp2AlternatingCoefficient_eq_depthSum :
    (sp2AlternatingCoefficient : ℤ)
      = ∑ j ∈ Finset.range 4, (-1 : ℤ) ^ j * (Nat.choose 7 j : ℤ) :=
  (Erdos287.SP2Source.sp2_balancedSeven_coefficient_eq_neg20).symm

/-! ## §2.2  The comparison object -/

/-- **`SP2BalancedSevenPhysicalComparison`** — the literal one-sign physical comparison

```
    −20 · ∑_{pvec ∈ cell} Ω(pvec) · [ Λ(2P + s) − 2B(P) ].
```
-/
noncomputable def SP2BalancedSevenPhysicalComparison
    (C : SP2PhysicalCell) (s : AffineSign) : ℝ :=
  (-20 : ℝ) * ∑ pv ∈ C.cell, C.Om pv *
    (vonMangoldt (affineNat s 1 (physModulus pv)) - 2 * C.B (physModulus pv))

/-- The affine argument of the comparison is literally `2P + s`. -/
theorem sp2PhysicalComparison_arg (s : AffineSign) {pv : Fin 7 → ℕ}
    (hP : 1 ≤ physModulus pv) :
    ((affineNat s 1 (physModulus pv) : ℕ) : ℤ) = 2 * (physModulus pv : ℤ) + s.val := by
  simpa using affineNat_cast s (le_refl 1) hP

/-- **`sp2PhysicalComparison_split`.**  `LEAN_PROVED`.

The comparison splits into its `Λ`-channel and its `2B`-channel:

```
    −20 ∑ Ω Λ(2P+s)  +  40 ∑ Ω B(P).
```
-/
theorem sp2PhysicalComparison_split (C : SP2PhysicalCell) (s : AffineSign) :
    SP2BalancedSevenPhysicalComparison C s
      = (-20 : ℝ) * (∑ pv ∈ C.cell, C.Om pv * vonMangoldt (affineNat s 1 (physModulus pv)))
        + (40 : ℝ) * (∑ pv ∈ C.cell, C.Om pv * C.B (physModulus pv)) := by
  simp only [SP2BalancedSevenPhysicalComparison, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun pv _ => by ring

/-- **`sp2PhysicalComparison_eq_zero_of_pointwise_match`.**  `LEAN_PROVED`.

If the physical `Λ`-value matches `2B(P)` on every vector of the cell, the one-sign
comparison vanishes.  This is the *shape* of the intended conclusion; nothing here supplies
the hypothesis. -/
theorem sp2PhysicalComparison_eq_zero_of_pointwise_match
    (C : SP2PhysicalCell) (s : AffineSign)
    (h : ∀ pv ∈ C.cell,
      vonMangoldt (affineNat s 1 (physModulus pv)) = 2 * C.B (physModulus pv)) :
    SP2BalancedSevenPhysicalComparison C s = 0 := by
  rw [SP2BalancedSevenPhysicalComparison, Finset.sum_congr rfl
    (fun pv hpv => by rw [h pv hpv]; ring : ∀ pv ∈ C.cell, C.Om pv *
      (vonMangoldt (affineNat s 1 (physModulus pv)) - 2 * C.B (physModulus pv)) = 0)]
  simp

/-- **`sp2PhysicalComparison_bound`.**  `LEAN_PROVED`.

A pointwise discrepancy bound transports to the comparison with the explicit constant
`20 · ∑ |Ω|`. -/
theorem sp2PhysicalComparison_bound (C : SP2PhysicalCell) (s : AffineSign) (eps : ℝ)
    (h : ∀ pv ∈ C.cell,
      |vonMangoldt (affineNat s 1 (physModulus pv)) - 2 * C.B (physModulus pv)| ≤ eps) :
    |SP2BalancedSevenPhysicalComparison C s| ≤ 20 * eps * ∑ pv ∈ C.cell, |C.Om pv| := by
  have key : |∑ pv ∈ C.cell, C.Om pv *
        (vonMangoldt (affineNat s 1 (physModulus pv)) - 2 * C.B (physModulus pv))|
      ≤ ∑ pv ∈ C.cell, eps * |C.Om pv| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun pv hpv => ?_)
    rw [abs_mul]
    calc |C.Om pv| * |vonMangoldt (affineNat s 1 (physModulus pv)) - 2 * C.B (physModulus pv)|
        ≤ |C.Om pv| * eps := mul_le_mul_of_nonneg_left (h pv hpv) (abs_nonneg _)
      _ = eps * |C.Om pv| := mul_comm _ _
  rw [SP2BalancedSevenPhysicalComparison, abs_mul, show |(-20 : ℝ)| = 20 by norm_num]
  calc (20 : ℝ) * |∑ pv ∈ C.cell, C.Om pv *
          (vonMangoldt (affineNat s 1 (physModulus pv)) - 2 * C.B (physModulus pv))|
      ≤ 20 * ∑ pv ∈ C.cell, eps * |C.Om pv| := by
        exact mul_le_mul_of_nonneg_left key (by norm_num)
    _ = 20 * eps * ∑ pv ∈ C.cell, |C.Om pv| := by rw [← Finset.mul_sum]; ring

/-! ## §2.3  Non-vacuity -/

/-- **`sp2PhysicalComparison_not_automatically_zero`.**  `LEAN_PROVED`.

The comparison object is a genuine quantity, not a tautologically vanishing one: on an
explicit one-vector cell with `B ≡ 0` it is `−20 · Λ(3) ≠ 0`. -/
theorem sp2PhysicalComparison_not_automatically_zero :
    ∃ (C : SP2PhysicalCell) (s : AffineSign),
      SP2BalancedSevenPhysicalComparison C s ≠ 0 := by
  classical
  refine ⟨⟨{fun _ => 1}, fun _ => 1, fun _ => 0⟩, AffineSign.plus, ?_⟩
  have hP : physModulus (fun _ => 1) = 1 := by
    simp [physModulus]
  have harg : affineNat AffineSign.plus 1 (physModulus (fun _ => 1)) = 3 := by
    rw [hP]; rfl
  rw [SP2BalancedSevenPhysicalComparison, Finset.sum_singleton, harg]
  have h3 : vonMangoldt 3 ≠ 0 := by
    rw [ne_eq, ArithmeticFunction.vonMangoldt_eq_zero_iff]
    exact fun h => h (Nat.Prime.isPrimePow (by norm_num))
  simpa using h3

/-! ## §2.4  Independence of the factorial `q`-cell

The definition above mentions only `vonMangoldt`, the cell, the weight `Om` and the field
`B`.  In particular the value of the comparison is unchanged by *any* modification of the
factorial machinery, and conversely two cells that differ only in `B` give different
comparisons.  The following is the machine-checkable form of "the physical object is not
defined from the factorial `q`-cell": it is determined by, and sensitive to, its own data
alone. -/
theorem sp2PhysicalComparison_congr {C D : SP2PhysicalCell} {s : AffineSign}
    (hcell : C.cell = D.cell) (hOm : ∀ pv, C.Om pv = D.Om pv) (hB : ∀ P, C.B P = D.B P) :
    SP2BalancedSevenPhysicalComparison C s = SP2BalancedSevenPhysicalComparison D s := by
  rw [SP2BalancedSevenPhysicalComparison, SP2BalancedSevenPhysicalComparison, hcell]
  refine congrArg _ (Finset.sum_congr rfl fun pv _ => ?_)
  rw [hOm pv, hB (physModulus pv)]

/-- Changing only the physical `B`-datum changes the comparison: the `2B` channel is
genuinely present, so a comparison theorem cannot be insensitive to which `B` is used. -/
theorem sp2PhysicalComparison_sensitive_to_B :
    ∃ (C D : SP2PhysicalCell) (s : AffineSign),
      C.cell = D.cell ∧ (∀ pv, C.Om pv = D.Om pv) ∧
        SP2BalancedSevenPhysicalComparison C s ≠ SP2BalancedSevenPhysicalComparison D s := by
  classical
  refine ⟨⟨{fun _ => 1}, fun _ => 1, fun _ => 0⟩, ⟨{fun _ => 1}, fun _ => 1, fun _ => 1⟩,
    AffineSign.plus, rfl, fun _ => rfl, ?_⟩
  have hP : physModulus (fun _ => 1) = 1 := by simp [physModulus]
  have harg : affineNat AffineSign.plus 1 (physModulus (fun _ : Fin 7 => 1)) = 3 := by
    rw [hP]; rfl
  simp only [SP2BalancedSevenPhysicalComparison, Finset.sum_singleton, harg]
  intro h
  norm_num at h
  linarith

end V23Comparison
end Erdos287
