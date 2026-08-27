import Mathlib

/-!
# Fixed-certificate transference — a purely finite/order-algebraic kernel

This file isolates the *logic* of a "fixed-certificate transference" argument as a
finite theorem over an arbitrary index type, with no number theory, no analysis and no
Ford–Maynard input whatsoever.  Everything here is kernel-checkable finite algebra.

## Setting

A finite index set `support` is partitioned into three finsets

* `P` — the certificate-positive region (`H = 1` there);
* `Ngood` — the good region (`H ≤ 0` there);
* `U` — the leakage region (no sign information).

Real weights `a b w : ι → ℝ` satisfy `w = a - b` and `0 ≤ a`, and `H : ι → ℝ` is the
comparison kernel.  With

* `B      = ∑_{p ∈ P} b p`,
* `Leak   = ∑_{n ∈ U} w n * H n`,
* `Total  = ∑_{n ∈ support} w n * H n`,

the exact finite identity

`∑_{p ∈ P} a p = B + Total − Leak − ∑_{n ∈ Ngood} (a n − b n) * H n`

together with `∑_{n ∈ Ngood} a n * H n ≤ 0` (from `a ≥ 0`, `H ≤ 0`) gives the
transference bound.

## Main results

* `Transference.sum_a_P_identity` — the exact partition identity;
* `Transference.sum_a_P_lower` — `∑_{p∈P} a p ≥ (1 + C) * B − 3E`;
* `Transference.sum_a_P_pos` — strict positivity when `E ≤ δ * B`, `0 < B` and
  `3 * δ < 1 + C`.

Nothing here asserts that any concrete certificate satisfies the hypotheses; those are
antecedents supplied by the caller.
-/

open scoped BigOperators

namespace Erdos287
namespace Transference

variable {ι : Type*} [DecidableEq ι]

/-- **Exact finite partition identity.**  With `w = a - b`, `H = 1` on `P`, and the
support split as `P ∪ Ngood ∪ U`, the certificate mass `∑_{p ∈ P} a p` equals
`B + Total − Leak − ∑_{Ngood} w·H`. -/
theorem sum_a_P_identity (P Ngood U : Finset ι) (a b w H : ι → ℝ)
    (hw : ∀ n, w n = a n - b n)
    (hHP : ∀ p ∈ P, H p = 1)
    (hPN : Disjoint P Ngood) (hPU : Disjoint P U) (hNU : Disjoint Ngood U) :
    ∑ p ∈ P, a p
      = (∑ p ∈ P, b p)
        + (∑ n ∈ (P ∪ Ngood ∪ U), w n * H n)
        - (∑ n ∈ U, w n * H n)
        - (∑ n ∈ Ngood, w n * H n) := by
  have hPNU : Disjoint (P ∪ Ngood) U := by
    simp [Finset.disjoint_union_left, hPU, hNU]
  rw [Finset.sum_union hPNU, Finset.sum_union hPN]
  have hP : ∑ n ∈ P, w n * H n = ∑ p ∈ P, a p - ∑ p ∈ P, b p := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [hHP p hp, hw p, mul_one]
  rw [hP]
  ring

/-- **Transference lower bound.**  Under the exact finite hypotheses

* `|Total| ≤ E`, `|Leak| ≤ E`,
* `∑_{Ngood} b·H ≥ C * B − E`,
* `0 ≤ a`, `H ≤ 0` on `Ngood`, `H = 1` on `P`,

one has `∑_{p ∈ P} a p ≥ (1 + C) * B − 3E`. -/
theorem sum_a_P_lower (P Ngood U : Finset ι) (a b w H : ι → ℝ) (Cc E : ℝ)
    (hw : ∀ n, w n = a n - b n)
    (ha : ∀ n, 0 ≤ a n)
    (hHP : ∀ p ∈ P, H p = 1)
    (hHN : ∀ n ∈ Ngood, H n ≤ 0)
    (hPN : Disjoint P Ngood) (hPU : Disjoint P U) (hNU : Disjoint Ngood U)
    (hTotal : |∑ n ∈ (P ∪ Ngood ∪ U), w n * H n| ≤ E)
    (hLeak : |∑ n ∈ U, w n * H n| ≤ E)
    (hGood : Cc * (∑ p ∈ P, b p) - E ≤ ∑ n ∈ Ngood, b n * H n) :
    (1 + Cc) * (∑ p ∈ P, b p) - 3 * E ≤ ∑ p ∈ P, a p := by
  set B := ∑ p ∈ P, b p with hB
  set Total := ∑ n ∈ (P ∪ Ngood ∪ U), w n * H n with hT
  set Leak := ∑ n ∈ U, w n * H n with hL
  have hid : ∑ p ∈ P, a p = B + Total - Leak - ∑ n ∈ Ngood, w n * H n :=
    sum_a_P_identity P Ngood U a b w H hw hHP hPN hPU hNU
  -- the good-region term
  have hsplit : ∑ n ∈ Ngood, w n * H n
      = (∑ n ∈ Ngood, a n * H n) - ∑ n ∈ Ngood, b n * H n := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro n _
    rw [hw n]; ring
  have haH : ∑ n ∈ Ngood, a n * H n ≤ 0 := by
    refine Finset.sum_nonpos ?_
    intro n hn
    exact mul_nonpos_of_nonneg_of_nonpos (ha n) (hHN n hn)
  have hgoodle : ∑ n ∈ Ngood, w n * H n ≤ - (Cc * B - E) := by
    rw [hsplit]
    have := hGood
    linarith
  have hT' : -E ≤ Total := by
    have := abs_le.1 hTotal; linarith [this.1]
  have hL' : Leak ≤ E := by
    have := abs_le.1 hLeak; linarith [this.2]
  rw [hid]
  linarith

/-- **Positive-mass specialization.**  If additionally `E ≤ δ * B` with `0 < B` and
`3δ < 1 + C`, the certificate mass is strictly positive, with the explicit bound
`∑_{p ∈ P} a p ≥ (1 + C − 3δ) * B > 0`. -/
theorem sum_a_P_pos (P Ngood U : Finset ι) (a b w H : ι → ℝ) (Cc E delta : ℝ)
    (hw : ∀ n, w n = a n - b n)
    (ha : ∀ n, 0 ≤ a n)
    (hHP : ∀ p ∈ P, H p = 1)
    (hHN : ∀ n ∈ Ngood, H n ≤ 0)
    (hPN : Disjoint P Ngood) (hPU : Disjoint P U) (hNU : Disjoint Ngood U)
    (hTotal : |∑ n ∈ (P ∪ Ngood ∪ U), w n * H n| ≤ E)
    (hLeak : |∑ n ∈ U, w n * H n| ≤ E)
    (hGood : Cc * (∑ p ∈ P, b p) - E ≤ ∑ n ∈ Ngood, b n * H n)
    (hBpos : 0 < ∑ p ∈ P, b p)
    (hE : E ≤ delta * (∑ p ∈ P, b p))
    (hdelta : 3 * delta < 1 + Cc) :
    0 < ∑ p ∈ P, a p ∧
      (1 + Cc - 3 * delta) * (∑ p ∈ P, b p) ≤ ∑ p ∈ P, a p := by
  have hlow := sum_a_P_lower P Ngood U a b w H Cc E hw ha hHP hHN hPN hPU hNU
    hTotal hLeak hGood
  set B := ∑ p ∈ P, b p with hB
  have hstep : (1 + Cc - 3 * delta) * B ≤ (1 + Cc) * B - 3 * E := by nlinarith
  have hpos : 0 < (1 + Cc - 3 * delta) * B := by nlinarith
  exact ⟨lt_of_lt_of_le hpos (le_trans hstep hlow), le_trans hstep hlow⟩

/-- Sanity instance: the hypotheses are simultaneously satisfiable in a nontrivial way
(so the transference theorems are not vacuous).  Take `P = {0}`, `Ngood = {1}`,
`U = ∅`, `a = 1`, `b = 1/2`, `H 0 = 1`, `H 1 = -1`, `E = 1`, `C = -1/2`. -/
theorem transference_nonvacuous :
    ∃ (P Ngood U : Finset ℕ) (a b w H : ℕ → ℝ) (Cc E : ℝ),
      (∀ n, w n = a n - b n) ∧ (∀ n, 0 ≤ a n) ∧ (∀ p ∈ P, H p = 1) ∧
      (∀ n ∈ Ngood, H n ≤ 0) ∧ Disjoint P Ngood ∧ Disjoint P U ∧ Disjoint Ngood U ∧
      |∑ n ∈ (P ∪ Ngood ∪ U), w n * H n| ≤ E ∧ |∑ n ∈ U, w n * H n| ≤ E ∧
      Cc * (∑ p ∈ P, b p) - E ≤ ∑ n ∈ Ngood, b n * H n ∧ 0 < ∑ p ∈ P, b p := by
  refine ⟨{0}, {1}, ∅, fun _ => 1, fun _ => (1 : ℝ)/2, fun _ => 1/2,
    fun n => if n = 0 then 1 else -1, -1/2, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num

end Transference
end Erdos287
