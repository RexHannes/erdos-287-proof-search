import Mathlib
import RequestProject.Erdos287.RankThreeOperator

/-!
# Erdős #287 effectivity — primitive projection and the rank-three cell reduction (§62)

```
SAWTOOTH MULTIPLICATION (RAABE) IDENTITY : KERNEL-PROVED
PRIMITIVE PROJECTION A_{1,f}(k,z)        : KERNEL-PROVED DEFINITION
FINITE PROJECTION NORM INTERFACE         : KERNEL-PROVED
RANK-THREE CELL REDUCTION                : KERNEL-PROVED
EXTREMUM ON FINITELY MANY CELLS          : KERNEL-PROVED
```

The multiplication (Raabe) identity for the strict sawtooth is

    ∑_{j < m} {x + j/m} = {m x} + (m−1)/2.

The primitive projection at conductor `f` is the Möbius-weighted shift average

    P_f[F](y) = ∑_{d ∣ f} μ(f/d) · (1/d) ∑_{j < d} F(y + j/d),
    A_{1,f}(k,z) = P_f[Δ_k](z/k),

and `projection_norm_interface` is the exact finite bound `|P_f[F](y)| ≤ τ(f)·M` for any
pointwise bound `M` on `F`.

`rankThree_cell_reduction` is the key finiteness statement: `Δ_k(x) − φ(k)x` depends on `x`
only through the integer cell `⌊k x⌋₊`, so the extremum of the one-coordinate constant over
`[0,1)` is attained on the `k` rational cells `[j/k, (j+1)/k)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §62.1  The sawtooth multiplication identity -/

/-- The shifted sawtooth sum `S_m(x) = ∑_{j<m} {x + j/m}`. -/
noncomputable def fractShiftSum (m : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range m, Int.fract (x + (j : ℝ) / (m : ℝ))

lemma fractShiftSum_shift {m : ℕ} (hm : 0 < m) (x : ℝ) :
    fractShiftSum m (x + 1 / (m : ℝ)) = fractShiftSum m x := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hM0 : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by
    push_cast
    positivity
  set g : ℕ → ℝ := fun j => Int.fract (x + (j : ℝ) / ((n + 1 : ℕ) : ℝ)) with hg
  have hL : fractShiftSum (n + 1) (x + 1 / ((n + 1 : ℕ) : ℝ))
      = ∑ j ∈ Finset.range (n + 1), g (j + 1) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hg]
    congr 1
    push_cast
    field_simp
    ring
  have hR : fractShiftSum (n + 1) x = ∑ j ∈ Finset.range (n + 1), g j := rfl
  have hgtop : g (n + 1) = g 0 := by
    have h1 : x + (((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) = x + 1 := by
      field_simp
    have h2 : x + (((0 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) = x := by simp
    rw [hg]
    simp only
    rw [h1, h2, Int.fract_add_one]
  rw [hL, hR, Finset.sum_range_succ (fun j => g (j + 1)) n, Finset.sum_range_succ' g n, hgtop]

lemma fractShiftSum_shift_int {m : ℕ} (hm : 0 < m) (x : ℝ) (n : ℤ) :
    fractShiftSum m (x + (n : ℝ) / (m : ℝ)) = fractShiftSum m x := by
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih =>
      have hstep : x + (((i : ℤ) + 1 : ℤ) : ℝ) / (m : ℝ)
          = (x + ((i : ℤ) : ℝ) / (m : ℝ)) + 1 / (m : ℝ) := by
        push_cast
        ring
      rw [hstep, fractShiftSum_shift hm, ih]
  | pred i ih =>
      have hstep : (x + ((-(i : ℤ) - 1 : ℤ) : ℝ) / (m : ℝ)) + 1 / (m : ℝ)
          = x + ((-(i : ℤ) : ℤ) : ℝ) / (m : ℝ) := by
        push_cast
        ring
      have h := fractShiftSum_shift hm (x + ((-(i : ℤ) - 1 : ℤ) : ℝ) / (m : ℝ))
      rw [hstep] at h
      rw [← h, ih]

lemma fractShiftSum_fundamental {m : ℕ} (hm : 0 < m) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x < 1 / (m : ℝ)) :
    fractShiftSum m x = (m : ℝ) * x + ((m : ℝ) - 1) / 2 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hterm : ∀ j ∈ Finset.range m,
      Int.fract (x + (j : ℝ) / (m : ℝ)) = x + (j : ℝ) / (m : ℝ) := by
    intro j hj
    rw [Finset.mem_range] at hj
    refine Int.fract_eq_self.2 ⟨by positivity, ?_⟩
    have hjm : ((j : ℝ)) ≤ (m : ℝ) - 1 := by
      have : (j : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hj
      linarith
    have h1 : (j : ℝ) / (m : ℝ) ≤ ((m : ℝ) - 1) / (m : ℝ) := by gcongr
    have h2 : ((m : ℝ) - 1) / (m : ℝ) = 1 - 1 / (m : ℝ) := by field_simp
    linarith [h2 ▸ h1]
  have hsumNat : (∑ j ∈ Finset.range m, j) * 2 = m * (m - 1) := Finset.sum_range_id_mul_two m
  have hsum : ∑ j ∈ Finset.range m, (j : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
    have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      have h1 : 1 ≤ m := hm
      push_cast [Nat.cast_sub h1]
      ring
    have h2 : (∑ j ∈ Finset.range m, (j : ℝ)) * 2 = (m : ℝ) * ((m : ℝ) - 1) := by
      have hc := congrArg (fun t : ℕ => (t : ℝ)) hsumNat
      push_cast at hc
      rw [hm1] at hc
      exact hc
    linarith
  rw [fractShiftSum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, ← Finset.sum_div, hsum]
  field_simp

/-- **`sawtooth_multiplication`.**  `KERNEL-PROVED`.  The multiplication (Raabe) identity
`∑_{j<m} {x + j/m} = {m x} + (m−1)/2`. -/
theorem sawtooth_multiplication {m : ℕ} (hm : 0 < m) (x : ℝ) :
    fractShiftSum m x = Int.fract ((m : ℝ) * x) + ((m : ℝ) - 1) / 2 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = ⌊(m : ℝ) * x⌋ := ⟨_, rfl⟩
  have hfr : Int.fract ((m : ℝ) * x) = (m : ℝ) * x - (n : ℝ) := by
    rw [hn, Int.fract]
  have key := fractShiftSum_shift_int hm (x - (n : ℝ) / (m : ℝ)) n
  have hxx : x - (n : ℝ) / (m : ℝ) + (n : ℝ) / (m : ℝ) = x := by ring
  rw [hxx] at key
  have hmx0 : (m : ℝ) * (x - (n : ℝ) / (m : ℝ)) = (m : ℝ) * x - (n : ℝ) := by
    field_simp
  have h0 : 0 ≤ (m : ℝ) * (x - (n : ℝ) / (m : ℝ)) := by
    rw [hmx0, ← hfr]
    exact Int.fract_nonneg _
  have h1 : (m : ℝ) * (x - (n : ℝ) / (m : ℝ)) < 1 := by
    rw [hmx0, ← hfr]
    exact Int.fract_lt_one _
  have hx00 : 0 ≤ x - (n : ℝ) / (m : ℝ) := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have hx01 : x - (n : ℝ) / (m : ℝ) < 1 / (m : ℝ) := by
    rw [lt_div_iff₀ hmR]
    nlinarith
  rw [key, fractShiftSum_fundamental hm hx00 hx01, hmx0, hfr]

/-! ## §62.2  The primitive projection -/

/-- The shift average `(1/d) ∑_{j<d} F(y + j/d)`. -/
noncomputable def shiftAverage (d : ℕ) (F : ℝ → ℝ) (y : ℝ) : ℝ :=
  (1 / (d : ℝ)) * ∑ j ∈ Finset.range d, F (y + (j : ℝ) / (d : ℝ))

/-- The primitive projection at conductor `f`. -/
noncomputable def primitiveProjection (f : ℕ) (F : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∑ d ∈ f.divisors, ((ArithmeticFunction.moebius (f / d) : ℤ) : ℝ) * shiftAverage d F y

/-- `A_{1,f}(k,z) = P_f[Δ_k](z/k)`. -/
noncomputable def AoneProj (f k : ℕ) (z : ℝ) : ℝ :=
  primitiveProjection f (DeltaOp k) (z / (k : ℝ))

/-- **`shiftAverage_norm`.**  `KERNEL-PROVED`.  Pointwise bound for the shift average. -/
theorem shiftAverage_norm {d : ℕ} (hd : 0 < d) {F : ℝ → ℝ} {M : ℝ} (hM : ∀ t, |F t| ≤ M)
    (y : ℝ) : |shiftAverage d F y| ≤ M := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  rw [shiftAverage, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (d : ℝ))]
  have hsum : |∑ j ∈ Finset.range d, F (y + (j : ℝ) / (d : ℝ))| ≤ (d : ℝ) * M := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range d) => hM (y + (j : ℝ) / (d : ℝ)))
    simpa [Finset.sum_const, Finset.card_range, mul_comm] using h
  calc 1 / (d : ℝ) * |∑ j ∈ Finset.range d, F (y + (j : ℝ) / (d : ℝ))|
      ≤ 1 / (d : ℝ) * ((d : ℝ) * M) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = M := by field_simp

/-- **`projection_norm_interface`.**  `KERNEL-PROVED`.  The exact finite projection norm
interface: `|P_f[F](y)| ≤ τ(f)·M` for any pointwise bound `M`. -/
theorem projection_norm_interface (f : ℕ) {F : ℝ → ℝ} {M : ℝ}
    (hM : ∀ t, |F t| ≤ M) (y : ℝ) :
    |primitiveProjection f F y| ≤ (f.divisors.card : ℝ) * M := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  rw [primitiveProjection]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ d ∈ f.divisors,
      |((ArithmeticFunction.moebius (f / d) : ℤ) : ℝ) * shiftAverage d F y| ≤ M := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    rw [abs_mul]
    have hmu : |((ArithmeticFunction.moebius (f / d) : ℤ) : ℝ)| ≤ 1 := by
      rcases eq_or_ne (ArithmeticFunction.moebius (f / d)) 0 with h0 | h0
      · rw [h0]; norm_num
      · rcases ArithmeticFunction.moebius_ne_zero_iff_eq_or.1 h0 with h1 | h1 <;>
          rw [h1] <;> norm_num
    calc |((ArithmeticFunction.moebius (f / d) : ℤ) : ℝ)| * |shiftAverage d F y|
        ≤ 1 * M := mul_le_mul hmu (shiftAverage_norm hd0 hM y) (abs_nonneg _) (by norm_num)
      _ = M := one_mul M
  calc ∑ d ∈ f.divisors, |((ArithmeticFunction.moebius (f / d) : ℤ) : ℝ) * shiftAverage d F y|
      ≤ ∑ _d ∈ f.divisors, M := Finset.sum_le_sum hterm
    _ = (f.divisors.card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ## §62.3  The rank-three cell reduction -/

/-- The value of the rank-three discrepancy on the cell `⌊k x⌋₊ = j`. -/
noncomputable def cellValue (k j : ℕ) : ℝ :=
  - (((Finset.Icc 1 j).filter (fun n => Nat.Coprime n k)).card : ℝ)

/-- **`rankThree_cell_reduction`.**  `KERNEL-PROVED`.  `Δ_k(x) − φ(k)x` depends on `x` only
through the integer cell `⌊k x⌋₊`. -/
theorem rankThree_cell_reduction {k : ℕ} (hk : 1 < k) {x : ℝ} (hx : 0 ≤ x) :
    DeltaOp k x - (Nat.totient k : ℝ) * x = cellValue k ⌊(k : ℝ) * x⌋₊ := by
  rw [DeltaOp_discrepancy_identity hk hx, cellValue, coprimeCount]
  ring

/-- **`rankThree_extremum_finitely_many_cells`.**  `KERNEL-PROVED`.  On the fundamental
interval `[0,1)` the rank-three discrepancy takes at most `k` values, indexed by the rational
cells `[j/k, (j+1)/k)`: the extremum problem is finite. -/
theorem rankThree_extremum_finitely_many_cells {k : ℕ} (hk : 1 < k) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x < 1) :
    ∃ j < k, DeltaOp k x - (Nat.totient k : ℝ) * x = cellValue k j := by
  refine ⟨⌊(k : ℝ) * x⌋₊, ?_, rankThree_cell_reduction hk hx0⟩
  have hkR : (0 : ℝ) < (k : ℝ) := by
    have hkpos : 0 < k := by omega
    exact_mod_cast hkpos
  have hlt : (k : ℝ) * x < (k : ℝ) := by nlinarith
  rw [Nat.floor_lt (by positivity : (0 : ℝ) ≤ (k : ℝ) * x)]
  exact_mod_cast hlt

end Effectivity
end Erdos287
