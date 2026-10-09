import Mathlib
import RequestProject.Erdos287.ProperGammaMultiplicityGeometry

/-!
# Erdős #287 effectivity — the `m = q n` product change of variables (§37)

```
m = q n LATTICE CHANGE OF VARIABLES : KERNEL-PROVED
m > z LOWER-CUTOFF FIREWALL         : KERNEL-PROVED
COMPLEMENTARY n GEOMETRY            : KERNEL-PROVED (reconstructed thresholds)
ARITHMETIC / GEOMETRIC SEPARATION   : KERNEL-PROVED
ERDŐS #287                          : OPEN
```

The discrete part of `I_X(z,q)` runs over the multiples of `q` in the window

    z < m ≤ 0.9 R.

Setting `m = q n` the *correct* transformed range is

    z < q n ≤ 0.9 R,

i.e. the lower cutoff `m > z` is retained (`product_resummation`).  Dropping it changes the
source (`lower_cutoff_matters`): the two sums differ already in a two-term example.

The complementary `n`-geometry of the survivor region is recorded exactly: the band index of
an `N ≥ 7` configuration is never `≤ 21` (`bandIndex_ge_22`), the indices `22, 23, 24` are the
exceptional finite geometry (`bandIndex_exceptional`), and from `25` on one is in the merged
chain regime `t ≤ 9/310` (`bandIndex_chain`).  The arithmetic side conditions
(`n ∣ m`, `q = m/n > 200`, `q` odd squarefree, `(q,z) = 1`, `m > z`) are kept in a **separate**
predicate `FibreArithmetic`, and `geometry_not_arithmetic` shows the geometric band condition
does not imply them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §37.1  The discrete windows -/

/-- The discrete `m`-window of `I_X(z,q)`: multiples of `q` with `z < m ≤ M`. -/
def discreteRange (z M q : ℕ) : Finset ℕ :=
  Finset.filter (fun m => q ∣ m ∧ z < m) (Finset.Icc 1 M)

/-- The same window **without** the lower cutoff `m > z`. -/
def discreteRangeNoCutoff (M q : ℕ) : Finset ℕ := Finset.filter (fun m => q ∣ m) (Finset.Icc 1 M)

/-- The transformed `n`-window after `m = q n`: `z < q n ≤ M`. -/
def fibreRange (z M q : ℕ) : Finset ℕ :=
  Finset.filter (fun n => z < q * n ∧ q * n ≤ M) (Finset.Icc 1 M)

theorem mem_discreteRange {z M q m : ℕ} :
    m ∈ discreteRange z M q ↔ (q ∣ m ∧ z < m ∧ m ≤ M) := by
  simp only [discreteRange, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨-, h2⟩, h3, h4⟩; exact ⟨h3, h4, h2⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by omega, h3⟩, h1, h2⟩

theorem mem_fibreRange {z M q n : ℕ} (hq : 0 < q) :
    n ∈ fibreRange z M q ↔ (z < q * n ∧ q * n ≤ M) := by
  simp only [fibreRange, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨-, h⟩; exact h
  · rintro ⟨h1, h2⟩
    refine ⟨⟨?_, ?_⟩, h1, h2⟩ <;> nlinarith

/-! ## §37.2  The exact change of variables -/

/-- **`product_resummation`.**  `KERNEL-PROVED`.  The lattice change of variables `m = q n`,
with the lower cutoff `m > z` retained on both sides. -/
theorem product_resummation {z M q : ℕ} (hq : 0 < q) (f : ℕ → ℚ) :
    ∑ m ∈ discreteRange z M q, f m = ∑ n ∈ fibreRange z M q, f (q * n) := by
  refine (Finset.sum_nbij' (fun n => q * n) (fun m => m / q) ?_ ?_ ?_ ?_ ?_).symm
  · intro n hn
    obtain ⟨h1, h2⟩ := (mem_fibreRange hq).1 hn
    exact mem_discreteRange.2 ⟨⟨n, rfl⟩, h1, h2⟩
  · intro m hm
    obtain ⟨⟨c, rfl⟩, h2, h3⟩ := mem_discreteRange.1 hm
    show (q * c) / q ∈ fibreRange z M q
    rw [Nat.mul_div_cancel_left c hq]
    exact (mem_fibreRange hq).2 ⟨h2, h3⟩
  · intro n _
    exact Nat.mul_div_cancel_left n hq
  · intro m hm
    obtain ⟨⟨c, rfl⟩, -, -⟩ := mem_discreteRange.1 hm
    show q * ((q * c) / q) = q * c
    rw [Nat.mul_div_cancel_left c hq]
  · intro n _
    rfl

/-- **`fibre_range_exact`.**  `KERNEL-PROVED`.  The transformed discrete range is exactly
`z < m ≤ M` written in the fibre variable. -/
theorem fibre_range_exact {z M q n : ℕ} (hq : 0 < q) :
    n ∈ fibreRange z M q ↔ (z < q * n ∧ q * n ≤ M) := mem_fibreRange hq

/-! ## §37.3  The `m > z` firewall -/

/-- **`lower_cutoff_matters`.**  `KERNEL-PROVED`.  Dropping the lower cutoff `m > z` changes
the source: with `q = 1`, `z = 1`, `M = 2` and `f ≡ 1` the two sums are `1` and `2`. -/
theorem lower_cutoff_matters :
    (∑ _m ∈ discreteRange 1 2 1, (1 : ℚ)) ≠ ∑ _m ∈ discreteRangeNoCutoff 2 1, (1 : ℚ) := by
  have h1 : discreteRange 1 2 1 = ({2} : Finset ℕ) := by decide
  have h2 : discreteRangeNoCutoff 2 1 = ({1, 2} : Finset ℕ) := by decide
  rw [h1, h2]
  norm_num

/-- **`cutoff_subset`.**  `KERNEL-PROVED`.  The cutoff window is contained in the uncut one. -/
theorem cutoff_subset (z M q : ℕ) : discreteRange z M q ⊆ discreteRangeNoCutoff M q := by
  intro m hm
  obtain ⟨h1, h2, h3⟩ := mem_discreteRange.1 hm
  simp only [discreteRangeNoCutoff, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨by omega, h3⟩, h1⟩

/-! ## §37.4  The complementary `n` geometry of the survivor region -/

/-- The geometric band condition of an `N ≥ 7` configuration at index `n`. -/
def BandCond (n : ℤ) (t : ℚ) : Prop := 7 < 10 * (n : ℚ) * t ∧ 10 * ((n : ℚ) + 6) * t ≤ 9

theorem bandCond_multAtLeast {n : ℤ} {t : ℚ} (h : BandCond n t) : MultAtLeast 7 t := by
  refine ⟨n, h.1, ?_⟩
  have := h.2
  push_cast
  linarith

/-- **`bandIndex_ge_22`.**  `KERNEL-PROVED`.  A geometric `N ≥ 7` band index is at least
`22`: the indices `n ≤ 21` are geometrically absent. -/
theorem bandIndex_ge_22 {n : ℤ} {t : ℚ} (ht : 0 < t) (h : BandCond n t) : 22 ≤ n := by
  obtain ⟨h1, h2⟩ := h
  have hn0 : 0 < n := by
    by_contra hc
    push_neg at hc
    have : ((n : ℚ)) ≤ 0 := by exact_mod_cast hc
    nlinarith
  have hnQ : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn0
  have hkey : 7 * ((n : ℚ) + 6) < 9 * (n : ℚ) := by nlinarith
  have : (7 : ℤ) * (n + 6) < 9 * n := by exact_mod_cast hkey
  omega

/-- **`bandIndex_le_21_absent`.**  `KERNEL-PROVED`.  Restatement: `n ≤ 21` never occurs. -/
theorem bandIndex_le_21_absent {n : ℤ} {t : ℚ} (ht : 0 < t) (hn : n ≤ 21) : ¬ BandCond n t :=
  fun h => by have := bandIndex_ge_22 ht h; omega

/-- **`bandIndex_exceptional`.**  `KERNEL-PROVED`.  The indices `22, 23, 24` are the
exceptional finite geometry: each pins `t` to one explicit rational band. -/
theorem bandIndex_exceptional {n : ℤ} {t : ℚ} (ht : 0 < t) (h : BandCond n t)
    (hn : n ≤ 24) :
    (n = 22 ∧ 7/220 < t ∧ t ≤ 9/280) ∨ (n = 23 ∧ 7/230 < t ∧ t ≤ 9/290) ∨
      (n = 24 ∧ 7/240 < t ∧ t ≤ 3/100) := by
  have h22 := bandIndex_ge_22 ht h
  obtain ⟨h1, h2⟩ := h
  interval_cases n
  · exact Or.inl ⟨rfl, by push_cast at h1; linarith, by push_cast at h2; linarith⟩
  · exact Or.inr (Or.inl ⟨rfl, by push_cast at h1; linarith, by push_cast at h2; linarith⟩)
  · exact Or.inr (Or.inr ⟨rfl, by push_cast at h1; linarith, by push_cast at h2; linarith⟩)

/-- **`bandIndex_chain`.**  `KERNEL-PROVED`.  From index `25` on the bands merge: the
normalised variable satisfies `t ≤ 9/310`. -/
theorem bandIndex_chain {n : ℤ} {t : ℚ} (ht : 0 < t) (h : BandCond n t) (hn : 25 ≤ n) :
    t ≤ 9/310 := by
  obtain ⟨-, h2⟩ := h
  have hnQ : (25 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  nlinarith

/-! ## §37.5  Arithmetic conditions are *not* geometry -/

/-- The arithmetic side conditions of the fibre, kept strictly separate from the geometry. -/
def FibreArithmetic (z q m n : ℕ) : Prop :=
  n ∣ m ∧ m = q * n ∧ 200 < q ∧ ¬ 2 ∣ q ∧ Squarefree q ∧ Nat.Coprime q z ∧ z < m

/-- **`geometry_not_arithmetic`.**  `KERNEL-PROVED`.  Firewall: the geometric band condition
does **not** imply the arithmetic conditions — they must be carried separately.  Witness:
`n = 22`, `t = 1/40` satisfies no band condition at that index, while `t = 3/100` at `n = 24`
does, with an even `q` violating the arithmetic. -/
theorem geometry_not_arithmetic :
    BandCond 24 (3/100) ∧ ¬ FibreArithmetic 1 2 2 1 := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rintro ⟨-, -, h, -⟩
  omega

/-- **`arithmetic_not_geometry`.**  `KERNEL-PROVED`.  Conversely, the arithmetic conditions do
not imply the geometry: an admissible arithmetic fibre can sit at a `t` outside the survivor
region. -/
theorem arithmetic_not_geometry :
    FibreArithmetic 1 211 211 1 ∧ ¬ BandCond 24 (1/2) := by
  refine ⟨⟨one_dvd _, by norm_num, by norm_num, by decide,
    (by norm_num : Nat.Prime 211).squarefree, by decide, by norm_num⟩, ?_⟩
  rintro ⟨-, h⟩
  norm_num at h

end Effectivity
end Erdos287
