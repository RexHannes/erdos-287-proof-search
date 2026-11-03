import Mathlib

open scoped BigOperators

namespace Erdos287
namespace Gold41

/-- Boolean membership indicator for a finite denominator set. -/
def boolIndicator (A : Finset ℕ) (n : ℕ) : Bool :=
  decide (n ∈ A)

/-- `0/1` membership indicator for a finite denominator set. -/
def natIndicator (A : Finset ℕ) (n : ℕ) : ℕ :=
  if n ∈ A then 1 else 0

@[simp] theorem boolIndicator_eq_true {A : Finset ℕ} {n : ℕ} :
    boolIndicator A n = true ↔ n ∈ A := by
  simp [boolIndicator]

@[simp] theorem boolIndicator_eq_false {A : Finset ℕ} {n : ℕ} :
    boolIndicator A n = false ↔ n ∉ A := by
  simp [boolIndicator]

@[simp] theorem natIndicator_eq_one {A : Finset ℕ} {n : ℕ} :
    natIndicator A n = 1 ↔ n ∈ A := by
  by_cases hn : n ∈ A <;> simp [natIndicator, hn]

@[simp] theorem natIndicator_eq_zero {A : Finset ℕ} {n : ℕ} :
    natIndicator A n = 0 ↔ n ∉ A := by
  by_cases hn : n ∈ A <;> simp [natIndicator, hn]

/-- Literal finite selected set for the Gold 4.1 local task. -/
structure SelectedSet where
  /-- selected denominators `A ⊆ {2, ..., M}` -/
  A : Finset ℕ
  /-- maximal selected denominator -/
  M : ℕ
  /-- lower endpoint condition `2 ≤ n` for all selected `n` -/
  two_le : ∀ {n : ℕ}, n ∈ A → 2 ≤ n
  /-- `M` is selected -/
  max_mem : M ∈ A
  /-- maximality of `M` on `A` -/
  le_max : ∀ {n : ℕ}, n ∈ A → n ≤ M
  /-- reciprocal sum source equation -/
  reciprocal_sum_one : ∑ n ∈ A, (1 : ℚ) / n = 1

namespace SelectedSet

variable (S : SelectedSet)

/-- Positivity of every selected denominator. -/
theorem pos_of_mem {n : ℕ} (hn : n ∈ S.A) : 0 < n :=
  lt_of_lt_of_le (by decide : 0 < 2) (S.two_le hn)

/-- Complete `q`-row sum `S_q = ∑_{n ∈ A, q ∣ n} 1/n`. -/
def row (q : ℕ) : ℚ :=
  ∑ n ∈ S.A.filter (fun n => q ∣ n), (1 : ℚ) / n

/-- Numerator of the reduced `q`-row rational. -/
def rowNum (q : ℕ) : ℤ := (S.row q).num

/-- Denominator of the reduced `q`-row rational. -/
def rowDen (q : ℕ) : ℕ := (S.row q).den

/-- Reduced-form decomposition `S_q = a_q / b_q`. -/
theorem row_eq_num_div_den (q : ℕ) :
    (S.rowNum q : ℚ) / (S.rowDen q : ℚ) = S.row q := by
  simpa [rowNum, rowDen] using Rat.num_div_den (S.row q)

/-- The reduced denominator is positive. -/
theorem rowDen_pos (q : ℕ) : 0 < S.rowDen q := by
  exact Nat.pos_of_ne_zero (Rat.den_nz (S.row q))

/-- Reducedness (`a_q`, `b_q` coprime) of the row representation. -/
theorem rowNum_rowDen_coprime (q : ℕ) : (Int.natAbs (S.rowNum q)).Coprime (S.rowDen q) := by
  simpa [rowNum, rowDen] using Rat.reduced (S.row q)

end SelectedSet

/-- Precise gap-two property over an interval `[N, M]`. -/
def GapTwoProperty (A : Finset ℕ) (N M : ℕ) : Prop :=
  ∀ n : ℕ, N ≤ n → n + 1 ≤ M → (n ∈ A ∨ n + 1 ∈ A)

end Gold41
end Erdos287
