import Mathlib
import RequestProject.TrustedBank.R9.Certificate

/-!
# High-order counterguard for the fixed-certificate leakage census (V12, Part G4)

The V12 correction withdraws the expectation that a fixed Ford certificate reduces the
leakage census to the two defect orders `k = 8, 9`.  This file certifies, by pure finite
combinatorics, **why** that reduction cannot be justified from the divisor combinatorics
alone: a truncated Möbius divisor weight on a *balanced* cell with `k` prime factors is
nonzero for every defect order `k`, not only for `k = 8, 9`.

Nothing analytic is claimed here.  In particular this file does **not** say that the
higher-order packets carry non-negligible analytic mass; it says only that they are not
combinatorially annihilated, so an "H8/H9 only" census is not a finite consequence of the
truncated Möbius weight.

## Model

A squarefree integer with `k` distinct prime factors has its divisor lattice isomorphic
to the subsets of a `k`-element set, with `μ(d) = (−1)^{#S}`.  If the `k` primes are
*balanced* (all of comparable size `n^{1/k}`) and the truncation is at `n^γ`, a divisor
survives the truncation exactly when its number of prime factors is at most `r = ⌊γk⌋`.
`balancedCellCut` certifies that cut; `balancedCellWeight` is the resulting weight.

## Main results

* `alternating_partial_binomial` — `∑_{j≤r} (−1)^j C(k,j) = (−1)^r C(k−1,r)` for `k ≥ 1`;
* `balancedCellWeight_eq` — the subset-lattice sum equals that partial alternating sum;
* `balancedCellWeight_ne_zero` — it is nonzero whenever `r < k`;
* `counterguard_k7 … counterguard_k12` — the explicit values at the balanced cut
  `r = (k−1)/2` for `k = 7,…,12`, namely `−20, −35, 70, 126, −252, −462`;
* `finite_H8H9_only_census_fails` — orders `k = 7, 10, 11, 12` also carry a nonzero
  weight, so the finite census is not exhausted by `k = 8, 9`.

The value `70` at `k = 9, r = 4` agrees with the banked `TrustedBank.R9.lowSum`.

**Nomenclature guard.**  No theorem in this file, and no theorem whose name contains
`FullNine` anywhere in the project, asserts exhaustiveness of the nine-prime window;
exhaustiveness is a source question, and it is not established here.
-/

open scoped BigOperators

namespace Erdos287
namespace Counterguard

/-! ## The partial alternating binomial identity -/

/-- **Partial alternating binomial sum.**  For `k ≥ 1` and any `r`,
`∑_{j=0}^{r} (−1)^j C(k,j) = (−1)^r C(k−1,r)`. -/
theorem alternating_partial_binomial (k r : ℕ) (hk : 1 ≤ k) :
    ∑ j ∈ Finset.range (r + 1), (-1 : ℤ) ^ j * (Nat.choose k j) =
      (-1) ^ r * (Nat.choose (k - 1) r) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.sum_range_succ, ih]
      have hsplit : Nat.choose k (r + 1) = Nat.choose (k - 1) r + Nat.choose (k - 1) (r + 1) := by
        obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
        simp [Nat.choose_succ_succ]
      rw [hsplit]
      push_cast
      ring

/-! ## The balanced cell -/

/-- The truncated Möbius weight of a balanced cell with `k` prime factors and cut `r`:
the sum of `(−1)^{#S}` over the subsets `S` of a `k`-element set with `#S ≤ r`. -/
def balancedCellWeight (k r : ℕ) : ℤ :=
  ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset.filter (fun S => S.card ≤ r),
    (-1 : ℤ) ^ S.card

/-- The cell weight in binomial form. -/
theorem balancedCellWeight_eq_sum (k r : ℕ) :
    balancedCellWeight k r = ∑ j ∈ Finset.range (r + 1), (-1 : ℤ) ^ j * (Nat.choose k j) := by
  classical
  have hEq : (Finset.univ : Finset (Fin k)).powerset.filter (fun S => S.card ≤ r)
      = (Finset.range (r + 1)).biUnion (fun j => Finset.powersetCard j Finset.univ) := by
    ext S
    simp [Finset.mem_powersetCard]
  rw [balancedCellWeight, hEq, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl ?_
    intro j _
    rw [Finset.sum_powersetCard j Finset.univ (fun c => (-1 : ℤ) ^ c)]
    simp [mul_comm]
  · intro i _ j _ hij
    simp only [Finset.disjoint_left]
    intro S hS hS'
    rw [Finset.mem_powersetCard] at hS hS'
    exact hij (hS.2 ▸ hS'.2 ▸ rfl)

/-- **Closed form of the balanced cell weight.** -/
theorem balancedCellWeight_eq (k r : ℕ) (hk : 1 ≤ k) :
    balancedCellWeight k r = (-1) ^ r * (Nat.choose (k - 1) r) := by
  rw [balancedCellWeight_eq_sum, alternating_partial_binomial k r hk]

/-- **The counterguard.**  For every defect order `k` and every cut `r < k`, the balanced
cell weight is nonzero. -/
theorem balancedCellWeight_ne_zero (k r : ℕ) (hk : 1 ≤ k) (hr : r < k) :
    balancedCellWeight k r ≠ 0 := by
  rw [balancedCellWeight_eq k r hk]
  have hchoose : Nat.choose (k - 1) r ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have : ((Nat.choose (k - 1) r : ℤ)) ≠ 0 := Int.natCast_ne_zero.2 hchoose
  exact mul_ne_zero (pow_ne_zero r (by norm_num)) this

/-! ## The truncation cut -/

/-- **Balanced cut lemma.**  If the truncation exponent `γ` satisfies `r ≤ γk < r+1`,
then a divisor of a balanced `k`-factor cell survives the truncation (i.e. has size at
most `n^γ`, equivalently `j/k ≤ γ`) exactly when its number `j` of prime factors is at
most `r`.  This is the exact finite content of the balanced-cell cut. -/
theorem balancedCellCut (k r j : ℕ) (gamma : ℚ)
    (hlow : (r : ℚ) ≤ gamma * k) (hhigh : gamma * k < r + 1) :
    (j : ℚ) ≤ gamma * k ↔ j ≤ r := by
  constructor
  · intro h
    have : (j : ℚ) < (r : ℚ) + 1 := lt_of_le_of_lt h hhigh
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  · intro h
    have : (j : ℚ) ≤ (r : ℚ) := by exact_mod_cast h
    linarith

/-- The balanced cut in force at `γ` slightly below `1/2`: the surviving orders are
exactly `j ≤ (k−1)/2`. -/
def halfCut (k : ℕ) : ℕ := (k - 1) / 2

/-! ## Explicit high-order instances

The claimed coefficients at the balanced cut `r = (k−1)/2` (the cut valid for every
rational `γ` in the window `r/k ≤ γ < (r+1)/k`, which contains exponents just below
`1/2` for each of these `k`). -/

theorem counterguard_k7 : balancedCellWeight 7 (halfCut 7) = -20 := by
  rw [balancedCellWeight_eq 7 _ (by norm_num)]; decide

theorem counterguard_k8 : balancedCellWeight 8 (halfCut 8) = -35 := by
  rw [balancedCellWeight_eq 8 _ (by norm_num)]; decide

theorem counterguard_k9 : balancedCellWeight 9 (halfCut 9) = 70 := by
  rw [balancedCellWeight_eq 9 _ (by norm_num)]; decide

theorem counterguard_k10 : balancedCellWeight 10 (halfCut 10) = 126 := by
  rw [balancedCellWeight_eq 10 _ (by norm_num)]; decide

theorem counterguard_k11 : balancedCellWeight 11 (halfCut 11) = -252 := by
  rw [balancedCellWeight_eq 11 _ (by norm_num)]; decide

theorem counterguard_k12 : balancedCellWeight 12 (halfCut 12) = -462 := by
  rw [balancedCellWeight_eq 12 _ (by norm_num)]; decide

/-- The `k = 9` instance agrees with the banked nine-prime alternating sum
`TrustedBank.R9.lowSum = 70`. -/
theorem counterguard_k9_matches_bank :
    balancedCellWeight 9 (halfCut 9) = TrustedBank.R9.lowSum := by
  rw [counterguard_k9, TrustedBank.R9.lowSum_eq]

/-- **`FINITE_H8_H9_ONLY_CENSUS = FAIL`.**  Defect orders other than `8` and `9` carry a
nonzero truncated Möbius weight at the balanced cut, so no finite argument based on that
weight can restrict the census to `k ∈ {8, 9}`. -/
theorem finite_H8H9_only_census_fails :
    ∀ k ∈ ({7, 10, 11, 12} : Finset ℕ), balancedCellWeight k (halfCut k) ≠ 0 := by
  intro k hk
  fin_cases hk
  · rw [counterguard_k7]; norm_num
  · rw [counterguard_k10]; norm_num
  · rw [counterguard_k11]; norm_num
  · rw [counterguard_k12]; norm_num

/-- The same statement for *every* order `k ≥ 1`: the weight at the balanced cut never
vanishes. -/
theorem balancedCellWeight_halfCut_ne_zero (k : ℕ) (hk : 1 ≤ k) :
    balancedCellWeight k (halfCut k) ≠ 0 :=
  balancedCellWeight_ne_zero k (halfCut k) hk (by unfold halfCut; omega)

end Counterguard
end Erdos287
