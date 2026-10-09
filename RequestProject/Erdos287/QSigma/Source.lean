import Mathlib

/-!
# Erdős #287 — the exact quotient-one source

For integers `a ≤ M` and a set `R` of *compulsory omissions* we define

* `B = [a, M] \ R` (the retained interval),
* `V = { n ∈ B \ {a, M} : |n - r| ≠ 1 for every r ∈ R }` (the optional positions),
* `W = lcm(B)`,
* `T = ∑_{n ∈ B} W/n - W` (an integer, no truncation),
* `τ = T / W`.

A *source solution* is an independent set `E ⊆ V` (no two consecutive integers) with
`∑_{n ∈ E} W/n = T`.  This file proves the purely arithmetic facts about this source:
the reciprocal form `τ = ∑_{n∈B} 1/n - 1`, the fact that every solution has reciprocal
mass exactly `τ`, and the size bound `|E| ≤ ⌊M T / W⌋`.

The bridge to the literal Erdős #287 counterexample predicate is in
`RequestProject/Erdos287/QSigma/Bridge.lean`.
-/

open scoped BigOperators

namespace Erdos287.ExactSource

/-- The retained interval `B = [a, M] \ R`. -/
def B (a M : ℕ) (R : Finset ℕ) : Finset ℕ := Finset.Icc a M \ R

/-- The optional positions `V`: retained, not an endpoint, not adjacent to a compulsory
omission. -/
def V (a M : ℕ) (R : Finset ℕ) : Finset ℕ :=
  (B a M R).filter (fun n => n ≠ a ∧ n ≠ M ∧ ∀ r ∈ R, n + 1 ≠ r ∧ r + 1 ≠ n)

/-- `W = lcm(B)`. -/
def W (a M : ℕ) (R : Finset ℕ) : ℕ := (B a M R).lcm id

/-- The exact source target `T = ∑_{n∈B} W/n - W`, computed in `ℤ` (no truncation). -/
def T (a M : ℕ) (R : Finset ℕ) : ℤ :=
  (∑ n ∈ B a M R, ((W a M R / n : ℕ) : ℤ)) - (W a M R : ℤ)

/-- `τ = T / W`. -/
def tau (a M : ℕ) (R : Finset ℕ) : ℚ := (T a M R : ℚ) / (W a M R : ℚ)

/-- A set of integers is *independent* if it contains no two consecutive integers. -/
def Indep (E : Finset ℕ) : Prop := ∀ x ∈ E, x + 1 ∉ E

/-- **(SOURCE)**: `E` is an independent subset of `V` with `∑_{n∈E} W/n = T`. -/
def SourceSol (a M : ℕ) (R E : Finset ℕ) : Prop :=
  E ⊆ V a M R ∧ Indep E ∧ (∑ n ∈ E, ((W a M R / n : ℕ) : ℤ)) = T a M R

/-- The size budget `R_T = ⌊M T / W⌋`. -/
def RT (a M : ℕ) (R : Finset ℕ) : ℕ := (M * (T a M R).toNat) / W a M R

variable {a M : ℕ} {R : Finset ℕ}

lemma mem_B {n : ℕ} : n ∈ B a M R ↔ a ≤ n ∧ n ≤ M ∧ n ∉ R := by
  simp [B, and_assoc]

lemma mem_V {n : ℕ} :
    n ∈ V a M R ↔ n ∈ B a M R ∧ n ≠ a ∧ n ≠ M ∧ ∀ r ∈ R, n + 1 ≠ r ∧ r + 1 ≠ n := by
  simp [V]

lemma V_subset_B : V a M R ⊆ B a M R := fun _ h => (mem_V.1 h).1

lemma dvd_W_of_mem_B {n : ℕ} (h : n ∈ B a M R) : n ∣ W a M R :=
  Finset.dvd_lcm (f := id) h

lemma pos_of_mem_B (ha : 0 < a) {n : ℕ} (h : n ∈ B a M R) : 0 < n :=
  lt_of_lt_of_le ha (mem_B.1 h).1

lemma W_ne_zero (ha : 0 < a) : W a M R ≠ 0 := by
  intro h
  rw [W, Finset.lcm_eq_zero_iff] at h
  obtain ⟨x, hx, hx0⟩ := h
  have := pos_of_mem_B (R := R) (M := M) ha hx
  simp at hx0; omega

lemma cast_W_div (ha : 0 < a) {n : ℕ} (h : n ∈ B a M R) :
    ((W a M R / n : ℕ) : ℚ) = (W a M R : ℚ) / n := by
  rw [Nat.cast_div (dvd_W_of_mem_B h)]
  exact_mod_cast (pos_of_mem_B ha h).ne'

/-- **Reciprocal form of the target**: `τ = ∑_{n∈B} 1/n - 1`. -/
theorem tau_eq (ha : 0 < a) : tau a M R = (∑ n ∈ B a M R, (1 : ℚ) / n) - 1 := by
  have hW : (W a M R : ℚ) ≠ 0 := by exact_mod_cast W_ne_zero ha
  rw [tau, T]
  simp only [Int.cast_sub, Int.cast_sum, Int.cast_natCast]
  rw [sub_div, div_self hW, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [cast_W_div ha hn]; field_simp

/-- Weighted sums over subsets of `B`, transported to `ℚ`. -/
lemma sum_W_div_cast (ha : 0 < a) {E : Finset ℕ} (hE : E ⊆ B a M R) :
    ((∑ n ∈ E, ((W a M R / n : ℕ) : ℤ) : ℤ) : ℚ) = (W a M R : ℚ) * ∑ n ∈ E, (1 : ℚ) / n := by
  simp only [Int.cast_sum, Int.cast_natCast]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [cast_W_div ha (hE hn)]; ring

/-- Every source solution has reciprocal mass exactly `τ`. -/
theorem SourceSol.recip_eq_tau (ha : 0 < a) {E : Finset ℕ} (h : SourceSol a M R E) :
    (∑ n ∈ E, (1 : ℚ) / n) = tau a M R := by
  have hW : (W a M R : ℚ) ≠ 0 := by exact_mod_cast W_ne_zero ha
  have key := sum_W_div_cast (R := R) (M := M) ha (h.1.trans V_subset_B)
  rw [h.2.2] at key
  rw [tau, key]; field_simp

/-- The target is nonnegative whenever a solution exists. -/
theorem SourceSol.T_nonneg {E : Finset ℕ} (h : SourceSol a M R E) : 0 ≤ T a M R := by
  rw [← h.2.2]; positivity

/-- **Size bound** in multiplicative form: `|E| · W ≤ M · T`. -/
theorem SourceSol.card_mul_W_le {E : Finset ℕ} (h : SourceSol a M R E) :
    (E.card : ℤ) * W a M R ≤ M * T a M R := by
  rw [← h.2.2, Finset.mul_sum, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_le_sum (fun n hn => ?_)
  have hB := V_subset_B (h.1 hn)
  have hnW := dvd_W_of_mem_B hB
  have hnM : n ≤ M := (mem_B.1 hB).2.1
  have h2 : W a M R ≤ M * (W a M R / n) := by
    calc W a M R = n * (W a M R / n) := (Nat.mul_div_cancel' hnW).symm
      _ ≤ M * (W a M R / n) := Nat.mul_le_mul_right _ hnM
  push_cast
  simp only [one_mul]
  exact_mod_cast h2

/-- **Size bound** `|E| ≤ R_T = ⌊M T / W⌋`. -/
theorem SourceSol.card_le_RT (ha : 0 < a) {E : Finset ℕ} (h : SourceSol a M R E) :
    E.card ≤ RT a M R := by
  have h1 := h.card_mul_W_le
  have hT := h.T_nonneg
  have hWpos : 0 < W a M R := Nat.pos_of_ne_zero (W_ne_zero ha)
  rw [RT, Nat.le_div_iff_mul_le hWpos]
  have : ((T a M R).toNat : ℤ) = T a M R := Int.toNat_of_nonneg hT
  have h2 : ((E.card * W a M R : ℕ) : ℤ) ≤ ((M * (T a M R).toNat : ℕ) : ℤ) := by
    push_cast; rw [this]; exact h1
  exact_mod_cast h2

end Erdos287.ExactSource
