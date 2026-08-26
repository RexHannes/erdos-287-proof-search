import RequestProject.Erdos287.Universal
import RequestProject.Erdos287.Counterexample

/-!
# Erdős Problem #287 — uniform numerator bounds and forced holes

This file provides *uniform* (formula) upper bounds for the numerator quantity `C`,
and uses them to package the prime-power window exclusion into a "forced hole"
predicate whose adjacency yields a contradiction for gap-`≤2` counterexamples.

We reuse the infrastructure of `Universal.lean`: `lcmUpto j = lcm(1,…,j)`, the
Mathlib harmonic number `harmonic j = H_j`, and the per-subset bound
`numerator_le_lcm_mul_harmonic`.

Main results:

* `C_le_lcm_mul_harmonic`: `C j ≤ lcm(1,…,j) · H_j` (Task 1).
* `C_le_U`: the Lean-friendly explicit bound `C j ≤ j · j!` (Task 2), where
  `U j = j · j!`.
* `primePower_window_exclusion_U`: uniform prime-power exclusion using `U` in place
  of the exact `C` (Task 3).
* `ForcedHole`: the predicate `∃ q = p^e, q ∣ n, p > U(⌊M/q⌋)` (Task 4).
* `Gap2CE.forcedHole_pair_contradiction`: two adjacent forced holes strictly inside
  the window contradict a gap-`≤2` counterexample (Task 5).
-/

open scoped BigOperators

namespace Erdos287

/-! ## Task 1 — the uniform numerator bound `C j ≤ lcm(1,…,j) · H_j` -/

/-- **Task 1.** `C j ≤ lcm(1,…,j) · H_j`, where `H_j` is the `j`-th harmonic number. -/
theorem C_le_lcm_mul_harmonic (j : ℕ) :
    (C j : ℚ) ≤ (lcmUpto j : ℚ) * harmonic j := by
  by_cases hj : 1 ≤ j
  · obtain ⟨S, _, hS₂, hS₃⟩ := C_attained j hj
    rw [← hS₃]
    exact numerator_le_lcm_mul_harmonic hS₂
  · interval_cases j
    unfold C lcmUpto
    norm_num [harmonic]

/-! ## Task 2 — the explicit Lean-friendly bound `C j ≤ j · j!` -/

/-- The explicit uniform upper bound `U j = j · j!` for `C j`. -/
def U (j : ℕ) : ℕ := j * Nat.factorial j

/-- `lcm(1,…,j)` divides `j!`, hence `lcm(1,…,j) ≤ j!`. -/
theorem lcmUpto_le_factorial (j : ℕ) : lcmUpto j ≤ Nat.factorial j := by
  refine' Nat.le_of_dvd ( Nat.factorial_pos _ ) _;
  refine' Finset.lcm_dvd fun x hx => Nat.dvd_factorial _ _ <;> aesop

/-- `H_j ≤ j`. -/
theorem harmonic_le_nat (j : ℕ) : harmonic j ≤ (j : ℚ) := by
  rw [harmonic_eq_sum_Icc]
  calc ∑ s ∈ Finset.Icc 1 j, (1 : ℚ) / s ≤ ∑ _s ∈ Finset.Icc 1 j, (1 : ℚ) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        simp only [Finset.mem_Icc] at hi
        rw [div_le_one (by exact_mod_cast hi.1)]
        exact_mod_cast hi.1
    _ = (j : ℚ) := by simp

/-- **Task 2.** The explicit uniform bound `C j ≤ j · j!`. -/
theorem C_le_U (j : ℕ) : C j ≤ (U j : ℤ) := by
  have hq : (C j : ℚ) ≤ (U j : ℚ) := by
    refine (C_le_lcm_mul_harmonic j).trans ?_
    have hL : (lcmUpto j : ℚ) ≤ (Nat.factorial j : ℚ) := by
      exact_mod_cast lcmUpto_le_factorial j
    have hh0 : (0 : ℚ) ≤ harmonic j := by
      rw [harmonic_eq_sum_Icc]; positivity
    calc (lcmUpto j : ℚ) * harmonic j ≤ (Nat.factorial j : ℚ) * (j : ℚ) :=
          mul_le_mul hL (harmonic_le_nat j) hh0 (by positivity)
      _ = (U j : ℚ) := by simp [U, Nat.cast_mul]; ring
  exact_mod_cast hq

/-! ## Task 3 — uniform prime-power window exclusion -/

/-- **Task 3.** Uniform prime-power window exclusion: if `A ⊆ {1,…,M}`, `∑ 1/a = 1`,
`q = p^e ≤ M`, `j = ⌊M/q⌋`, and `p > U(j)`, then no element of `A` is divisible by `q`. -/
theorem primePower_window_exclusion_U
    (A : Finset ℕ) (M p e : ℕ) (hp : p.Prime)
    (hpos : ∀ a ∈ A, 0 < a)
    (hAM : ∀ a ∈ A, a ≤ M)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1)
    (he : 1 ≤ e)
    (hqM : p ^ e ≤ M)
    (hpU : U (M / p ^ e) < p) :
    ∀ a ∈ A, ¬ (p ^ e ∣ a) := by
  apply primePower_window_exclusion A M p e hp hpos hAM hsum he hqM;
  exact lt_of_le_of_lt ( C_le_U _ ) ( mod_cast hpU )

/-! ## Task 4 — the `ForcedHole` predicate -/

/-- **Task 4.** `ForcedHole M n` holds when some prime power `q = p^e` divides `n`
with `p > U(⌊M/q⌋)`. Together with a reciprocal sum equal to `1` on `{1,…,M}`,
this forces `n` to be absent (a "hole"). -/
def ForcedHole (M n : ℕ) : Prop :=
  ∃ p e : ℕ, p.Prime ∧ 1 ≤ e ∧ p ^ e ∣ n ∧ U (M / p ^ e) < p

/-- A forced hole is genuinely absent from a gap-`≤2` counterexample. -/
theorem Gap2CE.forcedHole_not_mem (ce : Gap2CE) {n : ℕ}
    (h : ForcedHole ce.M n) : n ∉ ce.A := by
  obtain ⟨ p, e, hp, he, hdvd, hU ⟩ := h;
  contrapose! hU;
  have := primePower_window_exclusion_U ce.A ce.M p e hp ce.hpos ( fun a ha => Finset.le_max' _ _ ha ) ce.hsum he ( Nat.le_trans ( Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by linarith [ ce.hpos n hU ] ) ) hdvd ) ( Finset.le_max' _ _ hU ) );
  exact le_of_not_gt fun h => this h n hU hdvd

/-! ## Task 5 — adjacent forced holes give a contradiction -/

/-- **Task 5.** If a gap-`≤2` counterexample has endpoint `M` and there is `n` with
`M / e < n < M` (with `e = exp 1`) such that both `n` and `n+1` are forced holes,
then we reach a contradiction. -/
theorem Gap2CE.forcedHole_pair_contradiction (ce : Gap2CE) {n : ℕ}
    (hlo : (ce.M : ℝ) / Real.exp 1 < n)
    (hhi : n < ce.M)
    (h1 : ForcedHole ce.M n)
    (h2 : ForcedHole ce.M (n + 1)) : False := by
  have h_contradiction : ce.N ≤ n ∧ n + 1 ≤ ce.M := by
    refine' ⟨ Nat.le_of_lt_succ _, Nat.succ_le_of_lt hhi ⟩;
    have := ce.exp_lower;
    rw [ div_lt_iff₀ ( Real.exp_pos _ ) ] at hlo;
    exact_mod_cast ( by nlinarith [ Real.add_one_le_exp 1 ] : ( ce.N : ℝ ) < n + 1 );
  exact ce.holes_isolated n h_contradiction.1 h_contradiction.2 |> fun h => h.elim ( fun h => by have := Gap2CE.forcedHole_not_mem ce h1; aesop ) fun h => by have := Gap2CE.forcedHole_not_mem ce h2; aesop;

end Erdos287
