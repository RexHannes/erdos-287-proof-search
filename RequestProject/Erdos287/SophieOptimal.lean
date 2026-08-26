import RequestProject.Erdos287.Blocker

/-!
# Erdős Problem #287 — automatic placement and the cofactor-two Sophie blockers

This file is **append-only** with respect to the existing bank: nothing here rewrites or
weakens a previously banked theorem.  It adds three things.

## 1. Automatic placement

The banked global size inequality is `Gap2CE.exp_lower`,

  `Real.exp 1 * ((N : ℝ) - 1) < (M : ℝ)`,

in which `e` is *literally* Euler's number `Real.exp 1` (not a named integer constant),
so the inequality `2 < Real.exp 1` is available from Mathlib and may legitimately be used.
Consequently `M < 2 * x` forces `N ≤ x` (`Gap2CE.N_le_of_M_lt_two_mul`).  This removes the
`N ≤ p` / `N + 1 ≤ p` side conditions that the banked good-prime blockers carry as
hypotheses.

## 2. The cofactor-two window

The banked exclusion primitive is `ExcludedPP M q` together with
`Erdos287.primePower_window_exclusion`.  Its window is the **floor** `⌊M/q⌋`, its threshold
is the **strict** inequality `C ⌊M/q⌋ < p`, and it excludes **every multiple** of `q`
(not just `q` itself).  A prime `q > C 2 = 3` with `M < 3q` therefore has window `≤ 2`
and is excluded (`Erdos287.excludedPP_of_window_two`), so `2q` is a hole.

## 3. The plus/minus Sophie blockers

`Gap2CE.plus_sophie_blocker`  : `q > 3`, `p = 2q + 1` prime, `p ≤ M`, `M < 3q` ⟹ no `Gap2CE`.
`Gap2CE.minus_sophie_blocker` : `q > 3`, `p = 2q - 1` prime, `p + 1 ≤ M`, `M < 3q` ⟹ no `Gap2CE`.

Both are strictly stronger than the banked `Gap2CE.safePrime_blocker`, which needs
`r > 25 = C 4` and an explicit placement hypothesis, because the extra band hypothesis
`M < 3q` sharpens the window from `2d = 4` to `2`.
-/

open scoped BigOperators

namespace Erdos287

/-! ## The cofactor-two window exclusion -/

/-- **Cofactor-two exclusion.**  A prime `q > C 2 = 3` whose window is `⌊M/q⌋ ≤ 2`
(guaranteed by `M < 3q`) is an excluded prime power, so no multiple of `q` — in
particular `2q` — can be a denominator. -/
theorem excludedPP_of_window_two {M q : ℕ} (hq : q.Prime) (hq3 : 3 < q) (hM : M < 3 * q) :
    ExcludedPP M q := by
  refine ⟨q, 1, hq, le_rfl, (pow_one q).symm, ?_⟩
  have hw : M / q ≤ 2 := by
    have : M / q < 3 := Nat.div_lt_of_lt_mul (by omega)
    omega
  calc C (M / q) ≤ C 2 := C_mono hw
    _ = 3 := C_two
    _ < (q : ℤ) := by exact_mod_cast hq3

/-- **Architecture optimality (precise finite form).**  Any adjacent-pair architecture that
uses the denominator `2q` inside the window `[1, M]` necessarily has `⌊M/q⌋ ≥ 2`; so `J = 2`
is the smallest window such an architecture can present, and `C 2 = 3` the smallest threshold.
This is optimality *within* the stated `2q`-architecture only. -/
theorem window_ge_two_of_two_mul_le {M q : ℕ} (hq : 0 < q) (h : 2 * q ≤ M) : 2 ≤ M / q :=
  Nat.le_div_iff_mul_le hq |>.2 (by omega)

namespace Gap2CE

variable (ce : Gap2CE)

/-! ## Automatic placement -/

/-- `2 < Real.exp 1`, the only analytic ingredient of the placement lemma. -/
private lemma two_lt_exp_one : (2 : ℝ) < Real.exp 1 := by
  nlinarith [Real.exp_one_gt_d9]

/-- **Automatic placement.**  From the banked size inequality `e·(N-1) < M` (with `e` literally
Euler's number) and `M < 2x` we get `N ≤ x`.  No further hypotheses are needed. -/
theorem N_le_of_M_lt_two_mul {x : ℕ} (hx : ce.M < 2 * x) : ce.N ≤ x := by
  by_contra hcon
  push_neg at hcon
  have hxN : (x : ℝ) ≤ (ce.N : ℝ) - 1 := by
    have : (x : ℝ) + 1 ≤ (ce.N : ℝ) := by exact_mod_cast hcon
    linarith
  have hx0 : (0 : ℝ) < x := by
    rcases Nat.eq_zero_or_pos x with rfl | h
    · simp at hx
    · exact_mod_cast h
  have h1 : Real.exp 1 * (x : ℝ) ≤ Real.exp 1 * ((ce.N : ℝ) - 1) :=
    mul_le_mul_of_nonneg_left hxN (Real.exp_pos 1).le
  have h2 : (ce.M : ℝ) < 2 * (x : ℝ) := by exact_mod_cast hx
  have h3 := ce.exp_lower
  nlinarith [two_lt_exp_one]

/-! ## The plus/minus Sophie blockers -/

/-- **Plus Sophie blocker.**  Let `q > 3` and `p = 2q + 1` both be prime, with `p ≤ M` and
`M < 3q`.  Then no gap-`≤2` counterexample exists.

Chain (each step machine-checked, no step accepted by inspection):
`M < 3q ⟹ ⌊M/q⌋ ≤ 2 ⟹ q` excluded `⟹ 2q = p-1` is a hole;
`M < 3q < 2p ⟹ ⌊M/p⌋ = 1 ⟹ p` is a hole;
`M < 3q < 2(p-1) ⟹ N ≤ p-1` by automatic placement;
so `p-1, p ∈ [N, M]` are adjacent holes, contradicting `holes_isolated`. -/
theorem plus_sophie_blocker {q p : ℕ}
    (hq : q.Prime) (hq3 : 3 < q) (hp : p.Prime) (heq : p = 2 * q + 1)
    (hpM : p ≤ ce.M) (hM3 : ce.M < 3 * q) : False := by
  have hqexc : ExcludedPP ce.M q := excludedPP_of_window_two hq hq3 hM3
  have hM2p : ce.M < 2 * p := by omega
  have hpexc : ExcludedPP ce.M p := excludedPP_self_of_large hp hpM hM2p
  have hN : ce.N ≤ 2 * q := ce.N_le_of_M_lt_two_mul (by omega)
  exact ce.excludedPP_blockerPair (x := 2 * q) (q₁ := q) (q₂ := p)
    hN (by omega) hqexc hpexc ⟨2, by ring⟩ ⟨1, by omega⟩

/-- **Minus Sophie blocker.**  Let `q > 3` and `p = 2q - 1` both be prime (written
`p + 1 = 2q`), with `p + 1 ≤ M` and `M < 3q`.  Then no gap-`≤2` counterexample exists.

Chain: `⌊M/q⌋ ≤ 2 ⟹ 2q = p+1` is a hole; `M < 3q < 2p ⟹ p` is a hole (window `1`);
`M < 2p ⟹ N ≤ p`; so `p, p+1` are adjacent holes. -/
theorem minus_sophie_blocker {q p : ℕ}
    (hq : q.Prime) (hq3 : 3 < q) (hp : p.Prime) (heq : p + 1 = 2 * q)
    (hpM : p + 1 ≤ ce.M) (hM3 : ce.M < 3 * q) : False := by
  have hqexc : ExcludedPP ce.M q := excludedPP_of_window_two hq hq3 hM3
  have hM2p : ce.M < 2 * p := by omega
  have hpexc : ExcludedPP ce.M p := excludedPP_self_of_large hp (by omega) hM2p
  have hN : ce.N ≤ p := ce.N_le_of_M_lt_two_mul hM2p
  exact ce.excludedPP_blockerPair (x := p) (q₁ := p) (q₂ := q)
    hN hpM hpexc hqexc dvd_rfl ⟨2, by omega⟩

end Gap2CE

end Erdos287
