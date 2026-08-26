import RequestProject.Erdos287.Window
import RequestProject.Erdos287.Counterexample

/-!
# Erdős Problem #287 — prime-free corollary and blocker pairs

* `primeFree`: in a gap-`≤2` counterexample with `M ≥ 8152`, no denominator is prime.
  For a prime denominator `p`, we have `p ≥ N > M/8 ≥ 1019 = C(7)`, and
  `j = ⌊M/p⌋ ≤ 7`, so `C(j) ≤ C(7) = 1019 < p`; `primePower_window_exclusion`
  (with `e = 1`) then excludes `p`.
* `blockerPair_contradiction`: if two consecutive integers of `[N,M]` are both absent
  from `A`, the counterexample cannot exist (it violates `holes_isolated`).
-/

open scoped BigOperators

namespace Erdos287

namespace Gap2CE

variable (ce : Gap2CE)

/-- **Blocker pair.** If `x` and `x+1` both lie in `[N, M]` but neither is in `A`,
we reach a contradiction: a gap-`≤2` counterexample has no two consecutive holes. -/
theorem blockerPair_contradiction {x : ℕ}
    (hx0 : ce.N ≤ x) (hx1 : x + 1 ≤ ce.M)
    (hxni : x ∉ ce.A) (hx1ni : x + 1 ∉ ce.A) : False := by
  rcases ce.holes_isolated x hx0 hx1 with h | h
  · exact hxni h
  · exact hx1ni h

/-- **Prime-free corollary.** For `M ≥ 8152`, no denominator of the counterexample is prime. -/
theorem primeFree (hM : 8152 ≤ ce.M) : ∀ a ∈ ce.A, ¬ a.Prime := by
  intro a ha hprime
  -- `M < 8 * N`
  have hMN : ce.M < 8 * ce.N := ce.N_gt_M_div_eight (by omega)
  -- `N ≤ a = p`
  have hNa : ce.N ≤ a := Finset.min'_le _ _ ha
  have haM : a ≤ ce.M := Finset.le_max' _ _ ha
  -- `a ≥ 1020`
  have h1020 : 1020 ≤ a := by omega
  -- `M < 8 * a`
  have hM8a : ce.M < 8 * a := by omega
  -- `M / a ≤ 7`
  have hj : ce.M / a ≤ 7 := by
    have : ce.M / a < 8 := Nat.div_lt_of_lt_mul (by omega)
    omega
  -- `C (M / a) ≤ 1019`
  have hCle : C (ce.M / a) ≤ 1019 := by
    calc C (ce.M / a) ≤ C 7 := C_mono hj
      _ = 1019 := C_seven
  -- `C (M / a^1) < a`
  have hpow : a ^ 1 = a := pow_one a
  have hCa : C (ce.M / a ^ 1) < (a : ℤ) := by
    rw [hpow]
    calc C (ce.M / a) ≤ 1019 := hCle
      _ < (a : ℤ) := by exact_mod_cast (by omega : (1019 : ℤ) < (a : ℤ))
  -- apply the window exclusion with `e = 1`, `p = a`
  have hexcl := primePower_window_exclusion ce.A ce.M a 1 hprime ce.hpos
    (fun b hb => Finset.le_max' _ _ hb) ce.hsum le_rfl (by rw [hpow]; exact haM) hCa
  exact hexcl a ha (by rw [hpow])

end Gap2CE

end Erdos287
