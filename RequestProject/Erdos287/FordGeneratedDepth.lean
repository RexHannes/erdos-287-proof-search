import Mathlib

/-!
# Ford-generated depth: the explicit finite constants `N₀ ≤ 112 / 76 / 40` (V14, Part 2)

This file formalises **only the finite arithmetic** behind the three depth constants used by
the generated-fragment audit.  Nothing here reproves, or even states, Ford–Maynard
Lemma 7.17: the three input bounds

* smooth-fragment side depth `s ≤ 20`,
* high-prime count `k ≤ 6`,
* per-high-prime fragmentation multiplier `ell ≤ 12`,

are `PUBLISHED_EXTERNAL_INPUT`.  They enter every theorem below as explicit hypotheses.
What is proved is the arithmetic consequence

`fordGeneratedDepth s k ell = 2 * s + k * ell ≤ 112`

and its two specialisations, which is `PROVED_FINITE`.

The factor `2` on the smooth side counts the two sides (`u`- and `v`-fragments) of the
generated fragmentation; the term `k * ell` counts the fragments contributed by the `k`
high primes at multiplier `ell`.  The model is a *definition*, not a claim about the
literature: the ledger entry only asserts that, **given** the three published input
bounds, the depth of the model is at most the stated constant.

Ledger target: `FORD-GENERATED-DEPTH-N0-287 : PROVED_FINITE`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace FordDepth

/-- The generated-fragment depth model: two smooth sides of depth `s`, plus `k` high primes
each contributing at most `ell` fragments. -/
def fordGeneratedDepth (s k ell : ℕ) : ℕ := 2 * s + k * ell

@[simp] theorem fordGeneratedDepth_def (s k ell : ℕ) :
    fordGeneratedDepth s k ell = 2 * s + k * ell := rfl

/-- Monotonicity of the depth model in all three inputs. -/
theorem fordGeneratedDepth_mono {s k ell s' k' ell' : ℕ}
    (hs : s ≤ s') (hk : k ≤ k') (he : ell ≤ ell') :
    fordGeneratedDepth s k ell ≤ fordGeneratedDepth s' k' ell' := by
  have : k * ell ≤ k' * ell' := Nat.mul_le_mul hk he
  simp only [fordGeneratedDepth]
  omega

/-- **`general_ford_depth_le_112`** — `PROVED_FINITE`.

With the published input bounds `s ≤ 20`, `k ≤ 6`, `ell ≤ 12`, the generated depth is at
most `112`. -/
theorem general_ford_depth_le_112 {s k ell : ℕ}
    (hs : s ≤ 20) (hk : k ≤ 6) (he : ell ≤ 12) :
    fordGeneratedDepth s k ell ≤ 112 := by
  have h := fordGeneratedDepth_mono hs hk he
  simpa [fordGeneratedDepth] using h

/-- The bound `112` is attained by the extreme admissible input, so it is sharp for the
model (no smaller constant works for all admissible inputs). -/
theorem general_ford_depth_sharp : fordGeneratedDepth 20 6 12 = 112 := by decide

/-- **`fixed_certificate_depth_le_76`** — `PROVED_FINITE`.

On the fixed-`g*` support the high-prime fragment budget is halved, `k * ell ≤ 36`; the
depth is then at most `76`.  The hypothesis is stated as the product bound, which is the
weakest form the arithmetic actually needs. -/
theorem fixed_certificate_depth_le_76 {s k ell : ℕ}
    (hs : s ≤ 20) (hkl : k * ell ≤ 36) :
    fordGeneratedDepth s k ell ≤ 76 := by
  simp only [fordGeneratedDepth]
  omega

/-- The same bound from the factored form `k ≤ 3`, `ell ≤ 12`. -/
theorem fixed_certificate_depth_le_76_of_factors {s k ell : ℕ}
    (hs : s ≤ 20) (hk : k ≤ 3) (he : ell ≤ 12) :
    fordGeneratedDepth s k ell ≤ 76 :=
  fixed_certificate_depth_le_76 hs (Nat.mul_le_mul hk he)

theorem fixed_certificate_depth_sharp : fordGeneratedDepth 20 3 12 = 76 := by decide

/-- **`k0_depth_le_40`** — `PROVED_FINITE`.

On the `k = 0` branch there are no high primes, so only the two smooth sides contribute
and the depth is at most `40`. -/
theorem k0_depth_le_40 {s ell : ℕ} (hs : s ≤ 20) :
    fordGeneratedDepth s 0 ell ≤ 40 := by
  simp only [fordGeneratedDepth]
  omega

theorem k0_depth_sharp : fordGeneratedDepth 20 0 12 = 40 := by decide

/-- The three constants are ordered as the audit records them. -/
theorem depth_constants_ordered : (40 : ℕ) < 76 ∧ (76 : ℕ) < 112 := by decide

/-- Consistency with the banked singleton complement bound: the `k = 0` depth `40` has
complement depth `39`, the constant certified by `singleton_complement_depth_le_39`. -/
theorem k0_complement_depth : 40 - 1 = 39 := by decide

end FordDepth
end Erdos287
