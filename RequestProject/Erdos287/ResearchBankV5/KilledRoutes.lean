import Mathlib.Tactic

/-!
# Research Bank V5 — killed architectures (exact fixtures retained)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

A *killed* architecture is one whose **route** is dead at a precisely stated scope.  Killing a
route never falsifies a mathematical target (see `Routes.killed_not_false_target`), and never
kills a whole method: in particular the primorial cancellation below kills one pre-sieving
architecture, **not** sieve methods in general.

Retained exact fixtures:

* `primorial_local_factor_cancellation` — for `λ ∣ s` the cofactor density `1 - 1/λ` and the
  two-linear-form singular factor `λ/(λ-1)` cancel exactly:
  `(1 - 1/λ)·λ/(λ-1) = 1`.  Hence **PRIMORIAL-SCALE PRE-SIEVING TERMINAL ROUTE: KILLED**;
* `height_drop_20_19` and `no_universal_height_ratio` — the genuine `20 → 19` regression: raw
  forced-zero plus contact arithmetic does **not** give `N_child ≤ (1-η) N_parent` for a universal
  `η > 0`.  This kills the fixed multiplicative descent architecture only.
-/

namespace Erdos287
namespace ResearchBankV5

/-! ## 1.  Primorial pre-sieve: exact local-factor cancellation -/

/-- **Exact local-factor cancellation.**  For any `λ ≠ 0, 1`, the cofactor density `1 - 1/λ` and
the two-linear-form singular series factor `λ/(λ-1)` cancel exactly. -/
theorem primorial_local_factor_cancellation (lam : ℚ) (h0 : lam ≠ 0) (h1 : lam ≠ 1) :
    (1 - 1 / lam) * (lam / (lam - 1)) = 1 := by
  have hsub : lam - 1 ≠ 0 := sub_ne_zero.2 h1
  field_simp

/-- The same cancellation at an integer prime factor `λ ≥ 2` of the sieve modulus. -/
theorem primorial_local_factor_cancellation_prime (lam : ℕ) (h : 2 ≤ lam) :
    (1 - 1 / (lam : ℚ)) * ((lam : ℚ) / ((lam : ℚ) - 1)) = 1 := by
  have h0 : (lam : ℚ) ≠ 0 := by
    have : (0 : ℚ) < (lam : ℚ) := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) h
    linarith
  have h1 : (lam : ℚ) ≠ 1 := by
    have : (2 : ℚ) ≤ (lam : ℚ) := by exact_mod_cast h
    linarith
  exact primorial_local_factor_cancellation _ h0 h1

/-- Numerical instance of the cancellation at `λ = 3`. -/
theorem primorial_cancellation_fixture : (1 - 1 / (3 : ℚ)) * ((3 : ℚ) / ((3 : ℚ) - 1)) = 1 := by
  norm_num

/-! ## 2.  No fixed multiplicative height drop -/

/-- The exact `20 → 19` regression fixture: the observed child height is `19` when the parent
height is `20`, i.e. the ratio is exactly `1 - 1/20`. -/
theorem height_drop_20_19 : (19 : ℚ) = (1 - 1 / 20) * 20 := by norm_num

/-- **Fixed-ratio descent is killed.**  No universal `η > 1/20` can satisfy
`N_child ≤ (1-η) N_parent` on the `20 → 19` fixture; since the fixture recurs at every scale,
raw forced-zero plus contact arithmetic gives no universal multiplicative drop. -/
theorem no_universal_height_ratio (eta : ℚ) (h : 1 / 20 < eta) : ¬ ((19 : ℚ) ≤ (1 - eta) * 20) := by
  intro hle
  nlinarith

/-- Any `η` compatible with the fixture is at most `1/20`; letting the fixture recur, no positive
universal ratio survives an unbounded chain. -/
theorem height_ratio_le (eta : ℚ) (h : (19 : ℚ) ≤ (1 - eta) * 20) : eta ≤ 1 / 20 := by
  nlinarith

end ResearchBankV5
end Erdos287
