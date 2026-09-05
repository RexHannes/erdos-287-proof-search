import Mathlib

/-!
# Erdős #287 — September-3 bank, §E: canonical-split finite-interval geometry

```
ABSTRACT MONOTONE CROSSING LEMMA          : KERNEL-PROVED
CANONICAL SPLIT — TWO THRESHOLDS          : KERNEL-PROVED
COEFFICIENT = SIGNED SUM OF ≤ 4 INTERVAL INDICATORS : KERNEL-PROVED
NUMERICAL EXPONENT INSTANCE (ν = 1/2)     : KERNEL-PROVED (exact, no approximation)
```

This module is **append-only**, purely order-theoretic/arithmetic, and asserts nothing
analytic.

## Content

Over a physical window `A ≤ n ≤ B` and for a *fixed* odd `d`, the canonical `n ^ ν` split
changes only finitely many times.  Precisely, since `n ↦ n ^ ν` is monotone for `ν ≥ 0`,
each of the two conditions

    d ≤ n ^ ν        and        2 d ≤ n ^ ν

is *upward closed* in `n`, hence equal on the window to a single integer threshold test
`t ≤ n` (`exists_threshold_of_monotone`, `canonicalSplit_two_thresholds`).  Consequently the
physical coefficient

    c(n) = 1_{d ≤ n^ν} − 1_{2d ∣ n} · 1_{2d ≤ n^ν}

equals, on the whole window, a signed sum of at most four interval indicators: on each of
the two residue classes `2d ∣ n`, `2d ∤ n` it is a signed sum of at most two indicators of
the intervals `[t₀, B]`, `[t₂, B]` (`canonicalSplitFourInterval`).

No real-analysis inequality is hidden behind an unproved field: the crossing statement is
proved abstractly from monotonicity alone, and the *numerical* content is isolated in
`crossing_at_half_exponent`, where the threshold is computed exactly (`d ≤ n^(1/2) ↔
d² ≤ n`, no approximation).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace September3CanonicalSplit

/-! ## §E.1  The abstract crossing lemma -/

/-- **`exists_threshold_of_monotone`.**  `KERNEL-PROVED`.  A monotone real test on a finite
window of integers crosses its threshold at most once: there is an integer `t` such that on
`[A, B]` the condition `c ≤ g n` is exactly `t ≤ n`. -/
theorem exists_threshold_of_monotone {g : ℕ → ℝ} (hg : Monotone g) (c : ℝ) (A B : ℕ) :
    ∃ t : ℕ, ∀ n : ℕ, A ≤ n → n ≤ B → (c ≤ g n ↔ t ≤ n) := by
  classical
  by_cases h : ∃ n : ℕ, A ≤ n ∧ n ≤ B ∧ c ≤ g n
  · refine ⟨Nat.find h, fun n hA hB => ⟨fun hc => Nat.find_le ⟨hA, hB, hc⟩, fun ht => ?_⟩⟩
    obtain ⟨-, -, hc⟩ := Nat.find_spec h
    exact le_trans hc (hg ht)
  · refine ⟨B + 1, fun n hA hB => ⟨fun hc => absurd ⟨n, hA, hB, hc⟩ h, fun ht => ?_⟩⟩
    omega

/-- The canonical split test `x ≤ n ^ ν` is monotone in `n`. -/
theorem monotone_rpow (nu : ℝ) (hnu : 0 ≤ nu) :
    Monotone (fun n : ℕ => ((n : ℝ)) ^ nu) := fun _ _ hab =>
  Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.2 hab) hnu

/-! ## §E.2  The canonical split has at most two thresholds on a window -/

/-- **`canonicalSplit_two_thresholds`.**  `KERNEL-PROVED`.  On the physical window `[A, B]`,
for a fixed `d`, both canonical split conditions are single integer threshold tests. -/
theorem canonicalSplit_two_thresholds (d A B : ℕ) (nu : ℝ) (hnu : 0 ≤ nu) :
    ∃ t0 t2 : ℕ, ∀ n : ℕ, A ≤ n → n ≤ B →
      (((d : ℝ) ≤ (n : ℝ) ^ nu ↔ t0 ≤ n) ∧ (((2 * d : ℕ) : ℝ) ≤ (n : ℝ) ^ nu ↔ t2 ≤ n)) := by
  obtain ⟨t0, h0⟩ := exists_threshold_of_monotone (monotone_rpow nu hnu) (d : ℝ) A B
  obtain ⟨t2, h2⟩ := exists_threshold_of_monotone (monotone_rpow nu hnu) ((2 * d : ℕ) : ℝ) A B
  exact ⟨t0, t2, fun n hA hB => ⟨h0 n hA hB, h2 n hA hB⟩⟩

/-- The physical canonical-split coefficient at `n` for a fixed `d`:
`1_{d ≤ n^ν} − 1_{2d ∣ n} · 1_{2d ≤ n^ν}`. -/
noncomputable def splitCoeff (d : ℕ) (nu : ℝ) (n : ℕ) : ℝ :=
  (if (d : ℝ) ≤ (n : ℝ) ^ nu then 1 else 0)
    - (if 2 * d ∣ n then (1 : ℝ) else 0) * (if 2 * (d : ℝ) ≤ (n : ℝ) ^ nu then 1 else 0)

/-- **`canonicalSplitFourInterval`.**  `KERNEL-PROVED`.  On the physical window the canonical
coefficient is a signed sum of at most four interval indicators: two thresholds `t₀`, `t₂`,
each used on each of the two residue classes of `2d`. -/
theorem canonicalSplitFourInterval (d A B : ℕ) (nu : ℝ) (hnu : 0 ≤ nu) :
    ∃ t0 t2 : ℕ, ∀ n : ℕ, A ≤ n → n ≤ B →
      splitCoeff d nu n
        = (if t0 ≤ n then (1 : ℝ) else 0)
          - (if 2 * d ∣ n then (1 : ℝ) else 0) * (if t2 ≤ n then (1 : ℝ) else 0) := by
  obtain ⟨t0, t2, h⟩ := canonicalSplit_two_thresholds d A B nu hnu
  refine ⟨t0, t2, fun n hA hB => ?_⟩
  obtain ⟨h0, h2⟩ := h n hA hB
  classical
  push_cast at h2
  unfold splitCoeff
  rw [if_congr h0 rfl rfl, if_congr h2 rfl rfl]

/-- **`canonicalSplit_upward_closed`.**  `KERNEL-PROVED`.  The split, once switched on, stays
on: the number of changes over the window is therefore at most one per condition. -/
theorem canonicalSplit_upward_closed (d : ℕ) (nu : ℝ) (hnu : 0 ≤ nu) {m n : ℕ} (hmn : m ≤ n)
    (hm : (d : ℝ) ≤ (m : ℝ) ^ nu) : (d : ℝ) ≤ (n : ℝ) ^ nu :=
  le_trans hm (monotone_rpow nu hnu hmn)

/-! ## §E.3  The isolated numerical exponent instance -/

/-- **`crossing_at_half_exponent`.**  `KERNEL-PROVED`, exactly (no numerical approximation):
for the exponent `ν = 1/2` the canonical threshold is the exact integer `d ^ 2`, i.e.
`d ≤ n^(1/2) ↔ d² ≤ n`. -/
theorem crossing_at_half_exponent (d n : ℕ) :
    ((d : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) ↔ d ^ 2 ≤ n) := by
  have hn : ((n : ℝ)) ^ ((1 : ℝ) / 2) = Real.sqrt n := by
    rw [Real.sqrt_eq_rpow]
  rw [hn, show ((d : ℝ)) = Real.sqrt ((d : ℝ) ^ 2) by rw [Real.sqrt_sq (by positivity)],
    Real.sqrt_le_sqrt_iff (by positivity)]
  exact_mod_cast Iff.rfl

end September3CanonicalSplit
end Erdos287
