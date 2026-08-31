import Mathlib
import RequestProject.Erdos287.AggregateEulerLocal3221

/-!
# V24, §4–§5 — the Euler uniformity layer

`BALANCED7-EULER-UNIFORMITY45`

## What is proved finitely

The aggregate object is

```
    J_P(z) = ∑_{q ≤ z, (q,2P)=1} μ(q)/φ(q) · log(z/q),
```

whose candidate Dirichlet-series factorisation is `F_P(w) = H_P(w)/ζ(1+w)`.  For `p ∤ 2P`
the **repaired** local factor is

```
    1 − p^{-w} / [ p(p−1)(1 − p^{-1-w}) ].
```

Banked here, finitely and with no contour argument:

* `repairedLocalFactor_sub_one_bound` — for real `w ≥ −1/4` and `p ≥ 2`,
  `|local factor − 1| ≤ 6 · p^{-7/4}`, an explicit constant of the shape `C p^{-7/4}`;
* `balancedSeven_at_most_seven_onP_factors` — a balanced seven-prime `P` has at most seven
  distinct prime divisors, so at most seven local factors need the `p ∣ P` correction;
* the `w = 0` identity `H_P(0) = 2B(P)` is already banked in
  `AggregateEulerLocal3221.aggregateEuler_H0_eq_twoB` and is *reused*, not restated.

## What is not proved

No complex-analytic contour argument is invented in Lean.  The uniform estimate is carried
by the uninhabited interface `BalancedSevenEulerUniformity287Input` of §5, which records
the factorisation, the uniform `H_P(w) = O(1)` bound, Perron/Riesz inversion, the zero-free
contour, both physical cutoffs `z = 2P ± 1`, and the minimum sufficient fixed exponent
`A0` (the current research audit reports `A0 = 2` as sufficient; that number is carried as
*metadata*, not as a theorem).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace V24Euler

open Erdos287.V23Euler

/-! ## §4.1  The repaired local factor -/

/-- The repaired off-`P` local factor `1 − p^{-w}/[p(p−1)(1 − p^{-1-w})]`, for real `w`. -/
noncomputable def repairedLocalFactor (p w : ℝ) : ℝ :=
  1 - p ^ (-w) / (p * (p - 1) * (1 - p ^ (-1 - w)))

/-- **`repairedLocalFactor_sub_one_bound`.**  `LEAN_PROVED`.

For every prime scale `p ≥ 2` and every real `w ≥ −1/4`,

```
    |local factor − 1| ≤ 6 · p^{-7/4}.
```

The exponent `7/4` is what makes the product over `p` absolutely convergent on
`Re w ≥ −1/4`; the constant `6` is explicit.  (The complex-`w` version is part of the
external interface below; this is the real-`w` finite inequality.) -/
theorem repairedLocalFactor_sub_one_bound (p w : ℝ) (hp : 2 ≤ p) (hw : -1 / 4 ≤ w) :
    |repairedLocalFactor p w - 1| ≤ 6 * p ^ (-(7 : ℝ) / 4) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hnum : p ^ (-w) ≤ p ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have hnum0 : (0 : ℝ) < p ^ (-w) := Real.rpow_pos_of_pos hp0 _
  have h1 : p ^ (-1 - w) ≤ p ^ (-(3 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have h2 : (3 : ℝ) / 2 ≤ p ^ ((3 : ℝ) / 4) := by
    have hb : (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ p ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow (by norm_num) hp (by norm_num)
    have ha0 : (0 : ℝ) ≤ (2 : ℝ) ^ ((3 : ℝ) / 4) := (Real.rpow_pos_of_pos (by norm_num) _).le
    have h4 : ((3 : ℝ) / 2) ^ (4 : ℕ) ≤ ((2 : ℝ) ^ ((3 : ℝ) / 4)) ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ ((3 : ℝ) / 4)) 4, ← Real.rpow_mul (by norm_num)]
      norm_num
    have h32 : (3 : ℝ) / 2 ≤ (2 : ℝ) ^ ((3 : ℝ) / 4) :=
      le_of_pow_le_pow_left₀ (by norm_num) ha0 h4
    linarith
  have h3 : p ^ (-(3 : ℝ) / 4) ≤ 2 / 3 := by
    have heq : p ^ (-(3 : ℝ) / 4) = (p ^ ((3 : ℝ) / 4))⁻¹ := by
      rw [← Real.rpow_neg hp0.le]; norm_num
    rw [heq]
    have hpos : (0 : ℝ) < p ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hp0 _
    rw [inv_le_comm₀ hpos (by norm_num)]
    linarith
  have hden2 : (0 : ℝ) < 1 - p ^ (-1 - w) := by linarith
  have hpp0 : (0 : ℝ) < p * (p - 1) := by nlinarith
  have key : |repairedLocalFactor p w - 1|
      = p ^ (-w) / (p * (p - 1) * (1 - p ^ (-1 - w))) := by
    unfold repairedLocalFactor
    rw [show (1 - p ^ (-w) / (p * (p - 1) * (1 - p ^ (-1 - w))) - 1)
        = -(p ^ (-w) / (p * (p - 1) * (1 - p ^ (-1 - w)))) by ring, abs_neg,
      abs_of_pos (by positivity)]
  rw [key]
  have hlow : p ^ 2 / 6 ≤ p * (p - 1) * (1 - p ^ (-1 - w)) := by nlinarith
  have hstep : p ^ (-w) / (p * (p - 1) * (1 - p ^ (-1 - w)))
      ≤ p ^ ((1 : ℝ) / 4) / (p ^ 2 / 6) := by
    gcongr
  have hfin : p ^ ((1 : ℝ) / 4) / (p ^ (2 : ℕ) / 6) = 6 * p ^ (-(7 : ℝ) / 4) := by
    have h2r : (p : ℝ) ^ (2 : ℕ) = p ^ ((2 : ℝ)) := by
      rw [← Real.rpow_natCast p 2]; norm_num
    rw [h2r, div_div_eq_mul_div, mul_comm (p ^ ((1 : ℝ) / 4)) 6, mul_div_assoc,
      ← Real.rpow_sub hp0]
    norm_num
  exact le_trans hstep (le_of_eq hfin)

/-- The local factor is exactly `1` when the correcting term vanishes; the bound above is
therefore a genuine perturbation statement. -/
theorem repairedLocalFactor_eq_one_iff (p w : ℝ) (hp : 2 ≤ p)
    (hden : p * (p - 1) * (1 - p ^ (-1 - w)) ≠ 0) :
    repairedLocalFactor p w = 1 ↔ p ^ (-w) = 0 := by
  have hp0 : (0 : ℝ) < p := by linarith
  unfold repairedLocalFactor
  constructor
  · intro h
    have : p ^ (-w) / (p * (p - 1) * (1 - p ^ (-1 - w))) = 0 := by linarith
    exact (div_eq_zero_iff.mp this).resolve_right hden
  · intro h
    rw [h]
    simp

/-! ## §4.2  At most seven on-`P` corrections -/

/-- **`balancedSeven_at_most_seven_onP_factors`.**  `LEAN_PROVED`.

A balanced seven-prime `P = ∏_{i<7} p_i` has at most seven distinct prime divisors, so at
most seven local factors require the `p ∣ P` correction. -/
theorem balancedSeven_at_most_seven_onP_factors (pv : Fin 7 → ℕ) (h : ∀ i, (pv i).Prime) :
    (∏ i, pv i).primeFactors.card ≤ 7 := by
  classical
  have hsub : (∏ i, pv i).primeFactors ⊆ Finset.image pv Finset.univ := by
    intro q hq
    rw [Nat.mem_primeFactors] at hq
    obtain ⟨hqp, hdvd, _⟩ := hq
    obtain ⟨i, _, hi⟩ := (Nat.Prime.prime hqp).exists_mem_finset_dvd hdvd
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_univ _, ((Nat.prime_dvd_prime_iff_eq hqp (h i)).mp hi).symm⟩
  calc (∏ i, pv i).primeFactors.card ≤ (Finset.image pv Finset.univ).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin 7)).card := Finset.card_image_le
    _ = 7 := by simp

/-- The same bound for the odd prime divisors that actually carry the `(p−1)/(p−2)`
correction of `H_P(0)`. -/
theorem balancedSeven_at_most_seven_oddPrimeDivisors (pv : Fin 7 → ℕ)
    (h : ∀ i, (pv i).Prime) :
    (oddPrimeDivisors (∏ i, pv i)).card ≤ 7 :=
  le_trans (Finset.card_filter_le _ _) (balancedSeven_at_most_seven_onP_factors pv h)

/-- The `w = 0` identity `H_P(0) = 2B(P)` is the banked V23 result, reused verbatim. -/
theorem euler_H0_eq_twoB (S2 : ℝ) (P : ℕ) : H0 S2 P = 2 * BofP S2 P :=
  aggregateEuler_H0_eq_twoB S2 P

/-! ## §5  The external Euler-uniformity interface (uninhabited) -/

/-- **`BalancedSevenEulerUniformity287Input`** — `EXTERNAL / ANALYTIC / UNINHABITED`.

The analytic passage that this repository does **not** prove: the factorisation
`F_P = H_P/ζ`, a uniform `H_P(w) = O(1)` bound on the required contour, Perron/Riesz
inversion, a zero-free contour, and the resulting uniform estimate

```
    J_P(z) = 2B(P) + O(log^{-A0} z)
```

at both physical cutoffs `z = 2P + 1` and `z = 2P − 1`.  The field `A0min` records the
minimum sufficient fixed exponent; the current research audit reports `A0 = 2` as
sufficient, which is metadata carried by `eulerUniformity_reported_A0`, not a theorem. -/
structure BalancedSevenEulerUniformity287Input
    (family : Finset ℕ) (F H : ℕ → ℂ → ℂ) (zetaInv : ℂ → ℂ) (contour zeroFree : Set ℂ)
    (J : ℕ → ℝ → ℝ) (S2 Hbound A0min : ℝ) (perronInversion : Prop) : Prop where
  /-- The physical seven-prime family is nonempty. -/
  family_nonempty : family.Nonempty
  /-- The Dirichlet-series factorisation on the contour. -/
  factorisation : ∀ P ∈ family, ∀ w ∈ contour, F P w = H P w * zetaInv w
  /-- The uniform `O(1)` bound on `H_P`. -/
  uniform_H : ∀ P ∈ family, ∀ w ∈ contour, ‖H P w‖ ≤ Hbound
  /-- Perron / Riesz inversion is available in the form used. -/
  perron : perronInversion
  /-- The contour lies in the zero-free region. -/
  zero_free : contour ⊆ zeroFree
  /-- The resulting uniform estimate at `z = 2P + 1`. -/
  estimate_plus : ∀ P ∈ family,
    |J P (2 * (P : ℝ) + 1) - 2 * BofP S2 P|
      ≤ Hbound * (Real.log (2 * (P : ℝ) + 1)) ^ (-A0min)
  /-- The resulting uniform estimate at `z = 2P − 1`. -/
  estimate_minus : ∀ P ∈ family,
    |J P (2 * (P : ℝ) - 1) - 2 * BofP S2 P|
      ≤ Hbound * (Real.log (2 * (P : ℝ) - 1)) ^ (-A0min)
  /-- The declared minimum sufficient exponent is a genuine saving. -/
  A0min_pos : 0 < A0min

/-- The exponent the current research audit reports as sufficient.  **Metadata only.** -/
def eulerUniformity_reported_A0 : ℝ := 2

theorem eulerUniformity_reported_A0_pos : 0 < eulerUniformity_reported_A0 := by
  unfold eulerUniformity_reported_A0; norm_num

/-- **`eulerUniformity_not_automatic`.**  `LEAN_PROVED`.

The interface is a genuine restriction — explicit data refute it — so it is not discharged
by generalities, and it is not inhabited anywhere in this repository. -/
theorem eulerUniformity_not_automatic :
    ∃ (family : Finset ℕ) (F H : ℕ → ℂ → ℂ) (zetaInv : ℂ → ℂ) (contour zeroFree : Set ℂ)
      (J : ℕ → ℝ → ℝ) (S2 Hbound A0min : ℝ) (perronInversion : Prop),
      ¬ BalancedSevenEulerUniformity287Input family F H zetaInv contour zeroFree J S2
        Hbound A0min perronInversion := by
  refine ⟨∅, fun _ _ => 0, fun _ _ => 0, fun _ => 0, ∅, ∅, fun _ _ => 0, 0, 0, 1, True, ?_⟩
  intro h
  simpa using h.family_nonempty

end V24Euler
end Erdos287
