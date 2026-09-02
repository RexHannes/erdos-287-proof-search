import Mathlib

/-!
# The finite sublemmas of the `N2` λ-collar argument

```
Ω(n) ≤ 6 FROM σ > 1/7                    : KERNEL-PROVED
|H_ε(n)| ≤ 64 FROM ≤ 6 COORDINATES       : KERNEL-PROVED (conditional on |g_ε| ≤ 1)
SQUAREFUL / SQUAREFREE SPLIT             : KERNEL-PROVED
SHIFTED PRIME / PROPER PRIME POWER SPLIT : KERNEL-PROVED
LOCAL ROOT COUNTS ν₂, ν_p                : KERNEL-PROVED
SINGULAR SERIES = 2·Bsrc                 : PAPER-CLOSED EXTERNAL (uninhabited input)
```

This module is **append-only**.  It kernel-proves the *elementary* parts of the `N2`
argument and nothing else: the analytic collar itself is not proved here, and the singular
series identity is kept as an explicit external input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace N2Finite

/-! ## §A  `σ > 1/7` and `σ·Ω(n) ≤ 1` force `Ω(n) ≤ 6` -/

/-- **`omega_le_six`.**  `KERNEL-PROVED`.

If `σ > 1/7` and `σ·Ω ≤ 1` then `Ω ≤ 6`. -/
theorem omega_le_six {sigma : ℝ} {Om : ℕ} (hs : 1 / 7 < sigma) (h : sigma * (Om : ℝ) ≤ 1) :
    Om ≤ 6 := by
  by_contra hcon
  push_neg at hcon
  have h7 : (7 : ℝ) ≤ (Om : ℝ) := by exact_mod_cast hcon
  have hpos : (0 : ℝ) < sigma := lt_trans (by norm_num) hs
  have : 1 < sigma * (Om : ℝ) := by nlinarith
  linarith

/-- **`omega_le_six_sharp`.**  `KERNEL-PROVED`.  The bound is sharp in the sense that
`Ω = 6` is compatible with the hypotheses. -/
theorem omega_le_six_sharp : ∃ sigma : ℝ, 1 / 7 < sigma ∧ sigma * (6 : ℝ) ≤ 1 := by
  refine ⟨1 / 6, by norm_num, by norm_num⟩

/-! ## §B  The at-most-six-coordinate expansion gives `|H_ε(n)| ≤ 64` -/

/-- **`subvector_expansion_bound`.**  `KERNEL-PROVED`.

If the certificate value is expanded over the subvectors of at most six coordinates and each
term is bounded by `1` in absolute value, the total is bounded by `2⁶ = 64`. -/
theorem subvector_expansion_bound {coords : Finset ℕ} (hc : coords.card ≤ 6)
    (g : Finset ℕ → ℝ) (hg : ∀ S, |g S| ≤ 1) :
    |∑ S ∈ coords.powerset, g S| ≤ 64 := by
  have h1 : |∑ S ∈ coords.powerset, g S| ≤ ∑ S ∈ coords.powerset, |g S| :=
    Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ S ∈ coords.powerset, |g S| ≤ ∑ _S ∈ coords.powerset, (1 : ℝ) :=
    Finset.sum_le_sum fun S _ => hg S
  have h3 : ∑ _S ∈ coords.powerset, (1 : ℝ) = (coords.powerset.card : ℝ) := by simp
  have h4 : coords.powerset.card = 2 ^ coords.card := Finset.card_powerset coords
  have h5 : (2 : ℕ) ^ coords.card ≤ 64 := by
    calc (2 : ℕ) ^ coords.card ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hc
      _ = 64 := by norm_num
  have h6 : ((coords.powerset.card : ℝ)) ≤ 64 := by
    rw [h4]; exact_mod_cast h5
  linarith [h1, h2, h3 ▸ h2]

/-! ## §C  The disjoint splittings -/

/-- **`squarefree_split`.**  `KERNEL-PROVED`.  Any finite set of integers splits disjointly
into its squarefree and its squareful part. -/
theorem squarefree_split (S : Finset ℕ) :
    S.filter (fun n => Squarefree n) ∪ S.filter (fun n => ¬ Squarefree n) = S ∧
    Disjoint (S.filter (fun n => Squarefree n)) (S.filter (fun n => ¬ Squarefree n)) := by
  classical
  refine ⟨Finset.filter_union_filter_not_eq _ _, Finset.disjoint_filter_filter_not _ _ _⟩

/-- **`shifted_prime_split`.**  `KERNEL-PROVED`.  A finite set of prime powers splits
disjointly into the shifted primes and the proper shifted prime powers. -/
theorem shifted_prime_split (S : Finset ℕ) :
    S.filter (fun n => Nat.Prime n) ∪ S.filter (fun n => ¬ Nat.Prime n) = S ∧
    Disjoint (S.filter (fun n => Nat.Prime n)) (S.filter (fun n => ¬ Nat.Prime n)) := by
  classical
  refine ⟨Finset.filter_union_filter_not_eq _ _, Finset.disjoint_filter_filter_not _ _ _⟩

/-- **`proper_prime_power_characterisation`.**  `KERNEL-PROVED`.

Inside the prime powers, "not prime" is exactly "proper prime power". -/
theorem proper_prime_power_characterisation {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    ¬ Nat.Prime (p ^ k) ↔ 2 ≤ k := by
  constructor
  · intro h
    by_contra hk2
    push_neg at hk2
    have hk1 : k = 1 := by omega
    rw [hk1, pow_one] at h
    exact h hp
  · intro hk2 hprime
    obtain ⟨-, hk1⟩ := (Nat.Prime.pow_eq_iff hprime).1 rfl
    omega

/-! ## §D  The local root counts -/

/-- The local root count of `x(x + M) ≡ 0` modulo a prime `p`. -/
def rootCount (p : ℕ) [Fact p.Prime] (M : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : ZMod p => x * (x + (M : ZMod p)) = 0)).card

/-- **`rootCount_of_dvd`.**  `KERNEL-PROVED`.  If `p ∣ M` there is exactly one root. -/
theorem rootCount_of_dvd (p : ℕ) [Fact p.Prime] (M : ℕ) (hM : (M : ZMod p) = 0) :
    rootCount p M = 1 := by
  classical
  have hset : (Finset.univ.filter (fun x : ZMod p => x * (x + (M : ZMod p)) = 0))
      = {0} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hM, add_zero,
      mul_self_eq_zero]
  rw [rootCount, hset, Finset.card_singleton]

/-- **`rootCount_of_not_dvd`.**  `KERNEL-PROVED`.  If `p ∤ M` there are exactly two roots. -/
theorem rootCount_of_not_dvd (p : ℕ) [Fact p.Prime] (M : ℕ) (hM : (M : ZMod p) ≠ 0) :
    rootCount p M = 2 := by
  classical
  have hset : (Finset.univ.filter (fun x : ZMod p => x * (x + (M : ZMod p)) = 0))
      = {0, -(M : ZMod p)} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, mul_eq_zero]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linear_combination h)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by rw [h]; ring)
  have hne : (0 : ZMod p) ∉ ({-(M : ZMod p)} : Finset (ZMod p)) := by
    simp only [Finset.mem_singleton]
    intro h
    exact hM (by rw [← neg_eq_zero, ← h])
  rw [rootCount, hset, Finset.card_insert_of_notMem hne, Finset.card_singleton]

/-- **`nu_two`.**  `KERNEL-PROVED`.  At `p = 2` the admissible residues are the odd ones:
`ν₂ = 1`. -/
theorem nu_two : (Finset.univ.filter (fun x : ZMod 2 => x ≠ 0)).card = 1 := by decide

/-- **`nu_odd_dvd`.**  `KERNEL-PROVED`.  For a prime `p` dividing `M` — in particular for
every odd such `p`, which is the case used by the collar argument — `ν_p = 1`.  Oddness
turns out not to be needed for this count. -/
theorem nu_odd_dvd {p : ℕ} [Fact p.Prime] {M : ℕ} (h : (p : ℕ) ∣ M) :
    rootCount p M = 1 :=
  rootCount_of_dvd p M ((ZMod.natCast_eq_zero_iff M p).2 h)

/-- **`nu_odd_not_dvd`.**  `KERNEL-PROVED`.  For a prime `p` not dividing `M` — in
particular for every odd such `p` — `ν_p = 2`.  Oddness turns out not to be needed. -/
theorem nu_odd_not_dvd {p : ℕ} [Fact p.Prime] {M : ℕ} (h : ¬ (p : ℕ) ∣ M) :
    rootCount p M = 2 :=
  rootCount_of_not_dvd p M (fun hz => h ((ZMod.natCast_eq_zero_iff M p).1 hz))

/-! ## §E  The singular-series identity as an external input -/

/-- **`SingularSeriesEqualsTwoBsrc`** — `PAPER-CLOSED EXTERNAL / UNINHABITED`.

The source identity `𝔖(M, s) = 2·Bsrc(M)`.  Mathlib's infinite Euler-product infrastructure
makes a direct kernel proof impractical, so the identity is retained as an explicit external
input and is **never inhabited here**. -/
structure SingularSeriesEqualsTwoBsrc (singularSeries : ℕ → ℝ) (Bsrc : ℕ → ℝ) : Prop where
  /-- The literal identity. -/
  identity : ∀ M : ℕ, singularSeries M = 2 * Bsrc M

/-- **`singularSeries_input_is_a_genuine_constraint`.**  `KERNEL-PROVED`.

The identity is a real constraint: explicit data refute it, so nothing here supplies it. -/
theorem singularSeries_input_is_a_genuine_constraint :
    ∃ (s B : ℕ → ℝ), ¬ SingularSeriesEqualsTwoBsrc s B := by
  refine ⟨fun _ => 1, fun _ => 0, ?_⟩
  intro h
  have := h.identity 0
  norm_num at this

end N2Finite
end Erdos287
