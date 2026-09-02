import RequestProject.CurrentProgramme.Run1BAdditiveCharacters

/-!
# RUN1B / d*wp provider — §1  the exact source type

```
SOURCE-EXACT d*wp DATA TYPE            : DEFINED (data only)
NO ANALYTIC INEQUALITY AS A FIELD      : KERNEL-PROVED COUNTERGUARD
SOURCE TYPE INHABITED                  : KERNEL-PROVED
```

This module is **append-only** and project-neutral.

The record `DwpSource` carries *exactly* the source data of a `q = d·w'` bilinear
configuration together with its literal hypotheses

```
gcd(d, r) = 1,   gcd(w', r) = 1,
d ∈ [D, 2D],     w' ∈ [W, 2W],
Q ≤ D·W ≤ 4Q     (the "DW ≍ Q" range condition),
D, W ≥ x^(1/3 − ε),
Q ≥ x^(13/18 − ε),
r ≤ x^(1/2 + ε).
```

**Semantic hygiene.**  The desired analytic contraction inequality is *not* a field of this
record.  This is machine-checked: `dwpSource_does_not_carry_the_contraction` exhibits an
inhabitant at which a candidate contraction claim is false, so no projection out of
`DwpSource` can deliver it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Run1B
namespace Source

open Run1B.Characters

/-- The inverse of `n` modulo `r`, as an integer representative in `[0, r)`. -/
def invMod (r : ℕ) (n : ℕ) : ℤ := (((((n : ZMod r))⁻¹).val : ℕ) : ℤ)

/-- **The source-exact `q = d·w'` data.**  Data and its literal physical hypotheses only:
the analytic conclusion is deliberately absent. -/
structure DwpSource where
  /-- The main parameter `x`. -/
  x : ℝ
  /-- The dyadic scale of the `d`-variable. -/
  D : ℝ
  /-- The dyadic scale of the `w'`-variable. -/
  W : ℝ
  /-- The scale of the modulus product `q = d·w'`. -/
  Q : ℝ
  /-- The `o(1)` exponent slack. -/
  epsilon : ℝ
  /-- The residue modulus `r`. -/
  r : ℕ
  /-- The numerator `A` of the reciprocal phase. -/
  A : ℤ
  /-- The support of the `d`-variable. -/
  Dset : Finset ℕ
  /-- The support of the `w'`-variable. -/
  Wset : Finset ℕ
  /-- The coefficient sequence `α_d`. -/
  alpha : ℕ → ℂ
  /-- The coefficient sequence `β_{w'}`. -/
  beta : ℕ → ℂ
  /-- `x ≥ 1`. -/
  hx : 1 ≤ x
  /-- The slack is nonnegative. -/
  heps : 0 ≤ epsilon
  /-- The modulus is positive. -/
  hr : 0 < r
  /-- Every `d` is positive, coprime to `r`, and dyadically located at `D`. -/
  hDset : ∀ a ∈ Dset, 0 < a ∧ Nat.Coprime a r ∧ (a : ℝ) ∈ Set.Icc D (2 * D)
  /-- Every `w'` is positive, coprime to `r`, and dyadically located at `W`. -/
  hWset : ∀ b ∈ Wset, 0 < b ∧ Nat.Coprime b r ∧ (b : ℝ) ∈ Set.Icc W (2 * W)
  /-- `DW ≍ Q`, lower half. -/
  hDWQ_lower : Q ≤ D * W
  /-- `DW ≍ Q`, upper half. -/
  hDWQ_upper : D * W ≤ 4 * Q
  /-- `D ≥ x^(1/3 − ε)`. -/
  hDlow : x ^ ((1 : ℝ) / 3 - epsilon) ≤ D
  /-- `W ≥ x^(1/3 − ε)`. -/
  hWlow : x ^ ((1 : ℝ) / 3 - epsilon) ≤ W
  /-- `Q ≥ x^(13/18 − ε)`. -/
  hQlow : x ^ ((13 : ℝ) / 18 - epsilon) ≤ Q
  /-- `r ≤ x^(1/2 + ε)`. -/
  hrup : (r : ℝ) ≤ x ^ ((1 : ℝ) / 2 + epsilon)

namespace DwpSource

variable (s : DwpSource)

/-- The modulus `q = d·w'` attached to a pair of source variables. -/
def q (a b : ℕ) : ℕ := a * b

/-- The literal `d*w'` bilinear sum with the reciprocal phase `e_r(A·(dw')⁻¹)`. -/
noncomputable def dwpSum : ℂ :=
  ∑ a ∈ s.Dset, ∑ b ∈ s.Wset, s.alpha a * s.beta b * eAdd s.r (s.A * invMod s.r (q a b))

end DwpSource

/-! ## §1.1  Elementary consequences of the source hypotheses -/

/-- **`q_coprime_r`.**  `KERNEL-PROVED`.  `gcd(d, r) = gcd(w', r) = 1 ⇒ gcd(q, r) = 1`. -/
theorem q_coprime_r (s : DwpSource) {a b : ℕ} (ha : a ∈ s.Dset) (hb : b ∈ s.Wset) :
    Nat.Coprime (DwpSource.q a b) s.r :=
  Nat.Coprime.mul_left (s.hDset a ha).2.1 (s.hWset b hb).2.1

/-- **`q_pos`.**  `KERNEL-PROVED`. -/
theorem q_pos (s : DwpSource) {a b : ℕ} (ha : a ∈ s.Dset) (hb : b ∈ s.Wset) :
    0 < DwpSource.q a b :=
  Nat.mul_pos (s.hDset a ha).1 (s.hWset b hb).1

/-- **`Q_le_four_Q`.**  `KERNEL-PROVED`.  The range condition `DW ≍ Q` in usable form. -/
theorem DW_between (s : DwpSource) : s.Q ≤ s.D * s.W ∧ s.D * s.W ≤ 4 * s.Q :=
  ⟨s.hDWQ_lower, s.hDWQ_upper⟩

/-! ## §1.2  Semantic firewall: the analytic inequality is not a field -/

/-- A candidate analytic contraction claim for a `d*w'` source: an arbitrary-log saving for
the literal bilinear sum.  It is *not* part of `DwpSource`. -/
def ContractionClaim (s : DwpSource) (Aexp : ℝ) : Prop :=
  ‖s.dwpSum‖ ≤ s.x / (Real.log s.x) ^ (Aexp : ℝ)

/-- An explicit inhabitant of the source type: `x = 1`, `D = W = Q = 1`, `r = 1`, a single
`d` and a single `w'`, unit coefficients. -/
noncomputable def sampleSource : DwpSource where
  x := 1
  D := 1
  W := 1
  Q := 1
  epsilon := 0
  r := 1
  A := 0
  Dset := {1}
  Wset := {1}
  alpha := fun _ => 1
  beta := fun _ => 1
  hx := le_refl 1
  heps := le_refl 0
  hr := Nat.one_pos
  hDset := by
    intro a ha
    simp only [Finset.mem_singleton] at ha
    subst ha
    refine ⟨Nat.one_pos, Nat.coprime_one_right 1, ?_⟩
    norm_num
  hWset := by
    intro b hb
    simp only [Finset.mem_singleton] at hb
    subst hb
    refine ⟨Nat.one_pos, Nat.coprime_one_right 1, ?_⟩
    norm_num
  hDWQ_lower := by norm_num
  hDWQ_upper := by norm_num
  hDlow := by rw [Real.one_rpow]
  hWlow := by rw [Real.one_rpow]
  hQlow := by rw [Real.one_rpow]
  hrup := by rw [Real.one_rpow]; norm_num

/-- **`dwpSource_inhabited`.**  `KERNEL-PROVED`. -/
theorem dwpSource_inhabited : Nonempty DwpSource := ⟨sampleSource⟩

/-- **`sampleSource_dwpSum`.**  `KERNEL-PROVED`.  The sample sum is `1`. -/
theorem sampleSource_dwpSum : sampleSource.dwpSum = 1 := by
  simp [DwpSource.dwpSum, sampleSource, DwpSource.q, eAdd]

/-- **`dwpSource_does_not_carry_the_contraction`.**  `KERNEL-PROVED` semantic counterguard.

For every exponent `Aexp > 0` the contraction claim fails at the explicit inhabitant, so it
is **not** derivable from the source record: no field of `DwpSource`, and no projection out
of it, can supply the analytic inequality. -/
theorem dwpSource_does_not_carry_the_contraction (Aexp : ℝ) (hA : 0 < Aexp) :
    ¬ ∀ s : DwpSource, ContractionClaim s Aexp := by
  intro h
  have h1 := h sampleSource
  rw [ContractionClaim, sampleSource_dwpSum] at h1
  have hx : sampleSource.x = 1 := rfl
  rw [hx, Real.log_one] at h1
  rw [Real.zero_rpow hA.ne', div_zero] at h1
  simp only [norm_one] at h1
  linarith

end Source
end Run1B
