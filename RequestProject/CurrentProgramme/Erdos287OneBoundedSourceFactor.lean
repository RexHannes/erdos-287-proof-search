import Mathlib

/-!
# The one-bounded source factorisation `A_{τ,ρ}(a) · B_{τ,ρ}(b)`

`PERRON-PARENT-1BOUNDED-FACTOR45 : SOURCE/ALGEBRAIC PART KERNEL-PROVED`

This module is **append-only**.

It formalises the *purely algebraic* part of the one-bounded source
factorisation: the outer factors

```
A_{τ,ρ}(a) = 1_{a ∈ 𝒜} · e(θ_A(a)),
B_{τ,ρ}(b) = 1_{b ∈ ℬ} · μ(b) · e(θ_B(b)),
```

their elementary bounds `‖A‖ ≤ 1`, `‖B‖ ≤ 1`, the exact bilinear
factorisation of the double sum, and the structural record that the **Möbius
sign belongs linearly to the `B` factor**.

**Firewall.**  Nothing analytic is proved: no cancellation, no Perron contour,
no bilinear saving.  The complex/Perron implementation of the phases is kept
abstract (they are arbitrary real functions), and the only inequalities used are
`|μ| ≤ 1` and `|e(θ)| = 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open ArithmeticFunction

namespace Erdos287
namespace OneBoundedFactor

/-! ## §1  The factor data -/

/-- **`SourceFactorData`** — the finite data of a `(τ, ρ)` source factorisation: the two
supports and the two (abstract) phase functions. -/
structure SourceFactorData where
  /-- The parameter `τ`. -/
  tau : ℕ
  /-- The parameter `ρ`. -/
  rho : ℕ
  /-- The support of the `a`-variable. -/
  Asupport : Finset ℕ
  /-- The support of the `b`-variable. -/
  Bsupport : Finset ℕ
  /-- The abstract phase of the `A` factor. -/
  Aphase : ℕ → ℝ
  /-- The abstract phase of the `B` factor. -/
  Bphase : ℕ → ℝ

namespace SourceFactorData

variable (d : SourceFactorData)

/-- The outer factor `A_{τ,ρ}(a)`. -/
noncomputable def Afactor (a : ℕ) : ℂ :=
  if a ∈ d.Asupport then Complex.exp ((d.Aphase a : ℝ) * Complex.I) else 0

/-- The outer factor `B_{τ,ρ}(b)`, carrying the Möbius sign. -/
noncomputable def Bfactor (b : ℕ) : ℂ :=
  if b ∈ d.Bsupport then
    ((ArithmeticFunction.moebius b : ℤ) : ℂ) * Complex.exp ((d.Bphase b : ℝ) * Complex.I)
  else 0

/-- The `B` factor with a general integer coefficient vector in the Möbius slot. -/
noncomputable def BfactorGen (m : ℕ → ℤ) (b : ℕ) : ℂ :=
  if b ∈ d.Bsupport then ((m b : ℤ) : ℂ) * Complex.exp ((d.Bphase b : ℝ) * Complex.I)
  else 0

/-- The hypothetical placement of a coefficient vector in the `A` slot. -/
noncomputable def AfactorGen (m : ℕ → ℤ) (a : ℕ) : ℂ :=
  if a ∈ d.Asupport then ((m a : ℤ) : ℂ) * Complex.exp ((d.Aphase a : ℝ) * Complex.I)
  else 0

/-! ## §2  Elementary one-boundedness -/

/-- `|μ(n)| ≤ 1`: the only elementary input of this module. -/
theorem norm_moebius_le_one (n : ℕ) :
    ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
  rcases eq_or_ne (ArithmeticFunction.moebius n) 0 with h | h
  · simp [h]
  · rcases ArithmeticFunction.moebius_ne_zero_iff_eq_or.mp h with h1 | h1 <;> simp [h1]

/-- **`norm_Afactor_le_one`.**  `KERNEL-PROVED`.  `‖A_{τ,ρ}(a)‖ ≤ 1`. -/
theorem norm_Afactor_le_one (a : ℕ) : ‖d.Afactor a‖ ≤ 1 := by
  unfold Afactor
  split
  · simp [Complex.norm_exp_ofReal_mul_I]
  · simp

/-- **`norm_Bfactor_le_one`.**  `KERNEL-PROVED`.  `‖B_{τ,ρ}(b)‖ ≤ 1`. -/
theorem norm_Bfactor_le_one (b : ℕ) : ‖d.Bfactor b‖ ≤ 1 := by
  unfold Bfactor
  split
  · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact norm_moebius_le_one b
  · simp

/-! ## §3  The exact bilinear factorisation -/

/-- **`bilinear_factorisation`.**  `KERNEL-PROVED`.

The double source sum factorises exactly into the product of the two outer sums. -/
theorem bilinear_factorisation :
    ∑ a ∈ d.Asupport, ∑ b ∈ d.Bsupport, d.Afactor a * d.Bfactor b
      = (∑ a ∈ d.Asupport, d.Afactor a) * (∑ b ∈ d.Bsupport, d.Bfactor b) :=
  (Finset.sum_mul_sum _ _ _ _).symm

/-- **`bilinear_trivial_bound`.**  `KERNEL-PROVED`.

The only bound available from one-boundedness alone is the trivial one; in particular no
cancellation is claimed anywhere in this module. -/
theorem bilinear_trivial_bound :
    ‖∑ a ∈ d.Asupport, ∑ b ∈ d.Bsupport, d.Afactor a * d.Bfactor b‖
      ≤ (d.Asupport.card : ℝ) * (d.Bsupport.card : ℝ) := by
  refine le_trans (norm_sum_le _ _) ?_
  have hstep : ∀ a ∈ d.Asupport,
      ‖∑ b ∈ d.Bsupport, d.Afactor a * d.Bfactor b‖ ≤ (d.Bsupport.card : ℝ) := by
    intro a _
    refine le_trans (norm_sum_le _ _) ?_
    have : ∀ b ∈ d.Bsupport, ‖d.Afactor a * d.Bfactor b‖ ≤ 1 := by
      intro b _
      rw [norm_mul]
      exact mul_le_one₀ (d.norm_Afactor_le_one a) (norm_nonneg _) (d.norm_Bfactor_le_one b)
    calc ∑ b ∈ d.Bsupport, ‖d.Afactor a * d.Bfactor b‖
        ≤ ∑ _b ∈ d.Bsupport, (1:ℝ) := Finset.sum_le_sum this
      _ = (d.Bsupport.card : ℝ) := by simp
  calc ∑ a ∈ d.Asupport, ‖∑ b ∈ d.Bsupport, d.Afactor a * d.Bfactor b‖
      ≤ ∑ _a ∈ d.Asupport, (d.Bsupport.card : ℝ) := Finset.sum_le_sum hstep
    _ = (d.Asupport.card : ℝ) * (d.Bsupport.card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-! ## §4  The Möbius sign belongs linearly to `B` -/

/-- The Möbius coefficient vector is the one placed in the `B` slot. -/
theorem BfactorGen_moebius :
    d.BfactorGen (fun b => ArithmeticFunction.moebius b) = d.Bfactor := by
  funext b
  unfold BfactorGen Bfactor
  rfl

/-- **`BfactorGen_add`.**  `KERNEL-PROVED`.  The `B` slot is additive in the coefficient
vector. -/
theorem BfactorGen_add (m₁ m₂ : ℕ → ℤ) (b : ℕ) :
    d.BfactorGen (fun n => m₁ n + m₂ n) b = d.BfactorGen m₁ b + d.BfactorGen m₂ b := by
  unfold BfactorGen
  split
  · push_cast; ring
  · ring

/-- **`BfactorGen_smul`.**  `KERNEL-PROVED`.  The `B` slot is homogeneous in the
coefficient vector. -/
theorem BfactorGen_smul (c : ℤ) (m : ℕ → ℤ) (b : ℕ) :
    d.BfactorGen (fun n => c * m n) b = (c : ℂ) * d.BfactorGen m b := by
  unfold BfactorGen
  split
  · push_cast; ring
  · ring

/-- **`bilinear_linear_in_moebius_slot`.**  `KERNEL-PROVED`.

The whole double sum is linear in the coefficient vector occupying the `B` slot: this is
the exact sense in which the Möbius sign belongs to `B`. -/
theorem bilinear_linear_in_moebius_slot (m₁ m₂ : ℕ → ℤ) :
    ∑ a ∈ d.Asupport, ∑ b ∈ d.Bsupport, d.Afactor a * d.BfactorGen (fun n => m₁ n + m₂ n) b
      = (∑ a ∈ d.Asupport, ∑ b ∈ d.Bsupport, d.Afactor a * d.BfactorGen m₁ b)
        + ∑ a ∈ d.Asupport, ∑ b ∈ d.Bsupport, d.Afactor a * d.BfactorGen m₂ b := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [d.BfactorGen_add m₁ m₂ b]
  ring

/-- **`general_coefficients_do_not_fit_the_A_slot`.**  `KERNEL-PROVED`.

Counterguard: the `A` slot is reserved for one-bounded coefficients.  A coefficient vector
of size larger than one placed in the `A` slot destroys one-boundedness, so the placement
of the Möbius sign in `B` is not a free relabelling. -/
theorem general_coefficients_do_not_fit_the_A_slot (a : ℕ) (ha : a ∈ d.Asupport) :
    ¬ ‖d.AfactorGen (fun _ => (2 : ℤ)) a‖ ≤ 1 := by
  unfold AfactorGen
  rw [if_pos ha, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  norm_num

end SourceFactorData
end OneBoundedFactor
end Erdos287
