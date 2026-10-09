import Mathlib

/-!
# Anchored V3 — exponential-tilt / Fourier closure interface

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

This module contains **definitions and exact finite identities only**, plus the purely logical
conditional bridge.  The analytic Fourier-inversion estimate is *not* proved and is *not*
introduced as an axiom: it appears only as the named OPEN proposition `AntiHoleBridge`, which is
never inhabited.

For a finite nonnegative coefficient function `c` with support `supp` we define the exponential
tilt

```
Z(λ) = ∑_j c j e^{λ j},        P_λ(j) = c j e^{λ j} / Z(λ),
mean(λ) = ∑_j j P_λ(j),        var(λ) = ∑_j (j - mean λ)² P_λ(j),
φ_λ(θ) = ∑_j P_λ(j) e^{i θ j}.
```

Exact finite facts proved here: positivity of the normaliser, that `P_λ` is a probability
distribution on the support, and `‖φ_λ(θ)‖ ≤ 1`.

`FourierAntiHoleCriterion K T` packages the target-specific hypotheses of the intended analytic
theorem (a tilt with mean exactly `T`, standard deviation `σ ≥ 1`, and the arc-integral bound
`∫_{1/σ ≤ |θ| ≤ π} ‖φ_λ‖ < 5 / (3σ)`).  `AntiHoleBridge` is the OPEN statement that this
criterion forces `c T > 0`.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV3

/-- A finite nonnegative integer coefficient function with an explicit finite support. -/
structure FiniteCoeff where
  /-- the finite support -/
  supp : Finset ℕ
  /-- the coefficients -/
  c : ℕ → ℕ
  /-- coefficients vanish off the support -/
  hsupp : ∀ j, c j ≠ 0 → j ∈ supp

namespace FiniteCoeff

variable (K : FiniteCoeff)

/-- The exponential-tilt normaliser `Z(λ) = ∑_j c j e^{λ j} = H(e^λ)`. -/
noncomputable def Z (lam : ℝ) : ℝ := ∑ j ∈ K.supp, (K.c j : ℝ) * Real.exp (lam * j)

/-- The tilted probability of the value `j`. -/
noncomputable def prob (lam : ℝ) (j : ℕ) : ℝ := (K.c j : ℝ) * Real.exp (lam * j) / K.Z lam

/-- The tilted mean. -/
noncomputable def mean (lam : ℝ) : ℝ := ∑ j ∈ K.supp, (j : ℝ) * K.prob lam j

/-- The tilted variance. -/
noncomputable def var (lam : ℝ) : ℝ :=
  ∑ j ∈ K.supp, ((j : ℝ) - K.mean lam) ^ 2 * K.prob lam j

/-- The exact finite characteristic function of the tilted distribution. -/
noncomputable def char (lam θ : ℝ) : ℂ :=
  ∑ j ∈ K.supp, (K.prob lam j : ℂ) * Complex.exp (((θ * j : ℝ) : ℂ) * Complex.I)

/-- **The normaliser is positive** as soon as some coefficient on the support is positive. -/
theorem Z_pos {lam : ℝ} (h : ∃ j ∈ K.supp, 0 < K.c j) : 0 < K.Z lam := by
  obtain ⟨j₀, hj₀, hcj₀⟩ := h
  refine Finset.sum_pos' (fun j _ => ?_) ⟨j₀, hj₀, ?_⟩
  · positivity
  · have : (0:ℝ) < (K.c j₀ : ℝ) := by exact_mod_cast hcj₀
    positivity

theorem prob_nonneg (lam : ℝ) (j : ℕ) (hZ : 0 < K.Z lam) : 0 ≤ K.prob lam j := by
  unfold prob
  positivity

/-- **The tilted weights form a probability distribution on the support.** -/
theorem sum_prob (lam : ℝ) (hZ : 0 < K.Z lam) : ∑ j ∈ K.supp, K.prob lam j = 1 := by
  unfold prob
  rw [← Finset.sum_div, div_eq_one_iff_eq hZ.ne']
  rfl

/-- **The characteristic function has modulus at most one.** -/
theorem norm_char_le_one (lam θ : ℝ) (hZ : 0 < K.Z lam) : ‖K.char lam θ‖ ≤ 1 := by
  have hbound : ‖K.char lam θ‖ ≤ ∑ j ∈ K.supp, ‖(K.prob lam j : ℂ) *
      Complex.exp (((θ * j : ℝ) : ℂ) * Complex.I)‖ := norm_sum_le _ _
  have hterm : ∀ j ∈ K.supp,
      ‖(K.prob lam j : ℂ) * Complex.exp (((θ * j : ℝ) : ℂ) * Complex.I)‖ = K.prob lam j := by
    intro j _
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (K.prob_nonneg lam j hZ)]
  rw [Finset.sum_congr rfl hterm] at hbound
  rw [K.sum_prob lam hZ] at hbound
  exact hbound

/-- The target-specific hypotheses of the intended Fourier anti-hole theorem. -/
structure AntiHoleInput (T : ℕ) where
  /-- the tilt parameter -/
  lam : ℝ
  /-- the standard deviation of the tilted distribution -/
  sigma : ℝ
  /-- the variance is at least one -/
  hsigma : 1 ≤ sigma
  /-- `sigma` is the standard deviation -/
  hvar : sigma ^ 2 = K.var lam
  /-- the tilt is centred on the target -/
  hmean : K.mean lam = (T : ℝ)
  /-- the arc-integral bound `∫_{1/σ ≤ |θ| ≤ π} ‖φ_λ‖ < 5 / (3σ)` -/
  harc : 2 * (∫ θ in (1 / sigma)..Real.pi, ‖K.char lam θ‖) < 5 / (3 * sigma)

/-- The Fourier anti-hole criterion at the target `T`. -/
def FourierAntiHoleCriterion (T : ℕ) : Prop := Nonempty (K.AntiHoleInput T)

end FiniteCoeff

/-- **OPEN analytic owner.**  The Fourier-inversion anti-hole theorem: the target-specific
criterion forces the target coefficient to be positive.  This proposition is deliberately **not**
inhabited here; it is neither proved nor assumed as an axiom. -/
def AntiHoleBridge : Prop :=
  ∀ (K : FiniteCoeff) (T : ℕ), K.FourierAntiHoleCriterion T → 0 < K.c T

/-- The purely logical conditional bridge: given the OPEN analytic input and the finite
criterion, the target coefficient is positive. -/
theorem coeff_pos_of_antiHoleBridge (h : AntiHoleBridge) (K : FiniteCoeff) (T : ℕ)
    (hK : K.FourierAntiHoleCriterion T) : 0 < K.c T := h K T hK

end AnchoredV3
end Erdos287
