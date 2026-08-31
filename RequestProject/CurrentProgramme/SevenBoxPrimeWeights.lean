import Mathlib
import RequestProject.CurrentProgramme.ThreePlusFourProductAlgebra

/-!
# CurrentProgramme (post-Balanced7 pass) §3 — literal seven-box prime weights

The source form of the seven prime-box weights is

```
    ω_i(p) = 1_P(p) · V_i(p/Y) · p^{i t_i},
```

with `0 ≤ V_i ≤ 1`.  Only **finite** consequences are formalised:

* `omegaBox_eq_zero_of_not_prime` — the weight is supported on primes;
* `norm_omegaBox_le_one` — `|ω_i(p)| ≤ 1`;
* `norm_omegaBox_eq_V` — the modulus is exactly the smooth cutoff value, the archimedean
  twist `p^{i t}` being unimodular.

No prime-counting / PNT asymptotic is formalised here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace PostBalanced7Pro

/-- The literal prime-box weight `ω(p) = 1_P(p) · V(p/Y) · p^{i t}`, with `V` the smooth
cutoff profile evaluated at `p/Y` and `t` the archimedean twist. -/
noncomputable def omegaBox (V : ℝ → ℝ) (Y t : ℝ) (p : ℕ) : ℂ :=
  if p.Prime then (V ((p : ℝ) / Y) : ℂ) * Complex.exp (t * Real.log p * Complex.I) else 0

theorem omegaBox_eq_zero_of_not_prime {V : ℝ → ℝ} {Y t : ℝ} {p : ℕ} (hp : ¬ p.Prime) :
    omegaBox V Y t p = 0 := by
  simp [omegaBox, hp]

/-- **`norm_omegaBox_eq_V`.**  `LEAN_PROVED`.

The archimedean twist is unimodular, so the modulus of the weight at a prime is `|V(p/Y)|`. -/
theorem norm_omegaBox_eq_V {V : ℝ → ℝ} {Y t : ℝ} {p : ℕ} (hp : p.Prime) :
    ‖omegaBox V Y t p‖ = |V ((p : ℝ) / Y)| := by
  have htw : ‖Complex.exp ((t * Real.log p : ℝ) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  simp only [omegaBox, hp, if_true, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [show ((t : ℂ) * (Real.log p : ℂ) * Complex.I)
      = ((t * Real.log p : ℝ) : ℂ) * Complex.I by push_cast; ring, htw, mul_one]

/-- **`norm_omegaBox_le_one`.**  `LEAN_PROVED`.

With a normalised profile `0 ≤ V ≤ 1` the literal weight satisfies `|ω_i(p)| ≤ 1`. -/
theorem norm_omegaBox_le_one {V : ℝ → ℝ} {Y t : ℝ} (hV : ∀ x : ℝ, 0 ≤ V x ∧ V x ≤ 1) (p : ℕ) :
    ‖omegaBox V Y t p‖ ≤ 1 := by
  by_cases hp : p.Prime
  · rw [norm_omegaBox_eq_V hp, abs_of_nonneg (hV _).1]
    exact (hV _).2
  · simp [omegaBox, hp]

/-- **`omegaBox_support_is_primes`.**  `LEAN_PROVED`.

The support of the literal weight family consists of primes only. -/
theorem omegaBox_support_is_primes {V : ℝ → ℝ} {Y t : ℝ} {p : ℕ}
    (h : omegaBox V Y t p ≠ 0) : p.Prime := by
  by_contra hp
  exact h (omegaBox_eq_zero_of_not_prime hp)

end PostBalanced7Pro
end Erdos287
