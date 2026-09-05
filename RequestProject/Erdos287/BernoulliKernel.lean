import Mathlib

/-!
# Erdős #287 — sawtooth, joint Bernoulli kernel, and the no-lattice identity

```
SAWTOOTH DEFINITION / INTEGER CONVENTION : KERNEL-PROVED   (psi, psi_intCast)
SAWTOOTH PERIODICITY                     : KERNEL-PROVED   (psi_add_intCast)
JOINT KERNEL DEFINITION                  : DEFINED         (jointKernel)
NO-LATTICE JOINT KERNEL IDENTITY         : KERNEL-PROVED   (jointKernel_noLattice)
```

## Convention

`psi x = Int.fract x − 1/2`.  At integers `Int.fract n = 0`, hence `psi n = −1/2`:
this is exactly the *strict-endpoint* convention required by the source bank, and it is
**not** changed anywhere below.

## API design constraint (firewall)

The physical consumer of the `k`-sum is `jointKernel`, i.e. the *joined* endpoint +
derivative object.  The decomposition `jointKernel = bernoulliEndpoint + bernoulliDerivative`
is recorded (`jointKernel_eq_endpoint_add_derivative`), but **no** theorem in this file — or
anywhere downstream — licenses bounding `|bernoulliEndpoint|` and `|bernoulliDerivative|`
separately and summing them over `k` as independent consumers.  Any such bound would
destroy the cancellation that the joined kernel encodes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open MeasureTheory intervalIntegral

namespace Erdos287
namespace BernoulliKernel

/-! ## §6.1  The strict-endpoint sawtooth -/

/-- The strict-endpoint sawtooth `ψ(x) = {x} − 1/2`; in particular `ψ(n) = −1/2`
at every integer `n`. -/
noncomputable def psi (x : ℝ) : ℝ := Int.fract x - 1 / 2

/-- The integer convention: `ψ(n) = −1/2`. -/
@[simp] theorem psi_intCast (n : ℤ) : psi (n : ℝ) = -(1 / 2) := by
  simp [psi]

@[simp] theorem psi_zero : psi 0 = -(1 / 2) := by simp [psi]

/-- **Periodicity.** `ψ(x + m) = ψ(x)` for integer `m`. -/
theorem psi_add_intCast (x : ℝ) (m : ℤ) : psi (x + m) = psi x := by
  simp [psi, Int.fract_add_intCast]

/-- On `[0, 1)` the sawtooth is the affine function `x ↦ x − 1/2`. -/
theorem psi_eq_of_mem_Ico {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) : psi x = x - 1 / 2 := by
  rw [psi, Int.fract_eq_self.2 ⟨h0, h1⟩]

/-! ## §6.2  The joined Bernoulli kernel -/

/-- The endpoint part of the Bernoulli kernel. -/
noncomputable def bernoulliEndpoint (W : ℝ → ℝ) (X z k : ℝ) : ℝ := psi (z / k) * W (z ^ 2 / X)

/-- The derivative part of the Bernoulli kernel. -/
noncomputable def bernoulliDerivative (W' : ℝ → ℝ) (X z k : ℝ) : ℝ :=
  ∫ y in (z ^ 2 / X)..(9 / 10), psi (X * y / (z * k)) * W' y

/-- **The joined Bernoulli kernel** — the *only* physical `k`-consumer:

    K(X,z,k) = ψ(z/k)·W(z²/X) + ∫_{z²/X}^{9/10} ψ(X y/(z k))·W'(y) dy. -/
noncomputable def jointKernel (W W' : ℝ → ℝ) (X z k : ℝ) : ℝ :=
  bernoulliEndpoint W X z k + bernoulliDerivative W' X z k

theorem jointKernel_eq_endpoint_add_derivative (W W' : ℝ → ℝ) (X z k : ℝ) :
    jointKernel W W' X z k = bernoulliEndpoint W X z k + bernoulliDerivative W' X z k := rfl

/-! ## §8  The no-lattice region -/

/-- The no-lattice predicate `k > (9/10)·X/z`. -/
def noLattice (X z k : ℝ) : Prop := (9 / 10) * X / z < k

/-- The lattice-bearing predicate is the exact negation of `noLattice`. -/
def latticeExists (X z k : ℝ) : Prop := ¬ noLattice X z k

theorem noLattice_or_latticeExists (X z k : ℝ) : noLattice X z k ∨ latticeExists X z k := by
  by_cases h : noLattice X z k
  · exact Or.inl h
  · exact Or.inr h

theorem not_noLattice_and_latticeExists (X z k : ℝ) :
    ¬ (noLattice X z k ∧ latticeExists X z k) := fun h => h.2 h.1

/-- If `W` vanishes outside the open support window `(7/10, 9/10)`, then `W(9/10) = 0`. -/
theorem endpoint_vanishes_of_support {W : ℝ → ℝ}
    (hsupp : ∀ y, W y ≠ 0 → y ∈ Set.Ioo (7 / 10 : ℝ) (9 / 10)) : W (9 / 10) = 0 := by
  by_contra h
  exact absurd (hsupp _ h).2 (lt_irrefl _)

/-- **`jointKernel_noLattice`.** `KERNEL-PROVED`.  In the no-lattice region the joined
Bernoulli kernel collapses to a pure `1/(zk)` tail:

    K(X,z,k) = −(X/(z k)) · ∫_{z²/X}^{9/10} W(y) dy.

Hypotheses: positivity of `X, z, k`; the support constraint `z²/X ≤ 9/10` and
`W(9/10) = 0` coming from `supp W ⊆ [7/10, 9/10]`; `W'` is the derivative of `W` and is
interval integrable.  No Euler-summation lemma is used: the proof is the exact
integration by parts, legitimate precisely because the sawtooth argument never crosses an
integer in the no-lattice region. -/
theorem jointKernel_noLattice {W W' : ℝ → ℝ} {X z k : ℝ}
    (hX : 0 < X) (hz : 0 < z) (hk : 0 < k)
    (ha : z ^ 2 / X ≤ 9 / 10)
    (hW9 : W (9 / 10) = 0)
    (hderiv : ∀ y : ℝ, HasDerivAt W (W' y) y)
    (hW'int : IntervalIntegrable W' volume (z ^ 2 / X) (9 / 10))
    (hnl : noLattice X z k) :
    jointKernel W W' X z k = -(X / (z * k)) * ∫ y in (z ^ 2 / X)..(9 / 10), W y := by
  set a : ℝ := z ^ 2 / X with hadef
  have hzk : 0 < z * k := mul_pos hz hk
  have ha0 : 0 < a := div_pos (by positivity) hX
  -- the no-lattice bound, cleared of denominators
  have hnl' : (9 / 10) * X < z * k := by
    rw [noLattice, div_lt_iff₀ hz] at hnl
    nlinarith [hnl]
  -- `z / k < 1`
  have hzk1 : z / k < 1 := by
    have h1 : z * z ≤ (9 / 10) * X := by
      have := (div_le_iff₀ hX).1 ha
      nlinarith [this]
    have : z * z < z * k := lt_of_le_of_lt h1 hnl'
    have := lt_of_mul_lt_mul_left this hz.le
    exact (div_lt_one hk).2 this
  -- the sawtooth argument stays in `[0,1)` on the whole integration range
  have hpsi : ∀ y ∈ Set.uIcc a (9 / 10 : ℝ),
      psi (X * y / (z * k)) * W' y = (X * y / (z * k) - 1 / 2) * W' y := by
    intro y hy
    rw [Set.uIcc_of_le ha] at hy
    obtain ⟨hy1, hy2⟩ := hy
    have hy0 : 0 < y := lt_of_lt_of_le ha0 hy1
    have h0 : 0 ≤ X * y / (z * k) := by positivity
    have h1 : X * y / (z * k) < 1 := by
      rw [div_lt_one hzk]
      nlinarith [hnl', hy2, hX.le]
    rw [psi_eq_of_mem_Ico h0 h1]
  -- integration by parts
  have hu : ∀ x ∈ Set.uIcc a (9 / 10 : ℝ),
      HasDerivAt (fun y : ℝ => X * y / (z * k) - 1 / 2) (X / (z * k)) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => X * y) X x := by
      simpa using (hasDerivAt_id x).const_mul X
    simpa using ((h1.div_const (z * k)).sub_const (1 / 2))
  have hv : ∀ x ∈ Set.uIcc a (9 / 10 : ℝ), HasDerivAt W (W' x) x := fun x _ => hderiv x
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := (9 / 10 : ℝ))
    hu hv (_root_.intervalIntegrable_const) hW'int
  -- assemble
  have hend : psi (z / k) = z / k - 1 / 2 :=
    psi_eq_of_mem_Ico (by positivity) hzk1
  have hXa : X * a / (z * k) = z / k := by
    rw [hadef]
    field_simp
  rw [jointKernel, bernoulliEndpoint, bernoulliDerivative, ← hadef,
    intervalIntegral.integral_congr hpsi, hIBP, hW9, hend, hXa,
    intervalIntegral.integral_const_mul]
  ring

end BernoulliKernel
end Erdos287
