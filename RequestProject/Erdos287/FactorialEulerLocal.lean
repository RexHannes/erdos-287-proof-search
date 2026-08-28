import Mathlib

/-!
# V16, Part 3 — the local (formal) Euler algebra of the factorial polarization

The divided-power local factor `F_z(p^e) = a^e / e!` assembles into the formal power series

`∑_{e ≥ 0} F_z(p^e) T^e = exp(a T)`,

which is `localSeries_eq_rescale_exp` below (a genuine identity of `PowerSeries` over a
characteristic-zero field, proved coefficientwise — **no analytic convergence is used or
claimed**).

Its formal logarithmic derivative is the constant `a`: `derivative_localSeries` says
`d/dT S = a · S`, i.e. the local `Λ`-coefficients of `F_z` are supported on `e = 1`.
With the `log p` normalisation this is recorded by `localLambda`, together with
`localLambda_one` (`Λ_{F_z}(p) = a_z(p) log p`) and `localLambda_of_two_le`
(`Λ_{F_z}(p^e) = 0` for `e ≥ 2`), whose generating series is the constant
`C (a · log p)` (`localLambdaSeries_eq_C`).

**Class-`C` disclaimer.**  This repository contains **no** definition of the analytic class
`C`, so nothing here is labelled a class-`C` statement.  What is banked is exactly the
finite/formal prime-power coefficient algebra.  Status:
`OMEGA7-FACTORIAL-LOCAL-EULER45 : PROVED_ALGEBRAIC (formal power series only)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open PowerSeries

namespace Erdos287
namespace FactorialEuler

variable {K : Type*} [Field K] [CharZero K]

/-! ## The local divided-power series -/

/-- `S_a(T) = ∑_{e ≥ 0} (a^e / e!) T^e`, the generating series of `F_z(p^e)`. -/
noncomputable def localSeries (a : K) : PowerSeries K :=
  PowerSeries.mk fun e => a ^ e / (e.factorial : K)

omit [CharZero K] in
@[simp] theorem coeff_localSeries (a : K) (e : ℕ) :
    PowerSeries.coeff e (localSeries a) = a ^ e / (e.factorial : K) := by
  rw [localSeries, PowerSeries.coeff_mk]

/-- **The formal Euler identity** `∑_{e ≥ 0} F_z(p^e) T^e = exp(a T)`. -/
theorem localSeries_eq_rescale_exp (a : K) :
    localSeries a = PowerSeries.rescale a (PowerSeries.exp K) := by
  ext n
  rw [coeff_localSeries, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  rw [show ((algebraMap ℚ K) (1 / (n.factorial : ℚ))) = 1 / (n.factorial : K) by
    rw [map_div₀]; norm_num]
  rw [div_eq_mul_inv, div_eq_mul_inv, one_mul]

/-- The formal logarithmic derivative of the local series is the constant `a`:
`d/dT S_a = a · S_a`. -/
theorem derivative_localSeries (a : K) :
    (d⁄dX K) (localSeries a) = PowerSeries.C a * localSeries a := by
  ext n
  have h1 : ((n.factorial : K)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h2 : ((n : K) + 1) ≠ 0 := by
    have h : ((n + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    simpa using h
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul, coeff_localSeries,
    coeff_localSeries, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-! ## Uniqueness of the local `Λ`-coefficients -/

omit [CharZero K] in
/-- The local series is nonzero (its constant coefficient is `1`). -/
theorem localSeries_ne_zero (a : K) : localSeries a ≠ 0 := by
  intro h
  have h0 : PowerSeries.coeff 0 (localSeries a) = 0 := by rw [h, map_zero]
  rw [coeff_localSeries] at h0
  simp at h0

/-- **The formal logarithmic derivative determines the `Λ`-series.**  If `d/dT S = Λ̃ · S`
then `Λ̃` is the constant `a`; no choice of `Λ`-coefficients other than the one below is
possible. -/
theorem localLambdaSeries_unique (a : K) (Lam : PowerSeries K)
    (h : (d⁄dX K) (localSeries a) = Lam * localSeries a) : Lam = PowerSeries.C a := by
  have h2 : Lam * localSeries a = PowerSeries.C a * localSeries a := by
    rw [← h, derivative_localSeries]
  exact mul_right_cancel₀ (localSeries_ne_zero a) h2

/-- **The local `Λ`-coefficients are forced**: any family `λ` with
`d/dT S = (∑_{e ≥ 1} λ_e T^{e-1}) · S` has `λ_1 = a` and `λ_e = 0` for `e ≥ 2`. -/
theorem lambda_coeffs_of_logDeriv (a : K) (lam : ℕ → K)
    (h : (d⁄dX K) (localSeries a)
      = (PowerSeries.mk fun e => lam (e + 1)) * localSeries a) :
    lam 1 = a ∧ ∀ e, 2 ≤ e → lam e = 0 := by
  have hC := localLambdaSeries_unique a _ h
  constructor
  · have := congrArg (fun S => PowerSeries.coeff 0 S) hC
    simpa using this
  · intro e he
    have := congrArg (fun S => PowerSeries.coeff (e - 1) S) hC
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_C] at this
    rw [show e - 1 + 1 = e by omega, if_neg (by omega)] at this
    exact this

/-! ## The local `Λ`-coefficients -/

/-- The local von Mangoldt datum of `F_z` at `p^e`: `a · log p` at `e = 1`, else `0`. -/
noncomputable def localLambda (a logp : K) (e : ℕ) : K :=
  if e = 1 then a * logp else 0

omit [CharZero K] in
@[simp] theorem localLambda_one (a logp : K) : localLambda a logp 1 = a * logp := by
  rw [localLambda, if_pos rfl]

omit [CharZero K] in
theorem localLambda_of_two_le (a logp : K) {e : ℕ} (he : 2 ≤ e) : localLambda a logp e = 0 := by
  rw [localLambda, if_neg (by omega)]

omit [CharZero K] in
@[simp] theorem localLambda_zero (a logp : K) : localLambda a logp 0 = 0 := by
  rw [localLambda, if_neg (by omega)]

omit [CharZero K] in
/-- The generating series `∑_{e ≥ 1} Λ_{F_z}(p^e) T^{e-1}` is the constant `a · log p`,
matching `derivative_localSeries` after the `log p` normalisation. -/
theorem localLambdaSeries_eq_C (a logp : K) :
    (PowerSeries.mk fun e => localLambda a logp (e + 1)) = PowerSeries.C (a * logp) := by
  ext n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_C]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · rw [localLambda, if_neg (by omega), if_neg (by omega)]

end FactorialEuler
end Erdos287
