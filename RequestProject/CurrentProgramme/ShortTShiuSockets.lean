import Mathlib
import RequestProject.Erdos287.ShiuDivisorAverage3221
import RequestProject.Erdos287.ShortShiftSieve3221
import RequestProject.CurrentProgramme.HardThetaDelta

/-!
# CurrentProgramme §11 — the short-`t` and Shiu analytic sockets

`BALANCED7-SHORTT-SIEVE45`  : `analyticOpen`.
`BALANCED7-SHIU45`          : `analyticOpen` (conservative).

Two uninhabited interfaces:

* `BalancedSevenShortTSieveInput` — the short-`t` rough sieve.  Its saving is stated in the
  **sieve variable**, `1 / log z` with `z = T^{1/20}`, `T = X^{5/7−θ}`, and *not* as a
  hard-coded `1 / log X`.  The physical `O(1/log X)` budget is then *derived* by the
  separate compiler of §10 using `δ = 1/21`.
* `BalancedSevenShiuInput` — the Shiu divisor average along the **literal affine sequence**
  `2 w' m + s`, with its range and modulus hypotheses recorded explicitly.

Neither socket is inhabited.  The historical V21 sieve and Shiu interfaces are untouched and
are reused only by reference.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace CurrentProgramme

/-! ## §11.1  The short-`t` sieve socket -/

/-- **`BalancedSevenShortTSieveInput`** — `EXTERNAL / ANALYTIC / UNINHABITED`.

The short-`t` rough-sieve saving, stated in the sieve variable `z`.  `R` is the short-`t`
remainder at scale `X` and physical parameter `θ`; the sieve dimension and level exponent are
the banked V21 values (`1` and `1/20`). -/
structure BalancedSevenShortTSieveInput (X theta C R : ℝ) : Prop where
  /-- The scale is nontrivial. -/
  scale : 3 ≤ X
  /-- The physical `θ`-range. -/
  theta_range : 1 / 3 ≤ theta ∧ theta ≤ 2 / 3
  /-- The sieve level exponent is the banked `1/20`. -/
  level_exponent : V21Sieve.sieveLevelExponent = 1 / 20
  /-- The sieve dimension is the banked `1`. -/
  dimension : V21Sieve.sieveDimension = 1
  /-- The constant is nonnegative. -/
  const_nonneg : 0 ≤ C
  /-- **The saving is in the sieve variable** `1 / log z`, not in `1 / log X`. -/
  sieve_saving : |R| ≤ C / Real.log (hardZ X theta)

/-- **`shortT_physical_budget`** — `CONDITIONAL` (the §10 compiler applied to the socket).

A `1/log z` saving becomes the physical `O(1/log X)` budget with the constant `420 · C`,
which is exactly the `δ = 1/21` repair. -/
theorem shortT_physical_budget {X theta C R : ℝ}
    (h : BalancedSevenShortTSieveInput X theta C R) :
    |R| ≤ 420 * C / Real.log X :=
  physical_range_budget_of_sieve_saving h.scale h.theta_range.2 h.const_nonneg h.sieve_saving

/-- **`shortTSieve_not_automatic`.**  `LEAN_PROVED`.  The socket is not inhabited. -/
theorem shortTSieve_not_automatic :
    ∃ X theta C R : ℝ, ¬ BalancedSevenShortTSieveInput X theta C R := by
  refine ⟨0, 0, 0, 0, ?_⟩
  intro h
  have := h.scale
  norm_num at this

/-- **`shortT_saving_is_not_logX`.**  `LEAN_PROVED`.

The distinction is real: `log z` and `log X` differ, so a socket written with `1/log X`
would be a *different* (and stronger) hypothesis.  Concretely `log z < log X` for `X ≥ 3`
and `θ ≥ 1/3`, in particular on the physical range. -/
theorem shortT_saving_is_not_logX {X theta : ℝ} (hX : 3 ≤ X) (h1 : 1 / 3 ≤ theta) :
    Real.log (hardZ X theta) < Real.log X := by
  have hXpos : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  rw [log_hardZ_eq hXpos theta]
  nlinarith

/-! ## §11.2  The Shiu socket -/

/-- The literal affine sequence of the packet: `m ↦ 2 w' m + s`. -/
def affineSeq (Wprime s m : ℕ) : ℕ := 2 * Wprime * m + s

theorem affineSeq_apply (Wprime s m : ℕ) : affineSeq Wprime s m = 2 * Wprime * m + s := rfl

/-- **`BalancedSevenShiuInput`** — `EXTERNAL / ANALYTIC / UNINHABITED`.

The Shiu-type divisor average along the literal affine sequence `2 w' m + s`, with the range
and modulus hypotheses spelled out. -/
structure BalancedSevenShiuInput
    (Wprime s : ℕ) (Mbox : Finset ℕ) (Mlen : ℕ) (Cshiu : ℝ) : Prop where
  /-- The modulus datum is odd (the `2` in `2w'` is the only even factor). -/
  modulus_odd : Odd Wprime
  /-- The shift is coprime to the modulus, so the sequence is non-degenerate. -/
  coprime_shift : Nat.Coprime (2 * Wprime) s
  /-- The box is a genuine range of length `Mlen`. -/
  range : Mbox.Nonempty ∧ Mbox.card = Mlen ∧ 3 ≤ Mlen
  /-- The literal affine sequence is the one estimated. -/
  literal_sequence : ∀ m ∈ Mbox, 0 < affineSeq Wprime s m
  /-- The Shiu divisor-average bound along the affine sequence. -/
  divisor_average :
    (∑ m ∈ Mbox, ((affineSeq Wprime s m).divisors.card : ℝ)) ≤
      Cshiu * (Mlen : ℝ) * Real.log (Mlen : ℝ)
  /-- The local factor collapse `2W/φ(2W) = W/φ(W)` for odd `W`, as banked in V21. -/
  local_factor : V21Shiu.shiuLocalFactor Wprime = (Wprime : ℝ) / (Nat.totient Wprime : ℝ)
  /-- The constant is positive. -/
  const_pos : 0 < Cshiu

/-- **`shiu_consumer`** — `CONDITIONAL`. -/
theorem shiu_consumer {Wprime s : ℕ} {Mbox : Finset ℕ} {Mlen : ℕ} {Cshiu : ℝ}
    (h : BalancedSevenShiuInput Wprime s Mbox Mlen Cshiu) :
    (∑ m ∈ Mbox, ((affineSeq Wprime s m).divisors.card : ℝ)) ≤
      Cshiu * (Mlen : ℝ) * Real.log (Mlen : ℝ) :=
  h.divisor_average

/-- **`shiu_not_automatic`.**  `LEAN_PROVED`.  The socket is not inhabited. -/
theorem shiu_not_automatic :
    ∃ (Wprime s : ℕ) (Mbox : Finset ℕ) (Mlen : ℕ) (Cshiu : ℝ),
      ¬ BalancedSevenShiuInput Wprime s Mbox Mlen Cshiu := by
  refine ⟨2, 1, ∅, 0, 1, ?_⟩
  intro h
  have h2 : Odd 2 := h.modulus_odd
  norm_num at h2

end CurrentProgramme
end Erdos287
