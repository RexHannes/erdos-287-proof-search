import Mathlib
import RequestProject.Erdos287.ShortShiftSieve3221

/-!
# V21, Phase 6 — the Shiu divisor-average external interface, with the local factor proved

`SHIU-LITERAL287 : EXTERNALLY AUDITED CANDIDATE / UNINHABITED INTERFACE`

Shiu's theorem is **not** proved here and **not** axiomatised.  What is proved here is only
the elementary local-factor arithmetic that the interface has to record correctly:

* `totient_two_mul_of_odd` : `φ(2W') = φ(W')` for odd `W'`;
* `shiuLocalFactor_eq`     : `2W'/φ(2W') = 2 · W'/φ(W')` for odd `W'`.

The analytic statement — for the physical linear polynomial `n = 2 W' m + s`,

`∑_{m ∼ M} τ(2 W' m + s) ≤ C_shiu · M · log X · (2W'/φ(2W'))` —

is the uninhabited interface `ShiuLinearDivisorAverage3221Input`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators

namespace Erdos287
namespace V21Shiu

/-! ## §1. The local factor -/

/-- **`totient_two_mul_of_odd`.**  `LEAN_PROVED`.

`φ(2n) = φ(n)` for odd `n`. -/
theorem totient_two_mul_of_odd {n : ℕ} (hn : Odd n) : Nat.totient (2 * n) = Nat.totient n := by
  have hcop : Nat.Coprime 2 n := Nat.coprime_two_left.mpr hn
  rw [Nat.totient_mul hcop, Nat.totient_two, one_mul]

/-- The Shiu local factor `2W'/φ(2W')` of the physical progression. -/
noncomputable def shiuLocalFactor (W : ℕ) : ℝ := (2 * W : ℝ) / (Nat.totient (2 * W) : ℝ)

/-- **`shiuLocalFactor_eq`.**  `LEAN_PROVED`.

For odd `W'` the local factor is `2 · W'/φ(W')`, the convention-correct form. -/
theorem shiuLocalFactor_eq {W : ℕ} (hW : Odd W) :
    shiuLocalFactor W = 2 * ((W : ℝ) / (Nat.totient W : ℝ)) := by
  rw [shiuLocalFactor, totient_two_mul_of_odd hW]
  ring

/-- The number of divisors of an integer, through its absolute value. -/
noncomputable def divisorCount (n : ℤ) : ℕ := n.natAbs.divisors.card

/-! ## §2. The external analytic interface — `UNINHABITED` -/

/-- **`ShiuLinearDivisorAverage3221Input`** — `EXTERNAL ANALYTIC / UNINHABITED`.

The audited Shiu-type divisor average for the physical linear polynomial
`n = 2 W' m + s`, with the exact local factor `2W'/φ(2W')` recorded.

**No inhabitant is constructed anywhere in this repository.** -/
structure ShiuLinearDivisorAverage3221Input (Wprime : ℕ) (s : ℤ) (Mbox : Finset ℕ)
    (M X Cshiu : ℝ) : Prop where
  /-- `W'` is odd — the hypothesis under which the local factor collapses. -/
  odd_Wprime : Odd Wprime
  /-- **The open analytic estimate.** -/
  divisor_average :
    (∑ m ∈ Mbox, (divisorCount (2 * (Wprime : ℤ) * (m : ℤ) + s) : ℝ))
      ≤ Cshiu * M * Real.log X * shiuLocalFactor Wprime

/-- The interface, restated with the *proved* collapsed local factor `2 W'/φ(W')`. -/
theorem shiuInput_localFactor_collapsed {Wprime : ℕ} {s : ℤ} {Mbox : Finset ℕ}
    {M X Cshiu : ℝ} (h : ShiuLinearDivisorAverage3221Input Wprime s Mbox M X Cshiu) :
    (∑ m ∈ Mbox, (divisorCount (2 * (Wprime : ℤ) * (m : ℤ) + s) : ℝ))
      ≤ Cshiu * M * Real.log X * (2 * ((Wprime : ℝ) / (Nat.totient Wprime : ℝ))) := by
  have := h.divisor_average
  rwa [shiuLocalFactor_eq h.odd_Wprime] at this

/-- **`shiuInput_not_automatic`.**  `LEAN_PROVED`.

The Shiu interface is a genuine restriction. -/
theorem shiuInput_not_automatic :
    ∃ (Wprime : ℕ) (s : ℤ) (Mbox : Finset ℕ) (M X Cshiu : ℝ),
      ¬ ShiuLinearDivisorAverage3221Input Wprime s Mbox M X Cshiu := by
  refine ⟨2, 0, ∅, 0, 0, 0, ?_⟩
  intro h
  have h1 : ¬ Odd 2 := by decide
  exact h1 h.odd_Wprime

end V21Shiu
end Erdos287
