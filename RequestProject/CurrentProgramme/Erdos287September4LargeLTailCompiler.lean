import Mathlib

/-!
# Erdős #287 — September-4 signed-floor bank, §11: the large-`L` tail envelope

```
ENVELOPE MONOTONICITY  9360 L(1+L) e^{-L/2} decreasing : KERNEL-PROVED
ENDPOINT DECIMAL  envelope(62.5) < 10⁻⁶                : KERNEL-PROVED
TAIL COMPILER  62.5 ≤ L ≤ 3727 ⇒ envelope L < 10⁻⁶     : KERNEL-PROVED (implication)
MERTENS ENVELOPE                                        : UNINHABITED INTERFACE ONLY
```

This module is **append-only**.  It proves *only* properties of the explicit real function

    envelope L = 9360 · L · (1 + L) · exp(−L/2),

which is the absolute envelope recorded by the research bank for the floor ratio.  Whether
the *physical* floor ratio is dominated by `envelope` is an **input**, not a theorem of this
file: the tail compiler below is an implication that consumes that domination hypothesis as
an explicit binder.

The endpoint decimal is genuinely kernel-proved, not external: it is reduced to the exact
rational inequality `37147500 · 10⁶ < (7889/6144)^125` together with the Taylor lower bound
`7889/6144 ≤ exp(1/4)` (five terms) and `exp(125/4) = exp(1/4)^125`.

## Mertens firewall

No explicit Mertens estimate is asserted anywhere.  `MertensEnvelopeInput` is an
**uninhabited** interface recording the exact inequality a later run would have to supply or
certify; this development builds no inhabitant, and the published explicit-Mertens
literature is provenance only until formalised.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set

namespace Erdos287
namespace September4LargeLTail

/-! ## §11.1  The envelope and its derivative -/

/-- The absolute envelope of the research bank: `9360 · L · (1 + L) · exp(−L/2)`. -/
noncomputable def envelope (L : ℝ) : ℝ := 9360 * L * (1 + L) * Real.exp (-L / 2)

/-- The exact derivative of the envelope. -/
theorem envelope_hasDerivAt (x : ℝ) :
    HasDerivAt envelope (9360 * (1 + 2 * x) * Real.exp (-x / 2)
      + 9360 * x * (1 + x) * (-(1 / 2) * Real.exp (-x / 2))) x := by
  have h1 : HasDerivAt (fun y : ℝ => 9360 * y * (1 + y)) (9360 * (1 + 2 * x)) x := by
    have ha : HasDerivAt (fun y : ℝ => 9360 * y) 9360 x := by
      simpa using (hasDerivAt_id x).const_mul (9360 : ℝ)
    have hb : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
      simpa using (hasDerivAt_id x).const_add (1 : ℝ)
    have hab := ha.mul hb
    convert hab using 1
    ring
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y / 2)) (-(1 / 2) * Real.exp (-x / 2)) x := by
    have hc : HasDerivAt (fun y : ℝ => -y / 2) (-(1 / 2) : ℝ) x := by
      have hd := ((hasDerivAt_id x).neg).div_const 2
      convert hd using 1
      norm_num
    have he := hc.exp
    convert he using 1
    ring
  exact h1.mul h2

theorem envelope_deriv_neg {x : ℝ} (hx : 4 < x) : deriv envelope x < 0 := by
  rw [(envelope_hasDerivAt x).deriv]
  have hexp : 0 < Real.exp (-x / 2) := Real.exp_pos _
  have hfac : 9360 * (1 + 2 * x) * Real.exp (-x / 2)
        + 9360 * x * (1 + x) * (-(1 / 2) * Real.exp (-x / 2))
      = (9360 * (1 + 2 * x) - 4680 * x * (1 + x)) * Real.exp (-x / 2) := by ring
  rw [hfac]
  have hneg : 9360 * (1 + 2 * x) - 4680 * x * (1 + x) < 0 := by nlinarith
  exact mul_neg_of_neg_of_pos hneg hexp

/-- **`envelope_strictAntiOn`.**  `KERNEL-PROVED`.  The envelope is strictly decreasing on
`[4, ∞)`, hence on the whole required range `L ≥ 62.5`. -/
theorem envelope_strictAntiOn : StrictAntiOn envelope (Ici (4 : ℝ)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici _) ?_ ?_
  · exact Continuous.continuousOn (by unfold envelope; fun_prop)
  · intro x hx
    rw [interior_Ici] at hx
    exact envelope_deriv_neg hx

/-! ## §11.2  The endpoint decimal, kernel-proved -/

/-- Five Taylor terms: `7889/6144 ≤ exp(1/4)`. -/
theorem exp_quarter_lower : (7889 / 6144 : ℝ) ≤ Real.exp (1 / 4) := by
  have h := Real.sum_le_exp_of_nonneg (x := (1 / 4 : ℝ)) (by norm_num) 5
  refine le_trans (le_of_eq ?_) h
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- The exact endpoint inequality `37147500 · 10⁶ < exp(125/4)`. -/
theorem exp_endpoint_lower : (37147500 * 10 ^ 6 : ℝ) < Real.exp (125 / 4) := by
  have h1 : Real.exp (125 / 4) = (Real.exp (1 / 4)) ^ 125 := by
    rw [show ((125 : ℝ) / 4) = (125 : ℕ) * (1 / 4) by norm_num, Real.exp_nat_mul]
  rw [h1]
  refine lt_of_lt_of_le ?_ (pow_le_pow_left₀ (by norm_num) exp_quarter_lower 125)
  norm_num

/-- **`envelope_endpoint`.**  `KERNEL-PROVED`.  The sharp endpoint evaluation

    envelope(62.5) = 9360 · 62.5 · 63.5 · exp(−31.25) < 10⁻⁶. -/
theorem envelope_endpoint : envelope (125 / 2) < 1 / 10 ^ 6 := by
  have hpos : (0 : ℝ) < Real.exp (125 / 4) := Real.exp_pos _
  have hval : envelope (125 / 2) = 37147500 / Real.exp (125 / 4) := by
    unfold envelope
    rw [show (-(125 / 2 : ℝ) / 2) = -(125 / 4) by norm_num, Real.exp_neg]
    field_simp
    ring
  rw [hval, div_lt_div_iff₀ hpos (by norm_num : (0:ℝ) < 10 ^ 6)]
  have h := exp_endpoint_lower
  nlinarith [h]

/-! ## §11.3  The tail compiler -/

/-- The envelope is below `10⁻⁶` for every `L ≥ 62.5`. -/
theorem envelope_lt_of_ge {L : ℝ} (hL : 125 / 2 ≤ L) : envelope L < 1 / 10 ^ 6 := by
  rcases eq_or_lt_of_le hL with h | h
  · rw [← h]; exact envelope_endpoint
  · refine lt_trans ?_ envelope_endpoint
    exact envelope_strictAntiOn (by norm_num) (by norm_num; linarith) h

/-- **`largeL_tail_envelope_bound`.**  `KERNEL-PROVED`.  On the tail slab
`62.5 ≤ L ≤ 3727` the envelope stays below `10⁻⁶`. -/
theorem largeL_tail_envelope_bound {L : ℝ} (hL : L ∈ Icc (125 / 2 : ℝ) 3727) :
    envelope L < 1 / 10 ^ 6 :=
  envelope_lt_of_ge hL.1

/-- **`largeL_tail_compiler`.**  `KERNEL-PROVED` *implication*.  If a supplied floor ratio
is dominated by the envelope on the tail slab, it is below `10⁻⁶` there.  The domination
hypothesis is an explicit binder: nothing in this file asserts it. -/
theorem largeL_tail_compiler (ratio : ℝ → ℝ)
    (hdom : ∀ L ∈ Icc (125 / 2 : ℝ) 3727, ratio L ≤ envelope L)
    {L : ℝ} (hL : L ∈ Icc (125 / 2 : ℝ) 3727) : ratio L < 1 / 10 ^ 6 :=
  lt_of_le_of_lt (hdom L hL) (largeL_tail_envelope_bound hL)

/-! ## §11.4  The Mertens interface (uninhabited) -/

/-- **Uninhabited interface.**  The exact explicit-Mertens inequality that a later run would
consume, recorded as a hypothesis socket.  This development builds **no** inhabitant and
proves no numerical Mertens bound; in particular `|M(x)| ≤ 0.571 √x` is *not* asserted. -/
structure MertensEnvelopeInput where
  /-- The Mertens summatory function, supplied from outside. -/
  M : ℕ → ℝ
  /-- The explicit constant of the envelope. -/
  c : ℝ
  /-- Positivity of the constant. -/
  c_pos : 0 < c
  /-- The upper endpoint of the range on which the envelope is supplied. -/
  xmax : ℕ
  /-- The supplied inequality, on the supplied range only. -/
  bound : ∀ x : ℕ, x ≤ xmax → |M x| ≤ c * Real.sqrt x

end September4LargeLTail
end Erdos287
