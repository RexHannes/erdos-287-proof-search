import Mathlib
import RequestProject.CurrentProgramme.SharedG0PrimitiveURouter
import RequestProject.CurrentProgramme.LevelPairFixedDRigidity

/-!
# CRT reciprocal normal form — Erdős #287, ONE-LEVEL MÖBIUS Δ, §6

**Exact algebra only.**  Nothing analytic.

Fix a squarefree product modulus `n = r · s` with `s = n/r` and `gcd(r,s) = 1`.  After the
shared-`g₀` component has been isolated, the two remaining reciprocal phases live modulo `r`
and modulo `s` respectively.  This module banks:

* `exists_crtBeta` — the CRT representative `β_r` with `β_r ≡ b₁ (mod r)`, `β_r ≡ b₂ (mod s)`;
* `gcd_two_g0_beta_eq_one` — under the unit hypotheses, `gcd(2g₀β_r, n) = 1`;
* `crtNumerator` (`Ξ_r`) and `crtNumerator_rat` — the exact rational normal form
  `a₁/r + a₂/s = Ξ_r/n`;
* `reciprocal_phase_normalForm` — the corresponding exact identity for the repository's own
  additive phase: `e_r(a₁)·e_s(a₂) = e_n(Ξ_r)`;
* `reciprocal_normalForm_of_inverse` — with `a_i = D·(2g₀b_i)⁻¹` the combined mod-`n` phase of
  the reciprocal source, in the shape `e_n(Ξ_r)` with `Ξ_r = D(x₁s + x₂r)`;
* `global_inverse_restricts` — a global inverse of `2g₀β_r` modulo `n` restricts to inverses of
  `2g₀b₁` mod `r` and of `2g₀b₂` mod `s`, which is the precise sense in which the two coprime
  phases are the CRT components of one additive phase modulo `n`.

Status: `DET1-LEVELPAIR-N-RECIPROCAL-NORMALFORM45 : FORMALLY PROVED.`
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Erdos287.NormalForm3221

namespace Erdos287
namespace LevelPairReciprocal

/-! ## §6.1  The CRT representative `β_r` -/

/-- **Existence of `β_r`.**  `LEAN_PROVED`.

For coprime `r,s` and arbitrary `b₁,b₂` there is `β` with `β ≡ b₁ (mod r)` and
`β ≡ b₂ (mod s)`. -/
theorem exists_crtBeta {r s : ℤ} (hcop : IsCoprime r s) (b1 b2 : ℤ) :
    ∃ beta : ℤ, r ∣ beta - b1 ∧ s ∣ beta - b2 := by
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨b2 * (u * r) + b1 * (v * s), ⟨b2 * u - b1 * u, ?_⟩, ⟨b1 * v - b2 * v, ?_⟩⟩
  · have h : v * s = 1 - u * r := by linarith [huv]
    rw [h]; ring
  · have h : u * r = 1 - v * s := by linarith [huv]
    rw [h]; ring

/-- A congruence transports coprimality. -/
theorem gcd_eq_one_of_congr {a b m : ℤ} (h : m ∣ a - b) (hb : IsCoprime b m) : IsCoprime a m := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨u, v, huv⟩ := hb
  refine ⟨u, v - u * c, ?_⟩
  have ha : a = b + m * c := by linarith [hc]
  calc u * a + (v - u * c) * m = u * b + v * m := by rw [ha]; ring
    _ = 1 := huv

/-- **`gcd(2g₀β_r, n) = 1`.**  `LEAN_PROVED`.

Under the unit hypotheses `gcd(2g₀b₁, r) = 1`, `gcd(2g₀b₂, s) = 1` and the CRT congruences,
the single CRT reciprocal argument `2g₀β_r` is a unit modulo `n = rs`. -/
theorem gcd_two_g0_beta_eq_one {g0 r s beta b1 b2 : ℤ}
    (h1 : r ∣ beta - b1) (h2 : s ∣ beta - b2)
    (hu1 : IsCoprime (2 * g0 * b1) r) (hu2 : IsCoprime (2 * g0 * b2) s) :
    IsCoprime (2 * g0 * beta) (r * s) := by
  have e1 : r ∣ 2 * g0 * beta - 2 * g0 * b1 := by
    obtain ⟨c, hc⟩ := h1
    refine ⟨2 * g0 * c, ?_⟩
    rw [show 2 * g0 * beta - 2 * g0 * b1 = 2 * g0 * (beta - b1) by ring, hc]
    ring
  have e2 : s ∣ 2 * g0 * beta - 2 * g0 * b2 := by
    obtain ⟨c, hc⟩ := h2
    refine ⟨2 * g0 * c, ?_⟩
    rw [show 2 * g0 * beta - 2 * g0 * b2 = 2 * g0 * (beta - b2) by ring, hc]
    ring
  exact IsCoprime.mul_right (gcd_eq_one_of_congr e1 hu1) (gcd_eq_one_of_congr e2 hu2)

/-! ## §6.2  The CRT numerator `Ξ_r` -/

/-- The explicit CRT numerator `Ξ_r = a₁·(n/r) + a₂·r`. -/
def crtNumerator (a1 a2 r s : ℤ) : ℤ := a1 * s + a2 * r

/-- `Ξ_r ≡ a₁ s (mod r)` and `Ξ_r ≡ a₂ r (mod s)`. -/
theorem crtNumerator_congr (a1 a2 r s : ℤ) :
    r ∣ crtNumerator a1 a2 r s - a1 * s ∧ s ∣ crtNumerator a1 a2 r s - a2 * r := by
  refine ⟨⟨a2, by unfold crtNumerator; ring⟩, ⟨a1, by unfold crtNumerator; ring⟩⟩

/-- **Exact rational normal form.**  `LEAN_PROVED`.  `a₁/r + a₂/s = Ξ_r/(rs)`. -/
theorem crtNumerator_rat {r s : ℚ} (hr : r ≠ 0) (hs : s ≠ 0) (a1 a2 : ℚ) :
    a1 / r + a2 / s = (a1 * s + a2 * r) / (r * s) := by
  field_simp

/-- **`DET1-LEVELPAIR-N-RECIPROCAL-NORMALFORM45`, phase form.**  `LEAN_PROVED`.

The two coprime phases modulo `r` and modulo `s = n/r` combine into a single additive phase
modulo `n = rs`, with the explicit CRT numerator `Ξ_r`:

```
e_r(a₁) · e_s(a₂) = e_n(Ξ_r),   Ξ_r = a₁ s + a₂ r.
``` -/
theorem reciprocal_phase_normalForm {r s : ℤ} (hr : (r : ℝ) ≠ 0) (hs : (s : ℝ) ≠ 0)
    (a1 a2 : ℤ) :
    phase ((a1 : ℝ) / r) * phase ((a2 : ℝ) / s)
      = phase (((crtNumerator a1 a2 r s : ℤ) : ℝ) / ((r : ℝ) * s)) := by
  rw [← Erdos287.SharedG0Router.phase_add]
  congr 1
  unfold crtNumerator
  push_cast
  field_simp

/-- **Reciprocal source normal form.**  `LEAN_PROVED`.

Specialising to the reciprocal arguments `a_i = D·x_i` (where `x₁` is an inverse of `2g₀b₁`
mod `r` and `x₂` one of `2g₀b₂` mod `s`), the level-pair reciprocal phase is the single
mod-`n` phase with numerator `Ξ_r = D(x₁ s + x₂ r)`. -/
theorem reciprocal_normalForm_of_inverse {r s : ℤ} (hr : (r : ℝ) ≠ 0) (hs : (s : ℝ) ≠ 0)
    (D x1 x2 : ℤ) :
    phase (((D * x1 : ℤ) : ℝ) / r) * phase (((D * x2 : ℤ) : ℝ) / s)
      = phase (((D * (x1 * s + x2 * r) : ℤ) : ℝ) / ((r : ℝ) * s)) := by
  rw [reciprocal_phase_normalForm hr hs (D * x1) (D * x2)]
  congr 2
  unfold crtNumerator
  push_cast
  ring

/-- **Global inverse restricts.**  `LEAN_PROVED`.

If `x` inverts `2g₀β_r` modulo `n = rs`, then — by the CRT congruences defining `β_r` — the
same `x` inverts `2g₀b₁` modulo `r` and `2g₀b₂` modulo `s`.  This is the exact sense in which
the two coprime reciprocal phases are the CRT components of one phase modulo `n`. -/
theorem global_inverse_restricts {g0 r s beta b1 b2 x : ℤ}
    (h1 : r ∣ beta - b1) (h2 : s ∣ beta - b2)
    (hx : r * s ∣ x * (2 * g0 * beta) - 1) :
    r ∣ x * (2 * g0 * b1) - 1 ∧ s ∣ x * (2 * g0 * b2) - 1 := by
  have hxr : r ∣ x * (2 * g0 * beta) - 1 := dvd_trans ⟨s, rfl⟩ hx
  have hxs : s ∣ x * (2 * g0 * beta) - 1 := dvd_trans ⟨r, by ring⟩ hx
  constructor
  · obtain ⟨c, hc⟩ := h1
    obtain ⟨e, he⟩ := hxr
    refine ⟨e - x * 2 * g0 * c, ?_⟩
    have hb : b1 = beta - r * c := by linarith [hc]
    rw [hb]
    have : x * (2 * g0 * (beta - r * c)) - 1 = (x * (2 * g0 * beta) - 1) - r * (x * 2 * g0 * c) := by
      ring
    rw [this, he]
    ring
  · obtain ⟨c, hc⟩ := h2
    obtain ⟨e, he⟩ := hxs
    refine ⟨e - x * 2 * g0 * c, ?_⟩
    have hb : b2 = beta - s * c := by linarith [hc]
    rw [hb]
    have : x * (2 * g0 * (beta - s * c)) - 1 = (x * (2 * g0 * beta) - 1) - s * (x * 2 * g0 * c) := by
      ring
    rw [this, he]
    ring

end LevelPairReciprocal
end Erdos287
