import Mathlib
import RequestProject.CurrentProgramme.Erdos287Hybrid2AnalyticCompiler

/-!
# HYBRID-2 `η` compiler and the long-edge critical rectangle

Elementary real algebra only.  The analytic content enters exclusively through the explicit
hypotheses `hArch`, `hPacket`, `hLS` of `hybrid2_bound`; nothing here is claimed to be an
unconditional analytic theorem.

Contents.

* §9   `eta1`, `eta_sq_expand`, `hybrid2_bound` — the `η₁` normal form and the final estimate.
* §11  `rectangle_side1`, `rectangle_side2`, `rectangle_product`, `rectangle_intersection` —
  the division-safe long-edge rectangle algebra.

All positivity hypotheses are explicit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace Hybrid2

/-! ## §9  The `η₁` compiler -/

/-- The Hybrid-2 parameter

```
η₁ = C_arch · L_ℓ · sqrt( ((D+Q)(M₁+Q)) / (D M₁ Q) ).
``` -/
noncomputable def eta1 (Carch Lell D M1 Q : ℝ) : ℝ :=
  Carch * Lell * Real.sqrt (((D + Q) * (M1 + Q)) / (D * M1 * Q))

/-- **`eta_sq_expand`.**  `LEAN_PROVED` (unconditional).

```
η₁² = C_arch² L_ℓ² ( 1/D + 1/M₁ + 1/Q + Q/(D M₁) ).
```

No sign hypothesis on `C_arch`, `L_ℓ` is needed; only positivity of the three scales. -/
theorem eta_sq_expand {Carch Lell D M1 Q : ℝ} (hD : 0 < D) (hM1 : 0 < M1) (hQ : 0 < Q) :
    (eta1 Carch Lell D M1 Q) ^ 2
      = Carch ^ 2 * Lell ^ 2 * (1 / D + 1 / M1 + 1 / Q + Q / (D * M1)) := by
  unfold eta1
  have harg : (0 : ℝ) ≤ ((D + Q) * (M1 + Q)) / (D * M1 * Q) := by positivity
  have hsq : (Real.sqrt (((D + Q) * (M1 + Q)) / (D * M1 * Q))) ^ 2
      = ((D + Q) * (M1 + Q)) / (D * M1 * Q) := Real.sq_sqrt harg
  calc (Carch * Lell * Real.sqrt (((D + Q) * (M1 + Q)) / (D * M1 * Q))) ^ 2
      = Carch ^ 2 * Lell ^ 2 *
          (Real.sqrt (((D + Q) * (M1 + Q)) / (D * M1 * Q))) ^ 2 := by ring
    _ = Carch ^ 2 * Lell ^ 2 * (((D + Q) * (M1 + Q)) / (D * M1 * Q)) := by rw [hsq]
    _ = Carch ^ 2 * Lell ^ 2 * (1 / D + 1 / M1 + 1 / Q + Q / (D * M1)) := by
        congr 1
        field_simp
        ring

/-- `η₁ ≥ 0` when the two mass constants are nonnegative. -/
theorem eta1_nonneg {Carch Lell D M1 Q : ℝ} (hCarch : 0 ≤ Carch) (hLell : 0 ≤ Lell) :
    0 ≤ eta1 Carch Lell D M1 Q := by
  unfold eta1
  positivity

/-- **`hybrid2_bound`.**  `LEAN_PROVED` **conditionally** on `hArch`, `hPacket`, `hLS`.

This theorem is *not* unconditional.  Its three analytic inputs are, verbatim:

```
hArch    :  Btot² ≤ C_arch² · Etot
            (Archimedean reciprocal factor admits a separated packet expansion with total
             coefficient mass ≤ C_arch);

hPacket  :  Etot  ≤ L_ℓ² · Wsep
            (packet L² mass);

hLS      :  Wsep  ≤ 1/D + 1/M₁ + 1/Q + Q/(D M₁)
            (separated-frequency large sieve at spacing 1/Q, after the harmonic ℓ-sum).
```

Conclusion:  `Btot ≤ η₁ = C_arch L_ℓ sqrt( (D+Q)(M₁+Q) / (D M₁ Q) )`. -/
theorem hybrid2_bound {Carch Lell D M1 Q Btot Etot Wsep : ℝ}
    (hD : 0 < D) (hM1 : 0 < M1) (hQ : 0 < Q)
    (hCarch : 0 ≤ Carch) (hLell : 0 ≤ Lell)
    (hArch : Btot ^ 2 ≤ Carch ^ 2 * Etot)
    (hPacket : Etot ≤ Lell ^ 2 * Wsep)
    (hLS : Wsep ≤ 1 / D + 1 / M1 + 1 / Q + Q / (D * M1)) :
    Btot ≤ eta1 Carch Lell D M1 Q := by
  have h1 : Carch ^ 2 * Etot ≤ Carch ^ 2 * (Lell ^ 2 * Wsep) :=
    mul_le_mul_of_nonneg_left hPacket (by positivity)
  have h2 : Carch ^ 2 * (Lell ^ 2 * Wsep)
      ≤ Carch ^ 2 * Lell ^ 2 * (1 / D + 1 / M1 + 1 / Q + Q / (D * M1)) := by
    have := mul_le_mul_of_nonneg_left hLS (show (0:ℝ) ≤ Carch ^ 2 * Lell ^ 2 by positivity)
    calc Carch ^ 2 * (Lell ^ 2 * Wsep) = Carch ^ 2 * Lell ^ 2 * Wsep := by ring
      _ ≤ Carch ^ 2 * Lell ^ 2 * (1 / D + 1 / M1 + 1 / Q + Q / (D * M1)) := this
  have hsq : Btot ^ 2 ≤ (eta1 Carch Lell D M1 Q) ^ 2 := by
    rw [eta_sq_expand hD hM1 hQ]
    linarith
  have hEta : 0 ≤ eta1 Carch Lell D M1 Q := eta1_nonneg hCarch hLell
  nlinarith [hsq, hEta]

/-! ## §11  Long-edge rectangle algebra -/

/-- **`rectangle_side1`.**  `LEAN_PROVED` (unconditional, division-safe).

From the rectangle inequality `D·M₁ ≤ L² Q₁°` together with the source parametrisations
`M₁ = G/(e r₁)` and `Q₁° = B G / g₀`, all quantities positive,

```
r₁  ≥  g₀ D / (e B L²).
``` -/
theorem rectangle_side1 {D M1 G e r1 B L Q1circ g0 : ℝ}
    (hG : 0 < G) (he : 0 < e) (hr1 : 0 < r1) (hB : 0 < B) (hL : 0 < L) (hg0 : 0 < g0)
    (hM1 : M1 = G / (e * r1)) (hQ : Q1circ = B * G / g0)
    (hrect : D * M1 ≤ L ^ 2 * Q1circ) :
    g0 * D / (e * B * L ^ 2) ≤ r1 := by
  subst hM1
  subst hQ
  rw [div_le_iff₀ (by positivity)]
  have hkey : D * G * g0 ≤ L ^ 2 * (B * G) * (e * r1) := by
    have hpos : (0 : ℝ) < e * r1 * g0 := by positivity
    have h := mul_le_mul_of_nonneg_right hrect hpos.le
    have hL1 : D * (G / (e * r1)) * (e * r1 * g0) = D * G * g0 := by
      field_simp
    have hR1 : L ^ 2 * (B * G / g0) * (e * r1 * g0) = L ^ 2 * (B * G) * (e * r1) := by
      field_simp
    rw [hL1, hR1] at h
    exact h
  nlinarith [hkey, hG, hg0]

/-- **`rectangle_side2`.**  `LEAN_PROVED` (unconditional).  The symmetric side, with the primed
data `g₀'`, `M₂ = G/(e r₂)`, `Q₂° = B G / g₀'`. -/
theorem rectangle_side2 {D M2 G e r2 B L Q2circ g0' : ℝ}
    (hG : 0 < G) (he : 0 < e) (hr2 : 0 < r2) (hB : 0 < B) (hL : 0 < L) (hg0' : 0 < g0')
    (hM2 : M2 = G / (e * r2)) (hQ : Q2circ = B * G / g0')
    (hrect : D * M2 ≤ L ^ 2 * Q2circ) :
    g0' * D / (e * B * L ^ 2) ≤ r2 :=
  rectangle_side1 hG he hr2 hB hL hg0' hM2 hQ hrect

/-- **`rectangle_product`.**  `LEAN_PROVED` (unconditional).

Multiplying the two sides,

```
r₁ r₂  ≥  g₀ g₀' D² / (e² B² L₁² L₂²).
``` -/
theorem rectangle_product {D e B L1 L2 r1 r2 g0 g0' : ℝ}
    (hD : 0 ≤ D) (he : 0 < e) (hB : 0 < B) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hg0 : 0 < g0) (hg0' : 0 < g0')
    (h1 : g0 * D / (e * B * L1 ^ 2) ≤ r1) (h2 : g0' * D / (e * B * L2 ^ 2) ≤ r2) :
    g0 * g0' * D ^ 2 / (e ^ 2 * B ^ 2 * L1 ^ 2 * L2 ^ 2) ≤ r1 * r2 := by
  have hn1 : (0 : ℝ) ≤ g0 * D / (e * B * L1 ^ 2) := by positivity
  have hn2 : (0 : ℝ) ≤ g0' * D / (e * B * L2 ^ 2) := by positivity
  have hmul : (g0 * D / (e * B * L1 ^ 2)) * (g0' * D / (e * B * L2 ^ 2)) ≤ r1 * r2 :=
    mul_le_mul h1 h2 hn2 (le_trans hn1 h1)
  have hEq : (g0 * D / (e * B * L1 ^ 2)) * (g0' * D / (e * B * L2 ^ 2))
      = g0 * g0' * D ^ 2 / (e ^ 2 * B ^ 2 * L1 ^ 2 * L2 ^ 2) := by
    field_simp
  rwa [hEq] at hmul

/-- **`rectangle_intersection`.**  `LEAN_PROVED` (unconditional).

If in addition `r₁ r₂ < R_aff`, then

```
D  <  e B L₁ L₂ · sqrt( R_aff / (g₀ g₀') ).
``` -/
theorem rectangle_intersection {D e B L1 L2 r1 r2 g0 g0' Raff : ℝ}
    (hD : 0 < D) (he : 0 < e) (hB : 0 < B) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hg0 : 0 < g0) (hg0' : 0 < g0')
    (h1 : g0 * D / (e * B * L1 ^ 2) ≤ r1) (h2 : g0' * D / (e * B * L2 ^ 2) ≤ r2)
    (hRaff : r1 * r2 < Raff) :
    D < e * B * L1 * L2 * Real.sqrt (Raff / (g0 * g0')) := by
  have hprod := rectangle_product hD.le he hB hL1 hL2 hg0 hg0' h1 h2
  have hlt : g0 * g0' * D ^ 2 / (e ^ 2 * B ^ 2 * L1 ^ 2 * L2 ^ 2) < Raff := lt_of_le_of_lt hprod hRaff
  have hRpos : 0 < Raff := lt_of_le_of_lt (by positivity) hlt
  set K : ℝ := e * B * L1 * L2 * Real.sqrt (Raff / (g0 * g0')) with hK
  have hKnn : 0 ≤ K := by rw [hK]; positivity
  have hsqrt : (Real.sqrt (Raff / (g0 * g0'))) ^ 2 = Raff / (g0 * g0') :=
    Real.sq_sqrt (by positivity)
  have hK2 : K ^ 2 = e ^ 2 * B ^ 2 * L1 ^ 2 * L2 ^ 2 * (Raff / (g0 * g0')) := by
    rw [hK]
    calc (e * B * L1 * L2 * Real.sqrt (Raff / (g0 * g0'))) ^ 2
        = e ^ 2 * B ^ 2 * L1 ^ 2 * L2 ^ 2 *
            (Real.sqrt (Raff / (g0 * g0'))) ^ 2 := by ring
      _ = e ^ 2 * B ^ 2 * L1 ^ 2 * L2 ^ 2 * (Raff / (g0 * g0')) := by rw [hsqrt]
  have hDlt : D ^ 2 < K ^ 2 := by
    rw [div_lt_iff₀ (show (0:ℝ) < e ^ 2 * B ^ 2 * L1 ^ 2 * L2 ^ 2 by positivity)] at hlt
    rw [hK2, show e ^ 2 * B ^ 2 * L1 ^ 2 * L2 ^ 2 * (Raff / (g0 * g0'))
        = (e ^ 2 * B ^ 2 * L1 ^ 2 * L2 ^ 2 * Raff) / (g0 * g0') by ring,
      lt_div_iff₀ (show (0:ℝ) < g0 * g0' by positivity)]
    nlinarith [hlt]
  nlinarith [hDlt, hD, hKnn]

/-! ## §12  Top-shell comparability compiler (partial)

Only the part whose source hypotheses can be stated cleanly is formalised: the lower bound on
`e` produced by the two comparabilities `D ≍ G²/(A e)` and `A B ≍ X`, with the comparability
constants explicit.  The *exponent-level* consequence
`κ ≥ θ − 1/2 − ρ_aff/4 + (γ₀+γ₀')/4 − o(1)` is **NOT YET FORMALISED**: it requires a
source-exact dictionary between `κ, θ, ρ_aff, γ₀, γ₀'` and the scales, which is not present in
this repository, and no such dictionary is manufactured here. -/

/-- **`topShell_e_lower_bound`.**  `LEAN_PROVED` (unconditional, given the two comparability
hypotheses with explicit constants).

From `c₀ · G²/(A e) ≤ D` (lower half of `D ≍ G²/(Ae)`) and `A B ≤ c₂ X` (upper half of
`AB ≍ X`),

```
e  ≥  c₀ G² B / (c₂ X D).
``` -/
theorem topShell_e_lower_bound {D G A B X e c0 c2 : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hD : 0 < D) (he : 0 < e) (hX : 0 < X) (hc2 : 0 < c2)
    (hDlow : c0 * (G ^ 2 / (A * e)) ≤ D) (hABup : A * B ≤ c2 * X) :
    c0 * G ^ 2 * B / (c2 * X * D) ≤ e := by
  have hAe : (0 : ℝ) < A * e := by positivity
  have h1 : c0 * G ^ 2 ≤ D * (A * e) := by
    have := mul_le_mul_of_nonneg_right hDlow hAe.le
    calc c0 * G ^ 2 = c0 * (G ^ 2 / (A * e)) * (A * e) := by field_simp
      _ ≤ D * (A * e) := this
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hABup (mul_pos he hD).le, h1, hB.le, hD.le, he.le]

end Hybrid2
end Erdos287
