import Mathlib
import RequestProject.CurrentProgramme.Erdos287CommonXCollisionFirewall

/-!
# A0/C0 source-lift arithmetic — Erdős #287 (append-only)

This module is **append-only**: it is added strictly after the COMMON-x / fractional-linear
bank and edits nothing that was banked earlier.  Every theorem in this file is an
*unconditional* identity or divisibility of integers.  No analytic statement, no dyadic
range, no divisor-moment estimate and no closure claim occurs anywhere below.

Contents.

* §1  **Source data.**  A structure `SourceRow` collecting exactly the integer data used by
  the source-lift identities (`s, s', Δ₀, Δ₀'` are signed; the remaining slots are natural
  numbers), together with the positivity hypotheses that will later supply `F ≠ 0`.
* §2  **Primitive source forms.**  The literal expansions
  `Γ₁ = 2 e r₁ r₂ z b`, `Γ₂ = 2 e' r₁' r₂' z' b'`,
  `A0row = 2 s Δ₀ e' r₁' r₂' z' b' u' ℓ₀'` and `C0 = 2 s' Δ₀' e r₁ r₂ z b`.
* §3  **Pre-completion row representative.**  If `b₁' = β₂ + Q₂ t'` with `Q₂ = d₁' v x`, then
  `x ∣ Q₂` and `A0pre ≡ A0row [ZMOD x]`.  This says only that the *completed* row has a
  canonical modular representative; it does **not** assert that `A0 + t x` is a physical
  source tuple for arbitrary `t`.

Nothing here implies that the C0 branch is closed, and nothing here is a statement about
Erdős #287 itself; see `RequestProject/Status/CurrentStatusErdos287C0SourceLift.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace SourceLift

/-! ## §1  Source data

The signed slots `s, s', Delta0, Delta0'` are integers: no sign normalisation is assumed
anywhere in this file.  All remaining slots are natural numbers and are cast into `ℤ` at the
point of use, so that no `Nat` subtraction ever occurs. -/

/-- Integer data of a single source row, sufficient for the A0/C0 source-lift identities.

The four signed slots are `s, s', Delta0, Delta0'`.  The positivity hypotheses are exactly the
ones needed later to show that the common row factor `F = b * u'` is nonzero; no positivity is
assumed for the signed slots. -/
structure SourceRow where
  /-- Signed prefactor of the `A0` row. -/
  s : ℤ
  /-- Signed prefactor of the `C0` row. -/
  s' : ℤ
  /-- Signed source difference of the `A0` row. -/
  Delta0 : ℤ
  /-- Signed source difference of the `C0` row. -/
  Delta0' : ℤ
  /-- Level slot of `Γ₁`. -/
  e : ℕ
  /-- Level slot of `Γ₂`. -/
  e' : ℕ
  /-- First reciprocal slot of `Γ₁`. -/
  r1 : ℕ
  /-- Second reciprocal slot of `Γ₁`. -/
  r2 : ℕ
  /-- First reciprocal slot of `Γ₂`. -/
  r1' : ℕ
  /-- Second reciprocal slot of `Γ₂`. -/
  r2' : ℕ
  /-- Modulus slot of `Γ₁`. -/
  z : ℕ
  /-- Modulus slot of `Γ₂`. -/
  z' : ℕ
  /-- Row slot `b` of `Γ₁`. -/
  b : ℕ
  /-- Row slot `b'` of `Γ₂`. -/
  b' : ℕ
  /-- First factor of `u = r m`. -/
  r : ℕ
  /-- Second factor of `u = r m`. -/
  m : ℕ
  /-- First factor of `u' = r' m'`. -/
  r' : ℕ
  /-- Second factor of `u' = r' m'`. -/
  m' : ℕ
  /-- Fibre slot `ℓ₀'`. -/
  ell0' : ℕ
  /-- Denominator slot of the raw projective pair. -/
  d2 : ℕ
  /-- Numerator slot of the raw projective pair. -/
  k : ℕ
  /-- `b` is positive. -/
  hb : 0 < b
  /-- `b'` is positive. -/
  hb' : 0 < b'
  /-- `r` is positive. -/
  hr : 0 < r
  /-- `m` is positive. -/
  hm : 0 < m
  /-- `r'` is positive. -/
  hr' : 0 < r'
  /-- `m'` is positive. -/
  hm' : 0 < m'
  /-- `ℓ₀'` is positive. -/
  hell0' : 0 < ell0'

namespace SourceRow

variable (R : SourceRow)

/-- `u = r m`, as an integer. -/
def u : ℤ := (R.r : ℤ) * (R.m : ℤ)

/-- `u' = r' m'`, as an integer. -/
def u' : ℤ := (R.r' : ℤ) * (R.m' : ℤ)

/-- `Γ₁ = 2 e r₁ r₂ z b`. -/
def Gamma1 : ℤ := 2 * (R.e : ℤ) * (R.r1 : ℤ) * (R.r2 : ℤ) * (R.z : ℤ) * (R.b : ℤ)

/-- `Γ₂ = 2 e' r₁' r₂' z' b'`. -/
def Gamma2 : ℤ := 2 * (R.e' : ℤ) * (R.r1' : ℤ) * (R.r2' : ℤ) * (R.z' : ℤ) * (R.b' : ℤ)

/-- `β₂ = u' ℓ₀'`. -/
def beta2 : ℤ := R.u' * (R.ell0' : ℤ)

/-- `A0row = s Δ₀ Γ₂ β₂`. -/
def A0row : ℤ := R.s * R.Delta0 * R.Gamma2 * R.beta2

/-- `C0 = s' Δ₀' Γ₁`. -/
def C0 : ℤ := R.s' * R.Delta0' * R.Gamma1

/-! ## §2  Primitive source forms

All four statements are unconditional ring identities in the integers. -/

/-- **`erdos287_gamma1_primitive`.**  `LEAN_PROVED`.  `Γ₁ = 2 e r₁ r₂ z b`. -/
theorem erdos287_gamma1_primitive :
    R.Gamma1 = 2 * (R.e : ℤ) * (R.r1 : ℤ) * (R.r2 : ℤ) * (R.z : ℤ) * (R.b : ℤ) := rfl

/-- **`erdos287_gamma2_primitive`.**  `LEAN_PROVED`.  `Γ₂ = 2 e' r₁' r₂' z' b'`. -/
theorem erdos287_gamma2_primitive :
    R.Gamma2 = 2 * (R.e' : ℤ) * (R.r1' : ℤ) * (R.r2' : ℤ) * (R.z' : ℤ) * (R.b' : ℤ) := rfl

/-- **`erdos287_A0row_primitive`.**  `LEAN_PROVED`.
`A0row = 2 s Δ₀ e' r₁' r₂' z' b' u' ℓ₀'`. -/
theorem erdos287_A0row_primitive :
    R.A0row
      = 2 * R.s * R.Delta0 * (R.e' : ℤ) * (R.r1' : ℤ) * (R.r2' : ℤ) * (R.z' : ℤ) * (R.b' : ℤ)
          * R.u' * (R.ell0' : ℤ) := by
  simp only [A0row, Gamma2, beta2]
  ring

/-- **`erdos287_C0_primitive`.**  `LEAN_PROVED`.  `C0 = 2 s' Δ₀' e r₁ r₂ z b`. -/
theorem erdos287_C0_primitive :
    R.C0 = 2 * R.s' * R.Delta0' * (R.e : ℤ) * (R.r1 : ℤ) * (R.r2 : ℤ) * (R.z : ℤ) * (R.b : ℤ) := by
  simp only [C0, Gamma1]
  ring

/-- **`erdos287_u_pos`.**  `LEAN_PROVED`.  `u > 0`. -/
theorem erdos287_u_pos : 0 < R.u := by
  have h1 : (0 : ℤ) < (R.r : ℤ) := by exact_mod_cast R.hr
  have h2 : (0 : ℤ) < (R.m : ℤ) := by exact_mod_cast R.hm
  exact mul_pos h1 h2

/-- **`erdos287_u'_pos`.**  `LEAN_PROVED`.  `u' > 0`. -/
theorem erdos287_u'_pos : 0 < R.u' := by
  have h1 : (0 : ℤ) < (R.r' : ℤ) := by exact_mod_cast R.hr'
  have h2 : (0 : ℤ) < (R.m' : ℤ) := by exact_mod_cast R.hm'
  exact mul_pos h1 h2

/-- **`erdos287_b_pos`.**  `LEAN_PROVED`.  `b > 0` as an integer. -/
theorem erdos287_b_pos : (0 : ℤ) < (R.b : ℤ) := by exact_mod_cast R.hb

end SourceRow

/-! ## §3  Pre-completion / row representative

The progression relation is `b₁' = β₂ + Q₂ t'` with `Q₂ = d₁' v x`.  We record the two facts
that make `A0row` a canonical representative of `A0pre` modulo `x`.  No claim is made that
`A0row + t x` is a physical source tuple for arbitrary `t`. -/

/-- **`erdos287_Q2_dvd`.**  `LEAN_PROVED`.  With `Q₂ = d₁' v x` we have `x ∣ Q₂`. -/
theorem erdos287_Q2_dvd (d1' v x : ℤ) : x ∣ d1' * v * x := ⟨d1' * v, by ring⟩

/-- **`erdos287_A0pre_sub_A0row`.**  `LEAN_PROVED`.  Literal factorisation of the difference
between the pre-completion row value and its canonical representative. -/
theorem erdos287_A0pre_sub_A0row
    (s Delta0 Gamma2 beta2 d1' v x t' b1' : ℤ)
    (hb1' : b1' = beta2 + (d1' * v * x) * t') :
    s * Delta0 * Gamma2 * b1' - s * Delta0 * Gamma2 * beta2
      = (s * Delta0 * Gamma2 * d1' * v * t') * x := by
  subst hb1'
  ring

/-- **`erdos287_A0pre_dvd_sub`.**  `LEAN_PROVED`.  `x ∣ A0pre − A0row`. -/
theorem erdos287_A0pre_dvd_sub
    (s Delta0 Gamma2 beta2 d1' v x t' b1' : ℤ)
    (hb1' : b1' = beta2 + (d1' * v * x) * t') :
    x ∣ s * Delta0 * Gamma2 * b1' - s * Delta0 * Gamma2 * beta2 :=
  ⟨s * Delta0 * Gamma2 * d1' * v * t',
    by rw [erdos287_A0pre_sub_A0row s Delta0 Gamma2 beta2 d1' v x t' b1' hb1']; ring⟩

/-- **`erdos287_A0pre_congr_A0row`.**  `LEAN_PROVED`.  The completed row has a canonical
modular representative: `A0pre ≡ A0row [ZMOD x]`. -/
theorem erdos287_A0pre_congr_A0row
    (s Delta0 Gamma2 beta2 d1' v x t' b1' : ℤ)
    (hb1' : b1' = beta2 + (d1' * v * x) * t') :
    s * Delta0 * Gamma2 * b1' ≡ s * Delta0 * Gamma2 * beta2 [ZMOD x] :=
  Int.ModEq.symm (Int.modEq_iff_dvd.mpr
    (erdos287_A0pre_dvd_sub s Delta0 Gamma2 beta2 d1' v x t' b1' hb1'))

/-- **`erdos287_A0pre_congr_A0row_row`.**  `LEAN_PROVED`.  The same statement for the data of a
`SourceRow`: with `b₁' = β₂ + d₁' v x t'`, the pre-completion value
`A0pre = s Δ₀ Γ₂ b₁'` is congruent to `A0row` modulo `x`. -/
theorem erdos287_A0pre_congr_A0row_row (R : SourceRow) (d1' v x t' b1' : ℤ)
    (hb1' : b1' = R.beta2 + (d1' * v * x) * t') :
    R.s * R.Delta0 * R.Gamma2 * b1' ≡ R.A0row [ZMOD x] :=
  erdos287_A0pre_congr_A0row R.s R.Delta0 R.Gamma2 R.beta2 d1' v x t' b1' hb1'

end SourceLift
end Erdos287
