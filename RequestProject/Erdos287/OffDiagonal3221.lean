import Mathlib
import RequestProject.Erdos287.Exponent3221Ledger

/-!
# V17, Phase C — the exact off-diagonal integer parameter `t`

`3221-OFFDIAGONAL-T-RANGE45 : PROVED_FINITE + CAPACITY_ONLY`.

The off-diagonal relation of the 3221 arrangement is

`w₁ - w₂ = q t ≠ 0`,  `wᵢ = eᵢ nᵢ ℓᵢ`.

Everything here is done over `ℤ` (never truncated natural subtraction):

* `offdiag_existsUnique_t` — from `w₁ ≡ w₂ (mod q)` and `q ≠ 0` there is a **unique**
  integer `t` with `w₁ - w₂ = q t`;
* `offdiag_t_ne_zero` — it is nonzero exactly when `w₁ ≠ w₂`;
* `offdiag_abs_t_le` — the finite range `|t| · Q_min ≤ 2 W_max`, and its rational form
  `|t| ≤ 2 W_max / Q_min`.

The dyadic exponent layer is *only* the rational statement `Texp = 5/7 - 3/5 = 4/35`
already banked in `Exponent3221Ledger`; **no asymptotic dyadic theorem is claimed**, since
the repository contains no interval/dyadic-decomposition machinery to support one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace OffDiag3221

/-! ## §10. Exact `t`-parametrisation -/

/-- **Existence and uniqueness of the off-diagonal parameter `t`.**  If `w₁ ≡ w₂ (mod q)`
and `q ≠ 0`, there is exactly one integer `t` with `w₁ - w₂ = q t`. -/
theorem offdiag_existsUnique_t {w₁ w₂ q : ℤ} (hq : q ≠ 0) (hcong : w₁ ≡ w₂ [ZMOD q]) :
    ∃! t : ℤ, w₁ - w₂ = q * t := by
  obtain ⟨t, ht⟩ : q ∣ w₁ - w₂ := (Int.ModEq.dvd hcong.symm)
  refine ⟨t, ht, ?_⟩
  intro s hs
  have : q * s = q * t := by rw [← hs, ht]
  exact mul_right_injective₀ hq this

/-- The parameter is nonzero precisely on the genuine off-diagonal. -/
theorem offdiag_t_ne_zero {w₁ w₂ q t : ℤ} (hne : w₁ ≠ w₂) (ht : w₁ - w₂ = q * t) :
    t ≠ 0 := by
  rintro rfl
  simp only [mul_zero, sub_eq_zero] at ht
  exact hne ht

/-- Conversely a nonzero parameter forces a genuine off-diagonal term. -/
theorem offdiag_ne_of_t_ne_zero {w₁ w₂ q t : ℤ} (hq : q ≠ 0) (htne : t ≠ 0)
    (ht : w₁ - w₂ = q * t) : w₁ ≠ w₂ := by
  intro h
  rw [h, sub_self] at ht
  exact htne (by simpa [hq] using (mul_eq_zero.mp ht.symm).resolve_left hq)

/-! ## §11. The `t`-range, finite layer -/

/-- **Finite `t`-range.**  If both `w`'s lie in a box of radius `W_max` and every modulus
has `|q| ≥ Q_min > 0`, then `|t| · Q_min ≤ 2 W_max`. -/
theorem offdiag_abs_t_le {w₁ w₂ q t Wmax Qmin : ℤ} (hW₁ : |w₁| ≤ Wmax) (hW₂ : |w₂| ≤ Wmax)
    (hQ : Qmin ≤ |q|) (ht : w₁ - w₂ = q * t) :
    |t| * Qmin ≤ 2 * Wmax := by
  have h1 : |t| * Qmin ≤ |t| * |q| := by
    exact mul_le_mul_of_nonneg_left hQ (abs_nonneg t)
  have h2 : |t| * |q| = |w₁ - w₂| := by
    rw [ht, abs_mul]; ring
  have h3 : |w₁ - w₂| ≤ |w₁| + |w₂| := abs_sub _ _
  linarith

/-- The rational form `|t| ≤ 2 W_max / Q_min`. -/
theorem offdiag_abs_t_le_div {w₁ w₂ q t : ℤ} {Wmax Qmin : ℤ} (hQpos : 0 < Qmin)
    (hW₁ : |w₁| ≤ Wmax) (hW₂ : |w₂| ≤ Wmax) (hQ : Qmin ≤ |q|) (ht : w₁ - w₂ = q * t) :
    (|t| : ℚ) ≤ 2 * (Wmax : ℚ) / (Qmin : ℚ) := by
  have h := offdiag_abs_t_le hW₁ hW₂ hQ ht
  have hQ' : (0 : ℚ) < (Qmin : ℚ) := by exact_mod_cast hQpos
  rw [le_div_iff₀ hQ']
  exact_mod_cast h

/-! ## Dyadic exponent layer — capacity only

Only the rational identity is banked; see `Erdos287.Ledger3221.Texp_eq`. -/

/-- `Texp = W - Q = 4/35`, restated here for the off-diagonal file. -/
theorem texp_value : Erdos287.Ledger3221.Texp = 4 / 35 := Erdos287.Ledger3221.Texp_eq

end OffDiag3221
end Erdos287
