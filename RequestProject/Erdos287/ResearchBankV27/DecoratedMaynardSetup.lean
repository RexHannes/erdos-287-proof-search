import Mathlib

/-!
# Erdős #287 — Research Bank V27 §5.1–5.2: the decorated Maynard setup

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

## §5.1  Exact clean domain

`q = D q₀ ~ Q`, `B = q d`, `U ~ Q d`, `r_i = u_i v_i` with `u_i ~ R`, `v_i ~ S`, and the EXACT
assignment `R = R₃`, `S = R₂`.  The clean conditions are the fields of `CleanDomain`.

## §5.2  Range quantities

    Δ₁ = N² R² S / x,   Δ₂ = N² R³ S⁴ Q / x²,   Δ₃ = N R² S⁵ Q / x².

Required: `Δ₁ ≤ x^{−7η}`, `Δ₂ ≤ x^{−14η}`, `Δ₃ ≤ x^{−14η}` (`RangeConditions`).

**LEAN BANK.**
* `clean_substitution` — `n₁ ≡ n₂ (mod qd)` gives the exact substitution `n₁ − n₂ = f d q`;
* `delta1_rpow`, `delta2_rpow`, `delta3_rpow` — with `N = x^n`, `R = x^r`, `S = x^s`, `Q = x^κ`:
  `Δ₁ = x^{2n+2r+s−1}`, `Δ₂ = x^{2n+3r+4s+κ−2}`, `Δ₃ = x^{n+2r+5s+κ−2}`;
* `rangeConditions_iff_exponents` — for `x > 1` the three range conditions are EQUIVALENT to the
  three linear exponent inequalities (the arithmetic implication of the exponent ledger).

The analytic interpretation of the ranges remains conditional (it enters only through the
providers of `DISpectralProvider.lean`).
-/

namespace Erdos287
namespace ResearchBankV27
namespace DecoratedMaynardSetup

/-- The exact size assignment `R = R₃`, `S = R₂`. -/
structure SizeAssignment where
  R2 : ℝ
  R3 : ℝ
  R : ℝ
  S : ℝ
  hR : R = R3
  hS : S = R2

/-- The canonical assignment built from `(R₂, R₃)`. -/
def SizeAssignment.ofR (R2 R3 : ℝ) : SizeAssignment := ⟨R2, R3, R3, R2, rfl, rfl⟩

/-- **The clean domain** (all conditions recorded exactly). -/
structure CleanDomain (N C0 logx : ℝ) where
  D : ℕ
  q0 : ℕ
  d : ℕ
  u1 : ℕ
  u2 : ℕ
  v1 : ℕ
  v2 : ℕ
  n1 : ℤ
  n2 : ℤ
  r1 : ℕ := u1 * v1
  r2 : ℕ := u2 * v2
  hr1 : r1 = u1 * v1
  hr2 : r2 = u2 * v2
  cop_r : Nat.Coprime r1 r2
  cop_qd_r2 : Nat.Coprime (D * q0 * d) r2
  cop_n : IsCoprime n1 n2
  cop_n1 : IsCoprime n1 ((D * q0 * d * r1 : ℕ) : ℤ)
  cop_n2 : IsCoprime n2 ((D * q0 * d * r2 : ℕ) : ℤ)
  cong : n1 ≡ n2 [ZMOD ((D * q0 * d : ℕ) : ℤ)]
  sep : N / logx ^ C0 ≤ |((n1 - n2 : ℤ) : ℝ)|
  cop_D : Nat.Coprime D (q0 * d * r1 * r2)

/-- The modulus `q = D q₀`. -/
def CleanDomain.q {N C0 logx : ℝ} (c : CleanDomain N C0 logx) : ℕ := c.D * c.q0

/-- **Exact substitution** `n₁ − n₂ = f d q` (LEAN BANK). -/
theorem clean_substitution {N C0 logx : ℝ} (c : CleanDomain N C0 logx) :
    ∃ f : ℤ, c.n1 - c.n2 = f * c.d * c.q := by
  obtain ⟨f, hf⟩ := (Int.ModEq.dvd c.cong.symm)
  refine ⟨f, ?_⟩
  unfold CleanDomain.q
  push_cast at hf ⊢
  linarith [hf]

/-- `Δ₁ = N² R² S / x`. -/
noncomputable def Delta1 (N R S x : ℝ) : ℝ := N ^ 2 * R ^ 2 * S / x

/-- `Δ₂ = N² R³ S⁴ Q / x²`. -/
noncomputable def Delta2 (N R S Q x : ℝ) : ℝ := N ^ 2 * R ^ 3 * S ^ 4 * Q / x ^ 2

/-- `Δ₃ = N R² S⁵ Q / x²`. -/
noncomputable def Delta3 (N R S Q x : ℝ) : ℝ := N * R ^ 2 * S ^ 5 * Q / x ^ 2

/-- The required range conditions. -/
def RangeConditions (N R S Q x η : ℝ) : Prop :=
  Delta1 N R S x ≤ x ^ (-7 * η) ∧ Delta2 N R S Q x ≤ x ^ (-14 * η) ∧
    Delta3 N R S Q x ≤ x ^ (-14 * η)

section Exponents

variable {x : ℝ} (hx : 0 < x) (n r s κ : ℝ)
include hx

theorem rpow_pow_nat (a : ℝ) (k : ℕ) : (x ^ a) ^ k = x ^ (a * k) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]

theorem delta1_rpow : Delta1 (x ^ n) (x ^ r) (x ^ s) x = x ^ (2 * n + 2 * r + s - 1) := by
  unfold Delta1
  rw [rpow_pow_nat hx, rpow_pow_nat hx, ← Real.rpow_add hx, ← Real.rpow_add hx,
    div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hx]
  congr 1; push_cast; ring

theorem delta2_rpow :
    Delta2 (x ^ n) (x ^ r) (x ^ s) (x ^ κ) x = x ^ (2 * n + 3 * r + 4 * s + κ - 2) := by
  unfold Delta2
  rw [rpow_pow_nat hx, rpow_pow_nat hx, rpow_pow_nat hx, ← Real.rpow_add hx,
    ← Real.rpow_add hx, ← Real.rpow_add hx, div_eq_mul_inv, ← Real.rpow_natCast x 2,
    ← Real.rpow_neg hx.le, ← Real.rpow_add hx]
  congr 1; push_cast; ring

theorem delta3_rpow :
    Delta3 (x ^ n) (x ^ r) (x ^ s) (x ^ κ) x = x ^ (n + 2 * r + 5 * s + κ - 2) := by
  unfold Delta3
  rw [rpow_pow_nat hx, rpow_pow_nat hx, ← Real.rpow_add hx, ← Real.rpow_add hx,
    ← Real.rpow_add hx, div_eq_mul_inv, ← Real.rpow_natCast x 2, ← Real.rpow_neg hx.le,
    ← Real.rpow_add hx]
  congr 1; push_cast; ring

end Exponents

/-- **Range conditions ⟺ exponent inequalities** (LEAN BANK), for `x > 1`. -/
theorem rangeConditions_iff_exponents {x : ℝ} (hx : 1 < x) (n r s κ η : ℝ) :
    RangeConditions (x ^ n) (x ^ r) (x ^ s) (x ^ κ) x η ↔
      (2 * n + 2 * r + s - 1 ≤ -7 * η ∧ 2 * n + 3 * r + 4 * s + κ - 2 ≤ -14 * η ∧
        n + 2 * r + 5 * s + κ - 2 ≤ -14 * η) := by
  have hx0 : 0 < x := by linarith
  unfold RangeConditions
  rw [delta1_rpow hx0, delta2_rpow hx0, delta3_rpow hx0, Real.rpow_le_rpow_left_iff hx,
    Real.rpow_le_rpow_left_iff hx, Real.rpow_le_rpow_left_iff hx]

end DecoratedMaynardSetup
end ResearchBankV27
end Erdos287
