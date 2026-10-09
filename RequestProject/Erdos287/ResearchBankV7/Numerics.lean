import Mathlib
import RequestProject.Erdos287.ResearchBankV6.UpperGapCarry

/-!
# Erdős #287 — Research Bank V7: corrected numerical metadata for `J = L₄₄₇`

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The final modulus used by the exact-mass lane is `J = L₄₄₇ = lcm(1, …, 447)`.  Its size metadata
is **194 decimal digits and 644 bits** — the earlier "194-bit" wording was wrong and is corrected
here (nothing of the earlier layers is edited; this module states the corrected facts).

All statements are kernel-verified finite computations (`decide` on ordinary `Nat` arithmetic; no
`native_decide`):

* `J_digits` : `(Nat.digits 10 J).length = 194`;
* `J_bits` : `Nat.size J = 644`;
* `J_decimal_bounds`, `J_binary_bounds` : the underlying two-sided bounds;
* `J_is_not_194_bits` : the explicit correction — `J` is far larger than `2¹⁹⁴`.
-/

namespace Erdos287
namespace ResearchBankV7
namespace Numerics

/-- `lcmRange n = lcm(1, …, n)`, in the recursive form the kernel can evaluate. -/
def lcmRange : ℕ → ℕ
  | 0 => 1
  | (n + 1) => Nat.lcm (n + 1) (lcmRange n)

/-- The recursive form agrees with the V6 definition `lcmUpto` of `L_N = lcm(1, …, N)`. -/
theorem lcmRange_eq_lcmUpto : ∀ n : ℕ, lcmRange n = ResearchBankV6.UpperGap.lcmUpto n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hlcm : (insert (n + 1) (Finset.Icc 1 n)).lcm (id : ℕ → ℕ)
          = Nat.lcm (n + 1) ((Finset.Icc 1 n).lcm id) := by
        rw [Finset.lcm_insert]; rfl
      rw [lcmRange, ih, ResearchBankV6.UpperGap.lcmUpto, ResearchBankV6.UpperGap.lcmUpto,
        hIcc, hlcm]

/-- The final modulus of the exact-mass lane, `J = L₄₄₇`. -/
def J : ℕ := lcmRange 447

/-- `J` really is `lcm(1, …, 447)` in the sense of the banked `lcmUpto`. -/
theorem J_eq_lcmUpto : J = ResearchBankV6.UpperGap.lcmUpto 447 := lcmRange_eq_lcmUpto 447

set_option maxRecDepth 20000 in
/-- **Decimal size of `J`.** -/
theorem J_decimal_bounds : 10 ^ 193 ≤ J ∧ J < 10 ^ 194 := by decide

set_option maxRecDepth 20000 in
/-- **Binary size of `J`.** -/
theorem J_binary_bounds : 2 ^ 643 ≤ J ∧ J < 2 ^ 644 := by decide

/-- `J` is positive. -/
theorem J_pos : 0 < J :=
  lt_of_lt_of_le (by positivity : 0 < 10 ^ 193) J_decimal_bounds.1

/-- **`J = L₄₄₇` has 194 decimal digits.** -/
theorem J_digits : (Nat.digits 10 J).length = 194 := by
  have hlog : Nat.log 10 J = 193 :=
    Nat.log_eq_of_pow_le_of_lt_pow J_decimal_bounds.1 J_decimal_bounds.2
  rw [Nat.digits_len 10 J (by norm_num) (by have := J_pos; omega), hlog]

/-- **`J = L₄₄₇` has 644 bits.** -/
theorem J_bits : Nat.size J = 644 := by
  have h1 : Nat.size J ≤ 644 := Nat.size_le.2 J_binary_bounds.2
  have h2 : 643 < Nat.size J := Nat.lt_size.2 J_binary_bounds.1
  omega

/-- **The correction.**  `J` is *not* a 194-bit number: `2¹⁹⁴ < J`. -/
theorem J_is_not_194_bits : 2 ^ 194 < J := by
  have h : (2:ℕ) ^ 194 < 2 ^ 643 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  exact lt_of_lt_of_le h J_binary_bounds.1

end Numerics
end ResearchBankV7
end Erdos287
