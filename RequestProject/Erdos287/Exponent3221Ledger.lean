import Mathlib

/-!
# V17, Phase A (§5–§6) — the exact 3221 exponent ledger

`PASCADI41-3221-RANGE-LEDGER : PROVED_ALGEBRAIC / CAPACITY_ONLY`.

This file contains **exact rational arithmetic only**.  It records the exponents of the
3221 parameter choice

* `E = X^{1/7}`, `M = N = L = X^{2/7}`, `Q = X^{3/5}`,

the derived Poisson dual length `H = Q/M = X^{11/35}`, the off-diagonal parameter range
`|t| ≪ X^{4/35}` and the capacity margins quoted by the source run, and it checks the
standard three-block range defect at the aggregate triple point.

**Honesty statement.**  Nothing here is an analytic theorem.  No `X^{o(1)}` is defined, no
asymptotic is claimed, Pascadi's Theorem 4.1 (or 3.9) is *not* formalised, and none of these
rational identities implies any bound on any arithmetic sum.  They are a *capacity ledger*:
they certify that the arithmetic of the proposed parameter choice is internally consistent,
and nothing more.  Erdős #287 remains OPEN.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace Ledger3221

/-! ## §5. The exponents -/

/-- Exponent of the single-prime box `E = X^{1/7}`. -/
def Eexp : ℚ := 1 / 7

/-- Exponent of the box `M = X^{2/7}` (the box dualised by Poisson). -/
def Mexp : ℚ := 2 / 7

/-- Exponent of the box `N = X^{2/7}`. -/
def Nexp : ℚ := 2 / 7

/-- Exponent of the box `L = X^{2/7}`. -/
def Lexp : ℚ := 2 / 7

/-- Exponent of the modulus range `Q = X^{3/5}`. -/
def Qexp : ℚ := 3 / 5

/-- Exponent of the triple-product variable `W = E N L`. -/
def Wexp : ℚ := Eexp + Nexp + Lexp

/-- Exponent of the Poisson dual length `H = Q / M`. -/
def Hexp : ℚ := Qexp - Mexp

/-- Exponent of the off-diagonal parameter `t`. -/
def Texp : ℚ := Wexp - Qexp

/-- Exponent of the aggregated first block `M' = E M`. -/
def Mprimeexp : ℚ := Eexp + Mexp

/-- **`E M N L = X`** at exponent level. -/
theorem exponents_sum_one : Eexp + Mexp + Nexp + Lexp = 1 := by
  norm_num [Wexp, Texp, Hexp, Mprimeexp, Eexp, Mexp, Nexp, Lexp, Qexp]

/-- `W = X^{5/7}`. -/
theorem Wexp_eq : Wexp = 5 / 7 := by
  norm_num [Wexp, Texp, Hexp, Mprimeexp, Eexp, Mexp, Nexp, Lexp, Qexp]

/-- **`W / Q = X^{4/35}`.** -/
theorem Wexp_sub_Qexp : Wexp - Qexp = 4 / 35 := by
  norm_num [Wexp, Texp, Hexp, Mprimeexp, Eexp, Mexp, Nexp, Lexp, Qexp]

/-- `H = X^{11/35}`. -/
theorem Hexp_eq : Hexp = 11 / 35 := by
  norm_num [Wexp, Texp, Hexp, Mprimeexp, Eexp, Mexp, Nexp, Lexp, Qexp]

/-- `E H = X^{16/35}`. -/
theorem Eexp_add_Hexp : Eexp + Hexp = 16 / 35 := by
  norm_num [Wexp, Texp, Hexp, Mprimeexp, Eexp, Mexp, Nexp, Lexp, Qexp]

/-- **The no-wrap capacity `E H < Q`.** -/
theorem Eexp_add_Hexp_lt_Qexp : Eexp + Hexp < Qexp := by
  norm_num [Wexp, Texp, Hexp, Mprimeexp, Eexp, Mexp, Nexp, Lexp, Qexp]

/-- The no-wrap capacity margin is exactly `1/7`. -/
theorem noWrap_margin : Qexp - (Eexp + Hexp) = 1 / 7 := by
  norm_num [Wexp, Texp, Hexp, Mprimeexp, Eexp, Mexp, Nexp, Lexp, Qexp]

/-- `|t| ≪ X^{4/35}`, at exponent level. -/
theorem Texp_eq : Texp = 4 / 35 := by
  norm_num [Wexp, Texp, Hexp, Mprimeexp, Eexp, Mexp, Nexp, Lexp, Qexp]

/-- The source-assisted diagonal amplitude margin `(W/Q)^{1/2} = X^{2/35}`. -/
theorem diagonal_amplitude_margin : (Wexp - Qexp) / 2 = 2 / 35 := by
  norm_num [Wexp, Texp, Hexp, Mprimeexp, Eexp, Mexp, Nexp, Lexp, Qexp]

/-! ## §6. Standard three-block range audit at the aggregate triple point

The aggregate triple point is `M' = E M = X^{3/7}`, `N = L = X^{2/7}`, `Q = X^{3/5}`. -/

/-- `M' = X^{3/7}`. -/
theorem Mprimeexp_eq : Mprimeexp = 3 / 7 := by
  norm_num [Wexp, Texp, Hexp, Mprimeexp, Eexp, Mexp, Nexp, Lexp, Qexp]

/-- `N L = X^{4/7}`. -/
theorem Nexp_add_Lexp : Nexp + Lexp = 4 / 7 := by
  norm_num [Wexp, Texp, Hexp, Mprimeexp, Eexp, Mexp, Nexp, Lexp, Qexp]

/-- **The unique first range defect candidate:** `N L / Q = X^{-1/35}`, i.e. `Q < N L`. -/
theorem range_defect : (Nexp + Lexp) - Qexp = -(1 / 35) := by
  norm_num [Wexp, Texp, Hexp, Mprimeexp, Eexp, Mexp, Nexp, Lexp, Qexp]

/-- `Q > X^{1/2}` with margin `1/10`. -/
theorem margin_Q_half : Qexp - 1 / 2 = 1 / 10 := by
  norm_num [Wexp, Texp, Hexp, Mprimeexp, Eexp, Mexp, Nexp, Lexp, Qexp]

/-- `N L < X^{2/3}` with margin `2/21`. -/
theorem margin_two_thirds : 2 / 3 - (Nexp + Lexp) = 2 / 21 := by
  norm_num [Wexp, Texp, Hexp, Mprimeexp, Eexp, Mexp, Nexp, Lexp, Qexp]

/-- `(3 + 4Q) - (9N + 8L) = 19/35`. -/
theorem margin_three_four : (3 + 4 * Qexp) - (9 * Nexp + 8 * Lexp) = 19 / 35 := by
  norm_num [Wexp, Texp, Hexp, Mprimeexp, Eexp, Mexp, Nexp, Lexp, Qexp]

/-- `(1 - Q) - N = 4/35`. -/
theorem margin_one_minus_Q : (1 - Qexp) - Nexp = 4 / 35 := by
  norm_num [Wexp, Texp, Hexp, Mprimeexp, Eexp, Mexp, Nexp, Lexp, Qexp]

/-- `(2 + 2Q) - (4N + 7L) = 2/35`. -/
theorem margin_two_two : (2 + 2 * Qexp) - (4 * Nexp + 7 * Lexp) = 2 / 35 := by
  norm_num [Wexp, Texp, Hexp, Mprimeexp, Eexp, Mexp, Nexp, Lexp, Qexp]

/-! ## §9 (exponent part). The source-assisted diagonal exponent identity -/

/-- `M · (Q E N L)^{1/2} = X · (Q / (E N L))^{1/2}` at exponent level. -/
theorem diagonal_exponent_identity :
    Mexp + (Qexp + Eexp + Nexp + Lexp) / 2 = 1 + (Qexp - Wexp) / 2 := by
  norm_num [Wexp, Texp, Hexp, Mprimeexp, Eexp, Mexp, Nexp, Lexp, Qexp]

/-- The resulting saving over the trivial exponent `1`: `1 + (Q - W)/2 = 1 - 2/35`. -/
theorem diagonal_exponent_value : 1 + (Qexp - Wexp) / 2 = 1 - 2 / 35 := by
  norm_num [Wexp, Texp, Hexp, Mprimeexp, Eexp, Mexp, Nexp, Lexp, Qexp]

/-- The numerical value of the source-assisted diagonal exponent, `33/35`. -/
theorem diagonal_exponent_eq : Mexp + (Qexp + Eexp + Nexp + Lexp) / 2 = 33 / 35 := by
  norm_num [Wexp, Texp, Hexp, Mprimeexp, Eexp, Mexp, Nexp, Lexp, Qexp]

/-- The Pro run's stated pre-splice off-diagonal target exponent `39/35` is *above* the
trivial-looking `1` by exactly `4/35 = Texp`; recorded so that the target cannot be
silently confused with a nontrivial saving. -/
theorem preSplice_target_gap : (39 : ℚ) / 35 - 1 = Texp := by
  norm_num [Wexp, Texp, Hexp, Mprimeexp, Eexp, Mexp, Nexp, Lexp, Qexp]

end Ledger3221
end Erdos287
