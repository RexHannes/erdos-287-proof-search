import Mathlib
import RequestProject.Erdos287.TwoProjectorPhysicalClosure3221

/-!
# Fixed-budget V22 arithmetic

`FIXED-BUDGET-V22-ARITHMETIC : KERNEL-PROVED`

The repaired safe bad-character ledger of `Erdos287.V22Ledger` gives, at the cutoff
exponent `B0 = 1`,

```
    Cvar(1) = 5,
```

and the two-projector closure criterion of `Erdos287.V22Closure` is exactly

```
    netLogExponent Cvar Cext = −(2 + Cvar)/2 + Cext  <  −1     ⟺     2·Cext < Cvar.
```

This file fixes **one explicit rational physical budget**

```
    CextStar = 9/4
```

and banks the finite arithmetic it produces:

```
    2·CextStar = 9/2 < 5,
    netLogExponent 5 CextStar = −5/4 < −1.
```

Nothing analytic is asserted: `CextStar` is a *chosen budget*, and the statement that the
physical log-prefactor really obeys it is an external input, isolated in
`Erdos287FixedBudgetPhysicalWrapper.lean`.  In particular **the strong all-`A` supersqrt
theorem is not proved and not used**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace FixedBudgetV22

open Erdos287.V22Ledger
open Erdos287.V22Closure

/-! ## §1.  The ledger value at `B0 = 1` -/

/-- The exact current V22 fact: `Cvar(1) = 5`. -/
theorem cvar_one_eq_five : cvar 1 = 5 := cvar_at_one

/-! ## §2.  The explicit fixed budget -/

/-- The chosen explicit rational physical log-prefactor budget. -/
def CextStar : ℚ := 9 / 4

/-- `2·CextStar = 9/2 < 5`: the fixed budget sits strictly inside the `B0 = 1` capacity. -/
theorem two_CextStar_lt_five : 2 * CextStar < 5 := by norm_num [CextStar]

/-- The exact net log exponent at the fixed budget. -/
theorem netLogExponent_five_CextStar : netLogExponent 5 CextStar = -5 / 4 := by
  norm_num [netLogExponent, CextStar]

/-- Hence the fixed budget closes the two-projector criterion. -/
theorem netLogExponent_five_CextStar_lt_neg_one : netLogExponent 5 CextStar < -1 := by
  rw [netLogExponent_five_CextStar]; norm_num

/-- **`fixedBudget_B0_one_closes_at_cext_nine_fourths`.**  `KERNEL-PROVED`.

At `B0 = 1`, with the explicit budget `Cext = 9/4`, the exact net log exponent is `−5/4`,
which is strictly below the closure threshold `−1`. -/
theorem fixedBudget_B0_one_closes_at_cext_nine_fourths :
    2 * CextStar < cvar 1 ∧
      netLogExponent (cvar 1) CextStar = -5 / 4 ∧
      netLogExponent (cvar 1) CextStar < -1 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [cvar_one_eq_five]
  · exact two_CextStar_lt_five
  · exact netLogExponent_five_CextStar
  · exact netLogExponent_five_CextStar_lt_neg_one

/-! ## §3.  The general fixed-budget criterion, and its sharpness -/

/-- Any budget strictly below `5/2` closes at `B0 = 1`; this is the whole content of the
fixed-budget route. -/
theorem fixedBudget_closes_of_two_cext_lt_five {cext : ℚ} (h : 2 * cext < 5) :
    netLogExponent (cvar 1) cext < -1 := closure_capacity_B0_one h

/-- Sharpness: the budget `5/2` is exactly the break-even point — the net exponent is `−1`
and the criterion **fails**.  No slack is hidden anywhere. -/
theorem fixedBudget_fails_at_five_halves :
    netLogExponent (cvar 1) (5 / 2) = -1 ∧ ¬ netLogExponent (cvar 1) (5 / 2) < -1 := by
  have h : netLogExponent (cvar 1) (5 / 2) = -1 := by
    rw [cvar_one_eq_five]; norm_num [netLogExponent]
  exact ⟨h, by rw [h]; norm_num⟩

/-- The fixed budget is a *choice*, not a theorem: some rational budgets do not close. -/
theorem fixedBudget_is_a_choice : ∃ cext : ℚ, ¬ netLogExponent (cvar 1) cext < -1 :=
  ⟨5 / 2, fixedBudget_fails_at_five_halves.2⟩

end FixedBudgetV22
end Erdos287
