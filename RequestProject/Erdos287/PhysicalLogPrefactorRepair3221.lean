import Mathlib
import RequestProject.Erdos287.SP2ClosureCompiler3221

/-!
# V24, §1–§2 — supersession of `C_ext = 0` and the repaired local hard-cell log margin

`3221-PHYSICAL-LOG-PREFAC45 : REPAIRED WITH C_ext = 1`

## What changed

The SP-2 bank carried the physical prefactor interface

```
    PhysicalLogPrefactorSP23221 cext  :  cext = 0
```

i.e. the claim that the literal packet carries **no** residual power of `log X`.  The
source-minimal identity actually used is

```
    Λ(2P + s) = ∑_{q r = 2P + s} μ(q) · log r,
```

and unless the source explicitly normalises by `log X` and restores an external `log X`
factor, the honest physical ledger keeps that one power of `log X`.  Accordingly:

```
    SP2PhysicalLogPrefactorOld  (C_ext = 0) : RETRACTED / INCOMPLETE NORMALIZATION
    SP2PhysicalLogPrefactorRepaired (C_ext = 1) : the safe replacement
```

The historical object is **not deleted**: it is `Erdos287.SP2Closure.PhysicalLogPrefactorSP23221`
and stays exactly where it was.  `oldPrefactor_and_repaired_are_incompatible` proves the two
cannot both hold, so the supersession is a theorem, not a relabelling.

## The repaired local margin

With the banked `C_var(1) = 5`, the outer two-prime squared log contribution `2` and the
repaired `C_ext = 1`:

```
    −(2 + 5)/2 + 1 = −5/2 < −1,        C_var − 2·C_ext = 5 − 2 = 3 > 0.
```

Both are kernel-checked below.  This is a statement about the **local** `Q = X^{3/5}`
hard cell only; it does not close Balanced7.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace V24Prefactor

open Erdos287.V22Closure Erdos287.V22Ledger Erdos287.SP2Closure

/-! ## §1.1  The repaired prefactor interface -/

/-- **`SP2PhysicalLogPrefactorRepaired`** — the safe physical ledger: the literal packet
carries exactly one power of `log X` between the physical object and the normalised
`V_hi = AA − BA − AB + BB`. -/
structure SP2PhysicalLogPrefactorRepaired (cext : ℚ) : Prop where
  /-- The repaired residual power of `log X`. -/
  cext_eq_one : cext = 1

/-- The repaired constant. -/
def sp2CextRepaired : ℚ := 1

theorem sp2CextRepaired_spec : SP2PhysicalLogPrefactorRepaired sp2CextRepaired := ⟨rfl⟩

/-- **`oldPrefactor_and_repaired_are_incompatible`.**  `LEAN_PROVED`.

The retraction is a theorem: no exponent satisfies both the old `C_ext = 0` interface and
the repaired `C_ext = 1` one. -/
theorem oldPrefactor_and_repaired_are_incompatible (cext : ℚ) :
    ¬ (PhysicalLogPrefactorSP23221 cext ∧ SP2PhysicalLogPrefactorRepaired cext) := by
  rintro ⟨h0, h1⟩
  have e0 := h0.cext_eq_zero
  have e1 := h1.cext_eq_one
  rw [e0] at e1
  norm_num at e1

/-- **`repairedPrefactor_not_automatic`.**  `LEAN_PROVED`. -/
theorem repairedPrefactor_not_automatic :
    ∃ cext : ℚ, ¬ SP2PhysicalLogPrefactorRepaired cext := by
  refine ⟨0, ?_⟩
  intro h
  have := h.cext_eq_one
  norm_num at this

/-! ## §2  The repaired local hard-cell margin -/

/-- **`q35_netLogExponent_eq_neg_five_halves`.**  `LEAN_PROVED` (kernel arithmetic).

`−(2 + C_var(1))/2 + C_ext = −(2 + 5)/2 + 1 = −5/2`. -/
theorem q35_netLogExponent_eq_neg_five_halves :
    netLogExponent (cvar sp2B0) sp2CextRepaired = -5 / 2 := by
  rw [sp2_cvar_eq_five]
  unfold netLogExponent sp2CextRepaired
  norm_num

/-- **`q35_netLogExponent_lt_neg_one`.**  `LEAN_PROVED`.

`−5/2 < −1`: the repaired numerology still clears the `X/log X` threshold, now with margin
`3/2` rather than `5/2`. -/
theorem q35_netLogExponent_lt_neg_one :
    netLogExponent (cvar sp2B0) sp2CextRepaired < -1 := by
  rw [q35_netLogExponent_eq_neg_five_halves]
  norm_num

/-- **`q35_signed_log_margin`.**  `LEAN_PROVED`.

`C_var − 2·C_ext = 5 − 2 = 3 > 0`. -/
theorem q35_signed_log_margin :
    cvar sp2B0 - 2 * sp2CextRepaired = 3 ∧ (0 : ℚ) < cvar sp2B0 - 2 * sp2CextRepaired := by
  rw [sp2_cvar_eq_five]
  unfold sp2CextRepaired
  norm_num

/-- **`q35_local_capacity_pass`.**  `LEAN_PROVED`.

The `Q = X^{3/5}` local `3221` log capacity passes with the repaired prefactor.  This is
*local*: it is a statement about one hard dyadic cell and about nothing else. -/
theorem q35_local_capacity_pass :
    netLogExponent (cvar sp2B0) sp2CextRepaired < -1 ∧
      (0 : ℚ) < cvar sp2B0 - 2 * sp2CextRepaired :=
  ⟨q35_netLogExponent_lt_neg_one, q35_signed_log_margin.2⟩

/-- **`q35_capacity_is_not_balancedSeven`.**  `LEAN_PROVED`.

The local capacity check is compatible with the full comparison still failing: the
repository's comparison object remains refutable.  Local capacity therefore does not infer
full Balanced7 closure. -/
theorem q35_capacity_is_not_balancedSeven :
    ∃ X Dcut B0 hard model err : ℝ,
      ¬ Erdos287.V20Compiler.MuLogComparisonAtCutoff X Dcut B0 hard model err :=
  Erdos287.V20Compiler.comparisonAtCutoff_not_automatic

end V24Prefactor
end Erdos287
