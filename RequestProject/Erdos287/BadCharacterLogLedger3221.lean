import Mathlib
import RequestProject.Erdos287.BadCharacterCount3221
import RequestProject.Erdos287.PhysicalLogBudget3221

/-!
# V22, Phase 1 — the abstract log-power cutoff and the repaired `Cvar(B0)` ledger

`BADCHAR-D2-RELEDGER45 : FINITE / LOG-LEDGER PASS`

The safe bad-character count of V21 is `#Bad(q,D) ≤ (D+1)²` — **two** powers of `D`, not
one, and no `τ(q)`.  Any compiler whose log arithmetic silently assumed a single power of
`D` is therefore re-ledgered here, with the cutoff exponent `B0 : ℕ` kept **abstract**:

```
D = (log X)^{B0}     (asymptotic/log-ledger level only; no physical B0 is claimed)
```

Under the five-prime `L¹` input of strength `P5 ≤ W5 · log^{−5+o(1)}` and the full–full
child `AA ≤ X^{39/35} log^{−5+o(1)}`, the repaired expected channel exponents are

```
BB      :  −10 + 4·B0
BA / AB :  −15/2 + 2·B0          (via Cauchy)
```

and the resulting variance log exponent is

```
Cvar(B0) = min( 5 , 15/2 − 2 B0 , 10 − 4 B0 ),
```

represented here in **doubled integer arithmetic** to avoid rationals inside the finite
kernel checks:

```
2·Cvar(B0) = min( 10 , 15 − 4 B0 , 20 − 8 B0 ).
```

Kernel-checked samples: `Cvar(1) = 5`, `Cvar(2) = 2`, `Cvar(3) = −2`.

**No closure follows from this arithmetic.**  These are bookkeeping identities; the channel
bounds themselves remain open analytic inputs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace V22Ledger

/-! ## §1. The abstract cutoff exponent -/

/-- The abstract log-power cutoff `D = (log X)^{B0}`, at the ledger level only. -/
noncomputable def cutoffOfB0 (B0 : ℕ) (X : ℝ) : ℝ := Real.log X ^ (B0 : ℝ)

theorem cutoffOfB0_eq_sharedCutoff (B0 : ℕ) (X : ℝ) :
    cutoffOfB0 B0 X = Erdos287.V21Cutoff.sharedCutoff B0 X := rfl

/-! ## §2. The doubled channel exponents -/

/-- `2 × ` the full–full (`AA`) log exponent: `2·5 = 10`. -/
def aaDoubledExponent : ℤ := 10

/-- `2 × ` the `BB` log exponent `10 − 4 B0`, under the safe `D²` bad-character count. -/
def bb_logExponent (B0 : ℕ) : ℤ := 20 - 8 * (B0 : ℤ)

/-- `2 × ` the `BA` (and, symmetrically, `AB`) log exponent `15/2 − 2 B0`. -/
def ba_logExponent (B0 : ℕ) : ℤ := 15 - 4 * (B0 : ℤ)

/-- `2 × Cvar(B0) = min(10, 15 − 4B0, 20 − 8B0)`. -/
def highProjectorVarianceLogExponent (B0 : ℕ) : ℤ :=
  min aaDoubledExponent (min (ba_logExponent B0) (bb_logExponent B0))

/-- The rational form `Cvar(B0)`. -/
def cvar (B0 : ℕ) : ℚ := (highProjectorVarianceLogExponent B0 : ℚ) / 2

theorem cvar_doubled (B0 : ℕ) :
    2 * cvar B0 = (highProjectorVarianceLogExponent B0 : ℚ) := by
  rw [cvar]; ring

/-! ## §3. Kernel-checked samples -/

theorem cvar_doubled_at_one : highProjectorVarianceLogExponent 1 = 10 := by decide

theorem cvar_doubled_at_two : highProjectorVarianceLogExponent 2 = 4 := by decide

theorem cvar_doubled_at_three : highProjectorVarianceLogExponent 3 = -4 := by decide

theorem cvar_at_one : cvar 1 = 5 := by
  rw [cvar, cvar_doubled_at_one]; norm_num

theorem cvar_at_two : cvar 2 = 2 := by
  rw [cvar, cvar_doubled_at_two]; norm_num

theorem cvar_at_three : cvar 3 = -2 := by
  rw [cvar, cvar_doubled_at_three]; norm_num

/-- The ledger is genuinely `B0`-dependent and eventually negative: the safe `D²` count
costs `4 B0` in the `BB` channel, so no compiler may assume a single power of `D`. -/
theorem cvar_decreasing_sample : cvar 1 > cvar 2 ∧ cvar 2 > cvar 3 ∧ cvar 3 < 0 := by
  rw [cvar_at_one, cvar_at_two, cvar_at_three]
  norm_num

/-- `Cvar(B0)` is the minimum of the three channel exponents (rational form). -/
theorem cvar_le_channels (B0 : ℕ) :
    2 * cvar B0 ≤ (aaDoubledExponent : ℚ) ∧
      2 * cvar B0 ≤ (ba_logExponent B0 : ℚ) ∧
      2 * cvar B0 ≤ (bb_logExponent B0 : ℚ) := by
  rw [cvar_doubled, highProjectorVarianceLogExponent]
  refine ⟨?_, ?_, ?_⟩ <;> exact_mod_cast by
    first
      | exact min_le_left _ _
      | exact le_trans (min_le_right _ _) (min_le_left _ _)
      | exact le_trans (min_le_right _ _) (min_le_right _ _)

end V22Ledger
end Erdos287
