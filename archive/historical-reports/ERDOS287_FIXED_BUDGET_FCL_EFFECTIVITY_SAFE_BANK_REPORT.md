# ERDŐS #287 — FIXED-BUDGET V22 / FCL / EFFECTIVITY FIREWALL (APPEND-ONLY SAFE BANK)

**Status of Erdős #287: OPEN.**  Nothing in this pass proves it; the strong all-`A`
supersqrt theorem is **not** proved and is explicitly recorded as non-controlling.

Strictly append-only: no existing file was deleted, renamed, weakened or rewritten.  The
only change to an existing file is the appending of eight `import` lines to
`RequestProject/Main.lean`.

---

## 1. Files added

| File | Content |
|---|---|
| `RequestProject/CurrentProgramme/Erdos287FixedBudgetV22Arithmetic.lean` | §1 — `Cvar(1) = 5`, `CextStar = 9/4`, `2·CextStar < 5`, `netLogExponent 5 CextStar = −5/4 < −1` |
| `RequestProject/CurrentProgramme/Erdos287FixedDCutoffRepair.lean` | §2 — source-exact fixed-`D` cutoff interface at `D = log X`, `B0 = 1`; adapter from the banked stronger interface; refutation of the converse |
| `RequestProject/CurrentProgramme/Erdos287FixedBudgetPhysicalWrapper.lean` | §3 — `FixedBudgetTwoProjectorPhysical3221Inputs` (uninhabited) and its conditional closure compiler |
| `RequestProject/CurrentProgramme/Erdos287AllAFirewall.lean` | §4 — `FixedBudgetCorrelationInput` vs `ArbitraryLogCorrelationInput`, with the firewall |
| `RequestProject/CurrentProgramme/Erdos287FCLAlgebraicBridge.lean` | §5–§7 — generic scaling bridge into the banked FCL compiler, comparison-margin firewall, `N2` separation |
| `RequestProject/CurrentProgramme/Erdos287WindowPairExportEffectivity.lean` | §8–§10 — window-pair export dictionary, effectivity firewall, conditional end-to-end adapter |
| `RequestProject/Status/CurrentStatusErdos287FixedBudgetEffectivity.lean` | §11 — authoritative append-only status layer with backing theorems |
| `RequestProject/Status/AxiomAuditErdos287FixedBudgetEffectivity.lean` | `#print axioms` for all 55 principal theorems of this pass |
| `ERDOS287_FIXED_BUDGET_FCL_EFFECTIVITY_SAFE_BANK_REPORT.md` | this report |

## 2. File modified

* `RequestProject/Main.lean` — eight appended `import` lines only.

---

## 3. Section-by-section

### §1 Fixed-budget arithmetic — **KERNEL-PROVED**

```
cvar_one_eq_five                                  : Cvar(1) = 5
CextStar                                          : 9/4
two_CextStar_lt_five                              : 2·CextStar < 5
netLogExponent_five_CextStar                      : netLogExponent 5 CextStar = −5/4
netLogExponent_five_CextStar_lt_neg_one           : < −1
fixedBudget_B0_one_closes_at_cext_nine_fourths    : all three at once
fixedBudget_closes_of_two_cext_lt_five            : the general criterion
fixedBudget_fails_at_five_halves                  : exact break-even at 5/2
fixedBudget_is_a_choice                           : the budget is a choice, not a theorem
```

### §2 Fixed-`D` cutoff repair — **KERNEL-PROVED**

`FixedDCutoffCompat3221` requires only `Dana = Dphys = log X` and the vanishing statements
*at that cutoff*.  The banked `HighProjectorCutoffCompat3221` is untouched.

```
sharedCutoff_one                        : sharedCutoff 1 X = log X
fixedD_cutoffs_match
fixedD_of_strong                        : strong (B0 = 1) ⇒ fixed        [valid adapter]
fixedD_does_not_give_all_D_invariance   : the converse is FALSE          [firewall]
fixedD_not_automatic                    : the fixed interface is still an obligation
```

### §3 Fixed-budget physical wrapper — **EXTERNAL / CONDITIONAL / UNINHABITED**

`FixedBudgetTwoProjectorPhysical3221Inputs` packages the literal external source interfaces
of the banked physical package at `B0 = 1`, with the fixed-`D` cutoff field and the explicit
budget field `2·Cext < 5`.  No analytic field is inhabited; no axiom is introduced.

```
fixedBudgetPhysical_closes_logVar                    : ⇒ log-variance input ∧ netLog < −1
fixedBudgetPhysical_netExponent_at_CextStar          : = −5/4 at the distinguished budget
twoProjectorPhysical_of_fixedBudget_and_strongCutoff : wrapper + strong cutoff ⇒ banked pkg
fixedBudgetPhysical_budget_not_automatic
```

### §4 All-`A` firewall — **KERNEL-PROVED**

```
fixedBudget_of_arbitrary            : all-A ⇒ fixed budget at every A       [valid]
arbitrary_not_of_fixedBudget        : fixed budget ⇏ all-A                  [firewall]
allA_object_is_noncontrolling       : both, as one status fact
fixedBudgetCorrelation_not_automatic
```

The all-`A` object is **never derived**.

### §5 FCL algebraic bridge — **CONDITIONAL**

```
fcl_relative_error_of_scaling :
    0 < X, 0 < log X, 0 < cB, 0 ≤ δ,
    cB·X/log X ≤ B,  E ≤ cE·X/(log X)^{1+η},  cE ≤ δ·cB·(log X)^η   ⟹   E ≤ δ·B
fcl_prime_mass_pos_of_scaling : feeds the banked positivity compiler
fcl_threshold_not_automatic   : the threshold hypothesis can fail
```

All asymptotic/external hypotheses are explicit antecedents.

### §6 Comparison-margin firewall — **SOURCE OPEN**

`Erdos287.FordData.CertificatePinned` and `Erdos287.FordData.PositiveComparisonMargin` are
**not inhabited**.  The conditional wrapper `PositiveMarginSupply` exposes exactly
`0 < 1 + Cc`, and yields the finite arithmetic

```
margin_delta_arithmetic : 0 ≤ (1+Cc)/6  ∧  3·((1+Cc)/6) < 1+Cc
fcl_prime_mass_pos_of_margin
positiveMargin_not_automatic
certificatePinned_not_automatic
```

### §7 `N2` separation — **KERNEL-PROVED**

```
fcl_N2_additive         : the banked N2 compiler, restated with the slack visible
N2_slack_is_not_absorbed: a positive N2 slack strictly weakens the bound
```

No hidden absorption.

### §8 Window-pair export interface — **OPEN / UNINHABITED**

`FixedCertificatePrimeMassToWindowPairInput d M x pu au pv av` carries every required
field — positive certificate prime mass, `x`, `(pu, au)`, `(pv, av)`, both divisibilities,
both windows `≤ 9`, both `CVal` inequalities, `M ≤ 2x`, `x + 1 ≤ M` — and its conclusion is
literally `Erdos287.WindowPairSupply M`:

```
windowPairSupply_of_export
export_input_not_automatic
```

### §9 Effectivity firewall — **OPEN**

```
EventualSupply p        : ∃ M0, ∀ M ≥ M0, p M                    (non-effective)
EffectiveSupply p       : structure carrying M0 : ℕ and the supply (effective)
EffectiveSupply.Bounded : M0 ≤ 4000000000                        (recorded separately)

eventual_of_effective
eventual_does_not_give_bounded_effective :
    an eventual supply need not admit ANY threshold inside the verified finite range
```

No "sufficiently large" statement is converted into a `Nat` witness.

### §10 End-to-end adapter — **CONDITIONAL only**

```
closureInputs_of_boundedEffective     : bounded effective supply ⇒ Erdos287ClosureInputs
erdos287Statement_of_boundedEffective : ⇒ Erdos287Statement, via the banked compiler
adapter_needs_effective_supply
```

Neither premise is inhabited.

---

## 4. Build

Every new module was built individually (all clean).  Full build:

```
lake build
jobs      : 8352
errors    : 0
warnings  : 32   (all pre-existing in older files; 0 from the new files)
```

No historical file was moved, excluded or disabled.

## 5. Axiom audit

`RequestProject/Status/AxiomAuditErdos287FixedBudgetEffectivity.lean` prints the axioms of
all `55` principal theorems of this pass:

* `47` report `[propext, Classical.choice, Quot.sound]`, `[propext, Quot.sound]` or
  `[propext]`;
* `8` report *no axiom dependency at all*.

No `sorry`, `sorryAx`, custom `axiom`, `native_decide`, `unsafe` or `implemented_by` occurs
anywhere in the new files.

---

## 6. FINAL BLOCK

```
STRONG ALL-A SUPERSQRT:
    OPEN / NONCONTROLLING
    (firewall proved: fixed-budget input ⇏ arbitrary-A object)

FIXED-BUDGET V22 ARITHMETIC:
    KERNEL-PROVED
    Cvar(1) = 5;  CextStar = 9/4;  2·CextStar < 5;
    netLogExponent 5 CextStar = −5/4 < −1

FIXED-D CUTOFF REPAIR:
    KERNEL-PROVED
    strong (B0 = 1) ⇒ fixed;  converse refuted;  stronger interface untouched

FIXED-BUDGET PHYSICAL ANALYTIC INPUT:
    EXTERNAL / CONDITIONAL / UNINHABITED

CERTIFICATE POSITIVE MARGIN:
    SOURCE OPEN unless supplied
    CertificatePinned and PositiveComparisonMargin are not inhabited;
    conditional wrapper exposes exactly 0 < 1 + Cc, with δ = (1+Cc)/6 and 3δ < 1+Cc

FCL:
    CONDITIONAL
    generic scaling bridge proved; all analytic hypotheses explicit

N2 SEPARATION:
    KERNEL-PROVED, ADDITIVE ONLY, NO ABSORPTION

WINDOWPAIR EXPORT:
    OPEN unless supplied
    interface complete, conclusion literally WindowPairSupply M, uninhabited

EFFECTIVITY:
    OPEN unless supplied
    eventual vs effective separated; the ≤ 4·10⁹ bound recorded separately;
    no conversion of "sufficiently large" into a Nat witness

END-TO-END ADAPTER:
    CONDITIONAL ONLY; premises not inhabited

ERDOS287:
    OPEN

BUILD:
    lake build — 8352 jobs, 0 errors, 32 warnings (all pre-existing; 0 from new files)

AXIOM AUDIT:
    propext, Classical.choice, Quot.sound only
    no sorry, no sorryAx, no custom axiom, no native_decide, no unsafe, no implemented_by
```

STOP.
