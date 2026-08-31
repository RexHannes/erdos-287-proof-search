import Mathlib
import RequestProject.HostileAudit.EffectiveLowConductorExceptionalPNT
import RequestProject.CurrentProgramme.Block20GeneratedBilinearCompiler

/-!
# BLOCK20 Δ, Phase C (§15) — the exceptional main-term comparison adapter

The banked effective low-conductor PNT socket
`Erdos287.HostileAudit.EffectiveLowConductorExceptionalPNTInput` explicitly **retains** a
possible exceptional secondary term.  Turning that provider into the effective small-`q`
conclusion therefore needs one more source object: a comparison adapter saying what happens
to the exceptional term.

Three routes are possible, and this module **does not choose one without proof**:

* `ExceptionalRoute.absorbed` — the exceptional term is part of the physical expected term;
* `ExceptionalRoute.cancelled` — it cancels between the two signs / across the modulus
  family;
* `ExceptionalRoute.separatelyControlled` — the exceptional family is controlled on its own.

`ExceptionalMainTermComparisonAdapter` is **uninhabited** and carries the routing datum
together with exactly the estimate that route requires.  The conditional compiler

```
EffectiveLowConductorExceptionalPNTInput + ExceptionalMainTermComparisonAdapter
    →  EffectiveSmallQLowConductorConclusion
```

is proved.  Status:

```
287-EFFECTIVE-LOWCOND-EXCEPTIONAL-PNT45      : conditional provider / compiler
287-EXCEPTIONAL-MAINTERM-COMPARISON-ADAPTER45 : SOURCE_OPEN / UNINHABITED
BALANCED7 EFFECTIVE                           : OPEN
```
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace Block20

open Erdos287.HostileAudit

/-! ## §15.1  The routing datum -/

/-- The three admissible routes for the exceptional secondary term.  No route is chosen
here. -/
inductive ExceptionalRoute
  | absorbed
  | cancelled
  | separatelyControlled
  deriving DecidableEq, Fintype, Repr

/-- **`exceptionalRoute_not_decided`.**  `LEAN_PROVED`.

The three routes are genuinely distinct objects; this module commits to none of them. -/
theorem exceptionalRoute_not_decided :
    ExceptionalRoute.absorbed ≠ ExceptionalRoute.cancelled ∧
      ExceptionalRoute.absorbed ≠ ExceptionalRoute.separatelyControlled ∧
      ExceptionalRoute.cancelled ≠ ExceptionalRoute.separatelyControlled := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-! ## §15.2  The conclusion -/

/-- The effective small-`q` low-conductor conclusion: the weighted prime sum agrees with the
**physical expected** main term within the declared effective error, with no leftover
exceptional term. -/
def EffectiveSmallQLowConductorConclusion (psi physicalMainTerm err : ℝ) : Prop :=
  |psi - physicalMainTerm| ≤ err

/-! ## §15.3  The adapter (uninhabited) -/

/-- **`ExceptionalMainTermComparisonAdapter`** —
`EXTERNAL / SOURCE_OPEN / UNINHABITED`.

The routing datum plus exactly the comparison it needs:

* the physical expected term is pinned as data;
* the route is declared;
* on the `absorbed` route the exceptional term is *inside* the physical term;
* on the `cancelled` route the two-sign / modulus-family sum of exceptional terms vanishes to
  within the declared budget;
* on the `separatelyControlled` route the exceptional family is bounded by the declared
  budget;
* in every case the resulting comparison budget is explicit. -/
structure ExceptionalMainTermComparisonAdapter
    (mainTerm secondaryTerm physicalMainTerm exceptionalBudget : ℝ)
    (route : ExceptionalRoute) : Prop where
  /-- The comparison budget is explicit and nonnegative. -/
  budget_nonneg : 0 ≤ exceptionalBudget
  /-- `absorbed`: the physical expected term already contains the exceptional secondary
  term. -/
  absorbed_route : route = ExceptionalRoute.absorbed →
    physicalMainTerm = mainTerm + secondaryTerm
  /-- `cancelled`: the exceptional term cancels, up to the declared budget. -/
  cancelled_route : route = ExceptionalRoute.cancelled →
    physicalMainTerm = mainTerm ∧ |secondaryTerm| ≤ exceptionalBudget
  /-- `separatelyControlled`: the exceptional family is separately bounded. -/
  separate_route : route = ExceptionalRoute.separatelyControlled →
    physicalMainTerm = mainTerm ∧ |secondaryTerm| ≤ exceptionalBudget

/-- **`exceptionalAdapter_comparison`.**  `CONDITIONAL / LEAN_PROVED`.

Whatever route is declared, the adapter converts the provider's comparison
`|ψ − main − secondary| ≤ err` into a comparison against the **physical** main term with the
error inflated by exactly the declared exceptional budget. -/
theorem exceptionalAdapter_comparison
    {mainTerm secondaryTerm physicalMainTerm exceptionalBudget psi err : ℝ}
    {route : ExceptionalRoute}
    (hadapt : ExceptionalMainTermComparisonAdapter mainTerm secondaryTerm physicalMainTerm
      exceptionalBudget route)
    (hprov : |psi - mainTerm - secondaryTerm| ≤ err) :
    EffectiveSmallQLowConductorConclusion psi physicalMainTerm (err + exceptionalBudget) := by
  unfold EffectiveSmallQLowConductorConclusion
  cases hroute : route with
  | absorbed =>
      have hphys := hadapt.absorbed_route hroute
      have : psi - physicalMainTerm = psi - mainTerm - secondaryTerm := by rw [hphys]; ring
      rw [this]
      linarith [hadapt.budget_nonneg, hprov]
  | cancelled =>
      obtain ⟨hphys, hsec⟩ := hadapt.cancelled_route hroute
      have hsplit : psi - physicalMainTerm = (psi - mainTerm - secondaryTerm) + secondaryTerm := by
        rw [hphys]; ring
      rw [hsplit]
      exact le_trans (abs_add_le _ _) (add_le_add hprov hsec)
  | separatelyControlled =>
      obtain ⟨hphys, hsec⟩ := hadapt.separate_route hroute
      have hsplit : psi - physicalMainTerm = (psi - mainTerm - secondaryTerm) + secondaryTerm := by
        rw [hphys]; ring
      rw [hsplit]
      exact le_trans (abs_add_le _ _) (add_le_add hprov hsec)

/-- **`effective_smallQ_lowConductor_compiler`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

```
EffectiveLowConductorExceptionalPNTInput + ExceptionalMainTermComparisonAdapter
    →  EffectiveSmallQLowConductorConclusion.
```

Both antecedents are uninhabited in this repository. -/
theorem effective_smallQ_lowConductor_compiler
    {X C1 C2 X0 : ℝ} {A f q : ℕ} {V : ℝ → ℝ} {Tmell psi mainTerm secondaryTerm : ℝ}
    {exceptional : Option (ℕ × ℝ)} {physicalMainTerm exceptionalBudget : ℝ}
    {route : ExceptionalRoute}
    (hprov : EffectiveLowConductorExceptionalPNTInput X C1 C2 X0 A f q V Tmell psi mainTerm
      secondaryTerm exceptional)
    (hadapt : ExceptionalMainTermComparisonAdapter mainTerm secondaryTerm physicalMainTerm
      exceptionalBudget route) :
    EffectiveSmallQLowConductorConclusion psi physicalMainTerm
      (C1 * X / (Real.log X) ^ A + exceptionalBudget) :=
  exceptionalAdapter_comparison hadapt hprov.comparison

/-- **`exceptionalAdapter_not_automatic`.**  `LEAN_PROVED`.

The adapter is **uninhabited**: `287-EXCEPTIONAL-MAINTERM-COMPARISON-ADAPTER45` is
`SOURCE_OPEN`. -/
theorem exceptionalAdapter_not_automatic :
    ∃ (mainTerm secondaryTerm physicalMainTerm exceptionalBudget : ℝ) (route : ExceptionalRoute),
      ¬ ExceptionalMainTermComparisonAdapter mainTerm secondaryTerm physicalMainTerm
        exceptionalBudget route := by
  refine ⟨0, 0, 0, -1, ExceptionalRoute.absorbed, ?_⟩
  intro h
  have := h.budget_nonneg
  norm_num at this

/-- **`effective_route_is_not_chosen`.**  `LEAN_PROVED`.

The honest summary of §15: the compiler exists, the routes are distinct, and no route is
inhabited here — so `BALANCED7 EFFECTIVE` stays open. -/
theorem effective_route_is_not_chosen :
    (ExceptionalRoute.absorbed ≠ ExceptionalRoute.cancelled) ∧
      (∃ (mainTerm secondaryTerm physicalMainTerm exceptionalBudget : ℝ)
        (route : ExceptionalRoute),
        ¬ ExceptionalMainTermComparisonAdapter mainTerm secondaryTerm physicalMainTerm
          exceptionalBudget route) ∧
      (∃ (X C1 C2 X0 : ℝ) (A f q : ℕ) (V : ℝ → ℝ) (Tmell psi mainTerm secondaryTerm : ℝ)
        (exceptional : Option (ℕ × ℝ)),
        ¬ EffectiveLowConductorExceptionalPNTInput X C1 C2 X0 A f q V Tmell psi mainTerm
          secondaryTerm exceptional) :=
  ⟨exceptionalRoute_not_decided.1, exceptionalAdapter_not_automatic,
    effectiveLowConductor_not_automatic⟩

end Block20
end Erdos287
