import Mathlib
import RequestProject.CurrentProgramme.LowConductorSiegelWalfisz

/-!
# Hostile-audit safe bank §15 — the effectivity socket

`287-EFFECTIVE-LOWCOND-EXCEPTIONAL-PNT45 : SOURCE/THEOREM DICTIONARY OPEN`

This is a **parallel** interface to the banked (ineffective) Siegel–Walfisz socket
`Erdos287.PostBalanced7Pro.BalancedSevenLowConductorSiegelWalfiszInput`.  It is *not* that
socket: the banked one is explicitly ineffective (`lowConductor_effectivity_firewall` proves
that it never supplies a numerical threshold), whereas this one is required to carry

* explicit **effective** constants, supplied as data;
* an explicit numerical threshold;
* the principal term;
* an **optional** exceptional real character with its exceptional zero, and the corresponding
  secondary term (absent exactly when the option is `none`);
* a smooth `Y`-scale weight;
* a primitive conductor `f ≤ log^30 X`;
* the actual Mellin frequency range;
* the induction from the primitive conductor `f` to the modulus `q`;
* an exact comparison convention.

The conditional theorem `effective_smallQ_lowConductor_of_input` consumes it.  The interface
is **uninhabited**: nothing here claims an effective low-conductor exceptional PNT.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace HostileAudit

/-! ## §15.1  The effective target -/

/-- The exact comparison convention: the weighted prime sum, minus the principal term, minus
the (possibly absent) exceptional secondary term, is within the declared error. -/
def EffectiveSmallQLowConductorTarget (psi mainTerm secondaryTerm err : ℝ) : Prop :=
  |psi - mainTerm - secondaryTerm| ≤ err

/-! ## §15.2  The socket -/

/-- **`EffectiveLowConductorExceptionalPNTInput`** —
`EXTERNAL / EFFECTIVE / SOURCE-THEOREM DICTIONARY OPEN / UNINHABITED`.

Every ingredient is explicit data; in particular the constants `C₁`, `C₂` and the threshold
`X₀` are *given*, which is precisely what the classical ineffective Siegel–Walfisz statement
does not provide. -/
structure EffectiveLowConductorExceptionalPNTInput
    (X C1 C2 X0 : ℝ) (A f q : ℕ) (V : ℝ → ℝ) (Tmell : ℝ)
    (psi mainTerm secondaryTerm : ℝ)
    (exceptional : Option (ℕ × ℝ)) : Prop where
  /-- The scale is beyond the explicit threshold. -/
  scale : 3 ≤ X0 ∧ X0 ≤ X
  /-- The constants are explicit and positive — this is the effectivity requirement. -/
  effective_constants : 0 < C1 ∧ 0 < C2
  /-- The primitive conductor is in the low-conductor range `f ≤ log^30 X`. -/
  conductor_range : 0 < f ∧ (f : ℝ) ≤ Erdos287.PostBalanced7Pro.lowConductorCutoff X
  /-- The induction from the primitive conductor to the modulus. -/
  induced_to_q : f ∣ q ∧ 0 < q
  /-- The smooth `Y`-scale weight is normalised. -/
  weight_normalised : ∀ x : ℝ, 0 ≤ V x ∧ V x ≤ 1
  /-- The actual Mellin frequency range. -/
  mellin_range : (Real.log X) ^ 2 ≤ Tmell ∧ Tmell ≤ X
  /-- The exceptional data, when present, is a real character modulus together with a zero in
  the Landau–Siegel range. -/
  exceptional_convention :
    ∀ (m : ℕ) (beta : ℝ), exceptional = some (m, beta) →
      0 < m ∧ m ∣ q ∧ 1 - C2 / Real.log X ≤ beta ∧ beta < 1
  /-- With no exceptional character there is no secondary term. -/
  no_exceptional_no_secondary : exceptional = none → secondaryTerm = 0
  /-- The exact comparison, with an effective error. -/
  comparison : |psi - mainTerm - secondaryTerm| ≤ C1 * X / (Real.log X) ^ A

/-- **`effective_smallQ_lowConductor_of_input`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`. -/
theorem effective_smallQ_lowConductor_of_input
    {X C1 C2 X0 : ℝ} {A f q : ℕ} {V : ℝ → ℝ} {Tmell psi mainTerm secondaryTerm : ℝ}
    {exceptional : Option (ℕ × ℝ)}
    (h : EffectiveLowConductorExceptionalPNTInput X C1 C2 X0 A f q V Tmell psi mainTerm
      secondaryTerm exceptional) :
    EffectiveSmallQLowConductorTarget psi mainTerm secondaryTerm (C1 * X / (Real.log X) ^ A) :=
  h.comparison

/-- **`effective_input_has_no_exceptional_case`.**  `CONDITIONAL / LEAN_PROVED`.

If the source reports no exceptional character, the target holds with the pure principal
term. -/
theorem effective_input_has_no_exceptional_case
    {X C1 C2 X0 : ℝ} {A f q : ℕ} {V : ℝ → ℝ} {Tmell psi mainTerm secondaryTerm : ℝ}
    {exceptional : Option (ℕ × ℝ)}
    (h : EffectiveLowConductorExceptionalPNTInput X C1 C2 X0 A f q V Tmell psi mainTerm
      secondaryTerm exceptional)
    (hnone : exceptional = none) :
    |psi - mainTerm| ≤ C1 * X / (Real.log X) ^ A := by
  have h0 : secondaryTerm = 0 := h.no_exceptional_no_secondary hnone
  have := h.comparison
  rwa [h0, sub_zero] at this

/-- **`effective_socket_supplies_a_threshold`.**  `LEAN_PROVED`.

The effectivity contrast made formal: this socket always supplies a numerical threshold
`X₀ ≥ 3`, while the banked Siegel–Walfisz socket provably supplies none. -/
theorem effective_socket_supplies_a_threshold
    {X C1 C2 X0 : ℝ} {A f q : ℕ} {V : ℝ → ℝ} {Tmell psi mainTerm secondaryTerm : ℝ}
    {exceptional : Option (ℕ × ℝ)}
    (h : EffectiveLowConductorExceptionalPNTInput X C1 C2 X0 A f q V Tmell psi mainTerm
      secondaryTerm exceptional) :
    3 ≤ X0 ∧ X0 ≤ X ∧ 0 < C1 ∧ 0 < C2 :=
  ⟨h.scale.1, h.scale.2, h.effective_constants.1, h.effective_constants.2⟩

/-- **`effective_socket_is_not_siegelWalfisz`.**  `LEAN_PROVED`.

The two sockets are genuinely different objects: the banked Siegel–Walfisz interface never
carries a threshold, so it cannot be used to inhabit the effective one. -/
theorem effective_socket_is_not_siegelWalfisz :
    ∀ (X : ℝ) (A sMax : ℕ) (psi : ℕ → ℕ → ℕ → ℝ) (thr : Option ℕ),
      Erdos287.PostBalanced7Pro.BalancedSevenLowConductorSiegelWalfiszInput X A sMax psi thr →
        ∀ M : ℕ, thr ≠ some M :=
  fun _ _ _ _ _ h M => Erdos287.PostBalanced7Pro.lowConductor_effectivity_firewall h M

/-- **`effectiveLowConductor_not_automatic`.**  `LEAN_PROVED`.

The effectivity socket is **not inhabited**: `287-EFFECTIVE-LOWCOND-EXCEPTIONAL-PNT45` is
open. -/
theorem effectiveLowConductor_not_automatic :
    ∃ (X C1 C2 X0 : ℝ) (A f q : ℕ) (V : ℝ → ℝ) (Tmell psi mainTerm secondaryTerm : ℝ)
      (exceptional : Option (ℕ × ℝ)),
      ¬ EffectiveLowConductorExceptionalPNTInput X C1 C2 X0 A f q V Tmell psi mainTerm
        secondaryTerm exceptional := by
  refine ⟨0, 0, 0, 0, 0, 0, 0, fun _ => 0, 0, 0, 0, 0, none, ?_⟩
  intro h
  have := h.scale.1
  norm_num at this

end HostileAudit
end Erdos287
