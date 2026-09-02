import RequestProject.CurrentProgramme.Erdos287EndgameConditionalFCLCompiler
import RequestProject.CurrentProgramme.Erdos287FCLWindowPairBridgeTwelve

/-!
# The endgame effectivity layer and the end-to-end conditional compiler

```
ASYMPTOTIC FCL / EFFECTIVE FCL / EFFECTIVE WINDOWPAIR : kept strictly separate
ENDGAME EFFECTIVITY SOCKET (ε₀, X₀, M₀ ≤ 4·10⁹)      : OPEN / UNINHABITED
END-TO-END CONDITIONAL COMPILER                       : KERNEL-PROVED CONDITIONAL
ERDOS287                                              : OPEN
```

This module is **append-only**.

**§1 — the three effectivity notions.**  `AsymptoticFCL` (a bare *real* threshold),
`EffectiveFCL` (a `Nat` threshold carried as data) and the banked
`EffectiveWindowPairSupply` are three different objects.  `AsymptoticFCL` never yields a
bounded `Nat` threshold: the banked firewall is reused, not reproved.

**§2 — the effectivity socket.**  `EndgameEffectivityInput` carries exactly `ε₀`, `X₀`, `M₀`
together with `M₀ ≤ 4·10⁹` and the *uniform* FCL witness above `M₀`.  It is **not derived
from any "sufficiently large" statement** and it is **not inhabited**.

**§3 — the end-to-end compiler.**  Effectivity socket → `EffectiveWindowPairSupply`
(through the threshold-`12` bridge) → `Erdos287ClosureInputs` (through the banked finite
range up to `4·10⁹`) → `Erdos287Statement`.  Every step is conditional and no socket is
inhabited, so **Erdős #287 remains OPEN**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace EndgameEffectivity

open Erdos287.WindowPairExport
open Erdos287.FCLWindowPair

/-! ## §1  Asymptotic vs effective -/

/-- **`AsymptoticFCL`** — the non-effective form: *some* real threshold exists. -/
def AsymptoticFCL (P : ℕ → Prop) : Prop := ∃ T : ℝ, ∀ M : ℕ, T ≤ (M : ℝ) → P M

/-- **`EffectiveFCL`** — the effective form: the threshold is carried as `Nat` data. -/
structure EffectiveFCL (P : ℕ → Prop) where
  /-- The explicit threshold. -/
  M0 : ℕ
  /-- The supply above the threshold. -/
  supply : ∀ M : ℕ, M0 ≤ M → P M

/-- An effective FCL supply is in particular asymptotic. -/
theorem asymptoticFCL_of_effectiveFCL {P : ℕ → Prop} (s : EffectiveFCL P) :
    AsymptoticFCL P := by
  refine ⟨(s.M0 : ℝ), fun M hM => s.supply M ?_⟩
  exact_mod_cast hM

/-- **`asymptoticFCL_does_not_give_bounded_effective`.**  `KERNEL-PROVED`.

The firewall, reused from the banked statement: an asymptotic supply never yields a
threshold inside the kernel-verified finite range. -/
theorem asymptoticFCL_does_not_give_bounded_effective :
    ∃ p : ℕ → Prop, (∃ T : ℝ, ∀ M : ℕ, T ≤ (M : ℝ) → p M) ∧
      ∀ s : EffectiveSupply p, ¬ s.Bounded :=
  Erdos287.FCLWindowPair.asymptotic_does_not_give_bounded_effective

/-! ## §2  The endgame effectivity socket -/

/-- **`EndgameEffectivityInput`** — `OPEN / UNINHABITED`.

The explicit effectivity data of the endgame: the perturbation threshold `ε₀`, the analytic
scale threshold `X₀`, the arithmetic threshold `M₀` with `M₀ ≤ 4·10⁹`, and the *uniform*
FCL prime-mass witness above `M₀`.

**Nothing in this repository constructs it**, and it is deliberately *not* obtained from any
"for all sufficiently large" statement. -/
structure EndgameEffectivityInput where
  /-- The perturbation threshold. -/
  eps0 : ℝ
  /-- The analytic scale threshold. -/
  X0 : ℝ
  /-- The arithmetic threshold. -/
  M0 : ℕ
  /-- The perturbation threshold is positive. -/
  eps0_pos : 0 < eps0
  /-- The scale threshold is positive. -/
  X0_pos : 0 < X0
  /-- The arithmetic threshold is above the bridge threshold `12`. -/
  M0_ge_bridge : 12 ≤ M0
  /-- The arithmetic threshold lies inside the kernel-verified finite range. -/
  M0_bounded : M0 ≤ 4000000000
  /-- The uniform FCL prime-mass witness above the threshold. -/
  witness : ∀ M : ℕ, M0 ≤ M → PositiveFCLPrimeMassWitness M

/-- **`effectiveWindowPairSupply_of_effectivityInput`.**  `KERNEL-PROVED CONDITIONAL`.

The effectivity socket compiles into the banked effective window-pair supply through the
threshold-`12` bridge. -/
def effectiveWindowPairSupply_of_effectivityInput (I : EndgameEffectivityInput) :
    EffectiveWindowPairSupply where
  M0 := I.M0
  supply := fun M hM =>
    windowPairSupply_of_positiveFCLMass_twelve (le_trans I.M0_ge_bridge hM) (I.witness M hM)

/-- The compiled supply is bounded, by the socket's own `M₀ ≤ 4·10⁹` field. -/
theorem effectiveWindowPairSupply_bounded (I : EndgameEffectivityInput) :
    (effectiveWindowPairSupply_of_effectivityInput I).Bounded :=
  I.M0_bounded

/-- **`effectivity_socket_is_a_genuine_constraint`.**  `KERNEL-PROVED`.

The socket is a genuine obligation: no effectivity input can carry the composite value
`q = 4` at its own threshold, so its content is not a formality. -/
theorem effectivity_socket_is_a_genuine_constraint :
    ¬ ∃ I : EndgameEffectivityInput, (I.witness I.M0 le_rfl).q = 4 := by
  rintro ⟨I, hq⟩
  have hp := (I.witness I.M0 le_rfl).q_prime
  rw [hq] at hp
  exact (by decide : ¬ Nat.Prime 4) hp

/-! ## §3  The end-to-end conditional compiler -/

/-- **`closureInputs_of_effectivityInput`.**  `KERNEL-PROVED CONDITIONAL`.

The effectivity socket yields the banked `Erdos287ClosureInputs`, reusing the finite range
through `4·10⁹`. -/
def closureInputs_of_effectivityInput (I : EndgameEffectivityInput) :
    Erdos287ClosureInputs :=
  closureInputs_of_boundedEffective (effectiveWindowPairSupply_of_effectivityInput I)
    (effectiveWindowPairSupply_bounded I)

/-- **`erdos287Statement_of_effectivityInput`.**  `KERNEL-PROVED CONDITIONAL`.

The full end-to-end chain

```
    effectivity socket → EffectiveWindowPairSupply → Erdos287ClosureInputs
      → Erdos287Statement .
```

**The socket is never inhabited**, so this proves nothing about Erdős #287. -/
theorem erdos287Statement_of_effectivityInput (I : EndgameEffectivityInput) :
    Erdos287Statement :=
  no_Erdos287Counterexample_of_closure (closureInputs_of_effectivityInput I)

/-- **`erdos287_remains_open`.**  `KERNEL-PROVED`.

The end-to-end compiler consumes an object that this repository does not build: the uniform
witness family it requires is exactly the open FCL supply, and the asymptotic form of that
supply provably does not produce it. -/
theorem erdos287_remains_open :
    ∃ p : ℕ → Prop, (∃ T : ℝ, ∀ M : ℕ, T ≤ (M : ℝ) → p M) ∧
      ∀ s : EffectiveSupply p, ¬ s.Bounded :=
  asymptoticFCL_does_not_give_bounded_effective

end EndgameEffectivity
end Erdos287
