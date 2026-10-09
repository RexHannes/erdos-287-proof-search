import Mathlib
import RequestProject.Erdos287.CompensationLoop

/-!
# Erdős #287 effectivity — the bounded-conductor frontier object (§60)

```
BOUNDED-CONDUCTOR KERNEL (1000 < ell ≤ 5000) : KERNEL-PROVED DEFINITION
BoundedConductorK1Target                      : OPEN  (never inhabited)
FixedConductorCharacterBound                  : OPEN INTERFACE (never inhabited)
CHARACTER BOUND ⇒ k = 1 OWNER BOUND           : KERNEL-PROVED (conditional)
POSITIVE FINITE-KERNEL WRAPPER                : RETIRED_NONCLOSING
```

The current `k = 1` frontier is the **bounded-conductor signed outer-`z` estimate** for the
returned finite-conductor kernel `returnedKernel` of `CompensationLoop` (support
`1000 < ℓ ≤ 5000`).

`BoundedConductorK1Target b` is the OPEN analytic goal "the bounded-conductor kernel is
bounded by `b` uniformly in the physical window".  It is **not inhabited anywhere in this
bank**, and `boundedConductor_target_has_content` records that the underlying kernel is not
the zero object, so the goal is not vacuous.

`FixedConductorCharacterBound b` is the next analytic target: control of the **signed
outer-`z` sum** after a finite DFT/character expansion of the bounded-conductor kernel.  It
is likewise not inhabited; `character_bound_implies_k1_owner_bound` is the exact conditional
reduction at the source level.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §60.1  The OPEN bounded-conductor target -/

/-- **OPEN.**  The bounded-conductor `k = 1` target: a uniform bound `b` for the returned
finite-conductor kernel on `1000 < ℓ ≤ 5000`.  This proposition is *never inhabited* in this
bank. -/
def BoundedConductorK1Target (b : ℚ) : Prop :=
  ∀ A B z : ℤ, |returnedKernel A B z| ≤ b

/-- **`boundedConductorTarget_mono`.**  `KERNEL-PROVED`.  The target is monotone in the
budget. -/
theorem boundedConductorTarget_mono {b b' : ℚ} (h : b ≤ b') (hb : BoundedConductorK1Target b) :
    BoundedConductorK1Target b' :=
  fun A B z => le_trans (hb A B z) h

/-- **`boundedConductor_target_has_content`.**  `KERNEL-PROVED`.  The target is not vacuous:
the bounded-conductor kernel is built from atoms that do not all vanish. -/
theorem boundedConductor_target_has_content :
    ∃ ell ∈ Finset.Icc 1001 5000, ∃ s z : ℤ, Kell ell s z ≠ 0 :=
  returnedKernel_not_identically_zero

/-! ## §60.2  The new research interface -/

/-- **OPEN interface.**  `FixedConductorCharacterBound b`: after a finite DFT/character
expansion of the bounded-conductor kernel for `1000 < ℓ ≤ 5000`, the *signed outer-`z` sum*
against any bounded coefficient sequence is controlled by `b`.  Not inhabited. -/
def FixedConductorCharacterBound (b : ℚ) : Prop :=
  ∀ (A B : ℤ) (Zset : Finset ℤ) (w : ℤ → ℚ), (∀ z, |w z| ≤ 1) →
    |∑ z ∈ Zset, w z * returnedKernel A B z| ≤ b

/-- **`character_bound_implies_k1_owner_bound`.**  `KERNEL-PROVED` (conditional).  The signed
outer-`z` character bound implies the corresponding `k = 1` owner bound at the exact source
level: specialise to a single `z` with unit weight. -/
theorem character_bound_implies_k1_owner_bound {b : ℚ}
    (h : FixedConductorCharacterBound b) : BoundedConductorK1Target b := by
  intro A B z
  have hone : ∀ y : ℤ, |(1 : ℚ)| ≤ 1 := fun _ => by norm_num
  have := h A B {z} (fun _ => (1 : ℚ)) hone
  simpa using this

/-! ## §60.3  Retired wrapper -/

/-- Evidence tags used by this module. -/
inductive FrontierStatus
  | kernelProved
  | openGoal
  | retiredNonclosing
  deriving DecidableEq, Repr

/-- The positive finite-kernel wrapper is retired: bounding the *absolute values* of the
returned atoms cannot close the signed problem, since the signed cancellation is exactly what
the frontier estimate has to exploit. -/
def positiveFiniteKernelWrapper : FrontierStatus := .retiredNonclosing

/-- The current `k = 1` frontier. -/
def currentK1Frontier : FrontierStatus := .openGoal

/-- **`frontier_status_record`.**  `KERNEL-PROVED` (bookkeeping).  The recorded statuses of
the bounded-conductor frontier. -/
theorem frontier_status_record :
    positiveFiniteKernelWrapper = FrontierStatus.retiredNonclosing ∧
      currentK1Frontier = FrontierStatus.openGoal ∧
      currentK1Frontier ≠ FrontierStatus.kernelProved :=
  ⟨rfl, rfl, by decide⟩

end Effectivity
end Erdos287
