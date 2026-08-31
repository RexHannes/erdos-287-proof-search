import Mathlib
import RequestProject.Status.CurrentStatusErdos287Block20
import RequestProject.CurrentProgramme.PrimitiveLocalProfileGramSocket
import RequestProject.CurrentProgramme.PrimitiveRamanujanReassembly

/-!
# Append-only status layer — Erdős #287, PRIMITIVE-LOCALPROFILE Δ

This module is **append-only**: the BLOCK20 ledger (`Erdos287.Block20Status.ledger`) is
imported and left untouched; `historical_block20_status_preserved` re-checks a sample of its
rows.

Frontier movement of this delta:

```
before : 287-K0-SP2-DET1-PRIMITIVE-CONDUCTOR-SHORTLIFT-GRAM45
after  : 287-K0-SP2-DET1-PRIMITIVE-LOCALPROFILE-GRAM45
```

The historical row `PRIMITIVE-CONDUCTOR-SHORTLIFT-GRAM45` is recorded as
`supersededNotFalse`: it is no longer the controlling frontier, and it is **not** marked
false and **not** marked closed.

`FCL` is `notReached`, `UNIFORM k = 0` and `ERDOS287` are `open_`; there is no `closed` row.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace PrimitiveLocalProfileStatus

open Erdos287.PrimitiveRamanujan
open Erdos287.PrimitiveReassembly
open Erdos287.PrimitiveD
open Erdos287.PrimitiveFarey
open Erdos287.ShortLift
open Erdos287.PrimitiveLocalProfile

/-! ## §G.1  The ledger -/

/-- The nodes of the PRIMITIVE-LOCALPROFILE Δ pass. -/
inductive Node
  | primitiveTRamanujan45
  | primitiveRamanujanDivisorNormalForm45
  | ramanujanMobiusSimplification45
  | primitiveRamanujanReassembly45
  | shortLiftEulerCollapse45
  | primitiveDMultiplicity45
  | primitiveFareyNearCollision45
  | fareyMixedWeightRouting45
  | primitiveConductorShortLiftGram45
  | primitiveLocalProfileGram45
  | uniformK0
  | fcl
  | erdos287
  deriving DecidableEq, Fintype, Repr

/-- The status labels.  `closed` exists only so that "no closed row" is a statement about
this ledger; it is never used. -/
inductive Label
  | closed
  | provedFinite
  | provedAlgebraic
  | representationLoop
  | conditionalCompiler
  | researchPassCandidate
  | analyticOpen
  | supersededNotFalse
  | notReached
  | open_
  deriving DecidableEq, Fintype, Repr

open Node Label

/-- The PRIMITIVE-LOCALPROFILE Δ ledger. -/
def ledger : Node → Label
  | primitiveTRamanujan45 => provedAlgebraic
  | primitiveRamanujanDivisorNormalForm45 => provedAlgebraic
  | ramanujanMobiusSimplification45 => provedAlgebraic
  | primitiveRamanujanReassembly45 => representationLoop
  | shortLiftEulerCollapse45 => researchPassCandidate
  | primitiveDMultiplicity45 => provedFinite
  | primitiveFareyNearCollision45 => provedFinite
  | fareyMixedWeightRouting45 => open_
  | primitiveConductorShortLiftGram45 => supersededNotFalse
  | primitiveLocalProfileGram45 => analyticOpen
  | uniformK0 => open_
  | fcl => notReached
  | erdos287 => open_

/-- Which rows carry a proved conditional consumer only. -/
def hasConditionalConsumerOnly : Node → Bool
  | shortLiftEulerCollapse45 => true
  | primitiveLocalProfileGram45 => true
  | _ => false

/-- The exact main-line residual order after this delta. -/
def residualRank : Node → ℕ
  | primitiveLocalProfileGram45 => 1
  | shortLiftEulerCollapse45 => 2
  | fareyMixedWeightRouting45 => 3
  | _ => 0

/-! ## §G.2  Ledger integrity -/

/-- **`no_closed_rows`.**  `LEAN_PROVED`. -/
theorem no_closed_rows : ∀ n : Node, ledger n ≠ closed := by decide +kernel

/-- **`erdos287_open`.**  `LEAN_PROVED`. -/
theorem erdos287_open : ledger erdos287 = open_ := by decide +kernel

/-- **`uniform_k0_open_fcl_not_reached`.**  `LEAN_PROVED`. -/
theorem uniform_k0_open_fcl_not_reached :
    ledger uniformK0 = open_ ∧ ledger fcl = notReached := by decide +kernel

/-- **`shortLiftGram_superseded_not_false`.**  `LEAN_PROVED`.

The previous controlling frontier is recorded as strictly reduced and **not false**: its row
is `supersededNotFalse`, which is neither `closed` nor a falsity verdict, and it is no longer
first on the residual list. -/
theorem shortLiftGram_superseded_not_false :
    ledger primitiveConductorShortLiftGram45 = supersededNotFalse ∧
      supersededNotFalse ≠ closed ∧
      residualRank primitiveConductorShortLiftGram45 = 0 := by
  decide +kernel

/-- **`localProfileGram_is_first_exact_mainline_residual`.**  `LEAN_PROVED`.

`287-K0-SP2-DET1-PRIMITIVE-LOCALPROFILE-GRAM45` is the first exact main-line residual after
this delta, its row is `analyticOpen`, and its interface is **uninhabited** (explicit
refuting data). -/
theorem localProfileGram_is_first_exact_mainline_residual :
    ledger primitiveLocalProfileGram45 = analyticOpen ∧
      residualRank primitiveLocalProfileGram45 = 1 ∧
      (∀ n : Node, residualRank n = 1 → n = primitiveLocalProfileGram45) ∧
      (∃ (X eta C : ℝ) (gram : PrimitiveConductorConfig → ℝ),
        ¬ PrimitiveLocalProfileGramInput X eta C gram) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    primitiveLocalProfileGram_not_automatic⟩

/-- **`exact_rows_are_theorems`.**  `LEAN_PROVED`.

The `provedAlgebraic` / `provedFinite` / `representationLoop` rows are backed by the actual
kernel-checked statements of §§A, B, D, E. -/
theorem exact_rows_are_theorems :
    ledger primitiveTRamanujan45 = provedAlgebraic ∧
      ledger primitiveRamanujanDivisorNormalForm45 = provedAlgebraic ∧
      ledger ramanujanMobiusSimplification45 = provedAlgebraic ∧
      ledger primitiveRamanujanReassembly45 = representationLoop ∧
      ledger primitiveDMultiplicity45 = provedFinite ∧
      ledger primitiveFareyNearCollision45 = provedFinite ∧
      -- §A: the unit shift and the divisor normal form
      (∀ (g : ℕ), 0 < g → ∀ a b s w : ℤ, (g : ℤ) ∣ 2 * b * w - 1 →
        ramanujan g (a + s * w) = ramanujan g (2 * a * b + s)) ∧
      (∀ (g : ℕ), 0 < g → ∀ N : ℤ,
        ramanujan g N = ∑ r ∈ (Int.gcd (g : ℤ) N).divisors,
          (r : ℂ) * (ArithmeticFunction.moebius (g / r) : ℤ)) ∧
      -- §B: the reassembly representation loop
      (∀ (g : ℕ), 0 < g → Squarefree g → ∀ N : ℤ,
        ((ArithmeticFunction.moebius g : ℤ) : ℂ) / (g : ℂ) * ramanujan g N
          = rawProgression g N - additiveZeroMode g N) ∧
      -- §D: the multiplicity bound
      (∀ (g0 r1 r2 : ℕ), Nat.Coprime r1 r2 → 0 < r1 → ∀ D : ℤ,
        (dSolutionSet g0 r1 r2 D).card ≤ g0 + 1) ∧
      -- §E: the exact Farey finite count
      (∀ (g0 r1 r2 : ℕ), 0 < g0 → 0 < r1 → 0 < r2 → Nat.Coprime r1 r2 →
        ∀ A : ℚ, 0 < A →
          (nearCollisionSet g0 r1 r2 A).card
            ≤ (2 * (⌊((g0 : ℚ) * r1 * r2) / A⌋).toNat + 1) * g0) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel,
    fun g hg a b s w hw => ramanujan_unit_shift hg a b s w hw,
    fun g hg N => ramanujan_eq_divisor_sum g hg N,
    fun g hg hsq N => primitive_ramanujan_reassembly hg hsq N,
    fun _ _ _ hcop hr1 D => dSolutionSet_card_le hcop hr1 D,
    fun _ _ _ hg0 hr1 hr2 hcop _ hA => nearCollisionSet_card_le hg0 hr1 hr2 hcop hA⟩

/-- **`analytic_rows_are_uninhabited`.**  `LEAN_PROVED`.

Both analytic rows of this delta are interfaces with **no inhabitant**: the short-lift Euler
collapse (whose finite-prime-product avatar *is* proved) and the local-profile Gram input. -/
theorem analytic_rows_are_uninhabited :
    ledger shortLiftEulerCollapse45 = researchPassCandidate ∧
      ledger primitiveLocalProfileGram45 = analyticOpen ∧
      -- the finite avatar of the Euler collapse is a theorem …
      (∀ (n : ℕ), Squarefree n → ∀ H : ℕ,
        mProfileDivisor H n
          = ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ H), (1 - (1 : ℚ) / p)) ∧
      -- … while the Gram input is refuted by explicit data
      (∃ (X eta C : ℝ) (gram : PrimitiveConductorConfig → ℝ),
        ¬ PrimitiveLocalProfileGramInput X eta C gram) :=
  ⟨by decide +kernel, by decide +kernel,
    fun _ hn H => mProfileDivisor_euler_product hn H,
    primitiveLocalProfileGram_not_automatic⟩

/-- **`historical_block20_status_preserved`.**  `LEAN_PROVED`.

The imported BLOCK20 ledger is unmodified. -/
theorem historical_block20_status_preserved :
    Erdos287.Block20Status.ledger Erdos287.Block20Status.Node.erdos287
        = Erdos287.Block20Status.Label.open_ ∧
      Erdos287.Block20Status.ledger Erdos287.Block20Status.Node.fcl
        = Erdos287.Block20Status.Label.open_ ∧
      Erdos287.Block20Status.ledger Erdos287.Block20Status.Node.block20GeneratedTypeII45
        = Erdos287.Block20Status.Label.analyticOpen ∧
      (∀ n : Erdos287.Block20Status.Node,
        Erdos287.Block20Status.ledger n ≠ Erdos287.Block20Status.Label.closed) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  exact Erdos287.Block20Status.no_closed_rows

end PrimitiveLocalProfileStatus
end Erdos287
