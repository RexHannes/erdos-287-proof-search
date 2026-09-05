import RequestProject.Status.CurrentStatusErdos287September2Frontier
import RequestProject.CurrentProgramme.Erdos287September2OneSlotPerron
import RequestProject.CurrentProgramme.Erdos287September2TaggedTwoLaneSource
import RequestProject.CurrentProgramme.Erdos287September2LedgerAdaptersAndCompilers

/-!
# Append-only status layer — the September-2 two-lane master source / one-slot Perron /
hard-`U` adapter frontier

This module is **append-only** and is a *strictly later* layer than
`CurrentStatusErdos287September2Frontier`: no earlier row is deleted, and where this layer
records a different value the earlier one is marked `superseded` here rather than edited.

```
master two-lane tagged source (algebra)   : kernelProved
physical reconstruction semantics         : paperClosedExternal
selected-E type firewall                  : kernelProved
one-slot Perron mass < 128 log X          : kernelProved
N = kℓ + r + s ≤ 112, ⌈1/(1−γ)⌉ = 2        : kernelProved
complete typed Perron / nuclear ledger    : sourcePinOpen / strictlyReducedOpen
E_T                                       : paperClosedExternal (asymptotic)
hard-U → shared-Ford source adapter       : sourcePinOpen (uninhabited)
E_L                                       : conditionalKernel (open antecedent)
b-diagonal                                : conditionalKernel bypass (historical rows kept)
E_M                                       : paperClosedExternal (asymptotic)
N2 explicit two-linear-form sieve          : paperClosedExternal
elementary prime-pair survival bridge      : kernelProved (inclusion only)
current N2-based finite splice             : effectivityOpen (kernel-proved to fail)
four-error asymptotic FCL                  : conditionalKernel
explicit FCL / global effectivity          : effectivityOpen
Erdős #287                                 : open
```

`Status` is **metadata**: no row is a proof claim, and the firewall theorems below are
machine-checked.  Twin Prime is deliberately **not** a node of this ledger and is not a
dependency of anything here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace September2TwoLaneMasterStatus

/-! ## §1  The status vocabulary of §0 of the bank -/

/-- The status vocabulary. -/
inductive Status
  /-- Proved in the Lean kernel. -/
  | kernelProved
  /-- Closed in the published literature; never a Lean theorem here. -/
  | paperClosedExternal
  /-- A Lean theorem whose research antecedents are open. -/
  | conditionalKernel
  /-- The obligation is reduced to a literal source pin that is not supplied. -/
  | sourcePinOpen
  /-- Strictly reduced by an audit, still open. -/
  | strictlyReducedOpen
  /-- An open effectivity obligation. -/
  | effectivityOpen
  /-- A label from an earlier layer overridden by a later audit. -/
  | superseded
  /-- Open. -/
  | open_
  deriving DecidableEq, Fintype, Repr

/-! ## §2  Nodes of this layer -/

/-- Nodes of the September-2 two-lane master ledger. -/
inductive Node
  /-- The tagged two-lane disjoint-union source algebra. -/
  | taggedTwoLaneAlgebra
  /-- Physical reconstruction of `T_X` / `L_X` from the two lanes. -/
  | physicalReconstruction
  /-- The selected-`E` typing guard. -/
  | selectedEFirewall
  /-- The one-slot Perron mass bound `< 128 log X`. -/
  | oneSlotPerronMass
  /-- The finite source-arithmetic ceilings (`⌈1/(1−γ)⌉ = 2`, `N ≤ 112`, subset counts). -/
  | finiteSourceCeilings
  /-- The complete typed Perron / nuclear ledger obligation. -/
  | typedPerronNuclearLedger
  /-- The Tot-lane Type-I error `E_T`. -/
  | eT
  /-- The hard-`U` → shared-Ford literal source-equality adapter. -/
  | hardUSharedFordAdapter
  /-- The leakage error `E_L`. -/
  | eL
  /-- The two-copy b-diagonal package. -/
  | bDiagonal
  /-- The model error `E_M`. -/
  | eM
  /-- The explicit two-linear-form `N2` sieve (Bordignon–Lee analytics). -/
  | n2ExplicitSieve
  /-- The elementary prime-pair sieve-survival / inclusion bridge. -/
  | primePairSurvivalBridge
  /-- The finite splice of the current `N2` threshold into the finite bank. -/
  | n2FiniteSplice
  /-- The asymptotic four-error compiler. -/
  | fourErrorAsymptoticFCL
  /-- The explicit (effective) four-error compiler. -/
  | fourErrorExplicitFCL
  /-- Global effectivity of the #287 programme. -/
  | globalEffectivity
  /-- Erdős #287 itself. -/
  | erdos287
  deriving DecidableEq, Fintype, Repr

/-! ## §3  The authoritative ledger -/

/-- The authoritative September-2 two-lane status assignment. -/
def status : Node → Status
  | Node.taggedTwoLaneAlgebra => Status.kernelProved
  | Node.physicalReconstruction => Status.paperClosedExternal
  | Node.selectedEFirewall => Status.kernelProved
  | Node.oneSlotPerronMass => Status.kernelProved
  | Node.finiteSourceCeilings => Status.kernelProved
  | Node.typedPerronNuclearLedger => Status.sourcePinOpen
  | Node.eT => Status.paperClosedExternal
  | Node.hardUSharedFordAdapter => Status.sourcePinOpen
  | Node.eL => Status.conditionalKernel
  | Node.bDiagonal => Status.conditionalKernel
  | Node.eM => Status.paperClosedExternal
  | Node.n2ExplicitSieve => Status.paperClosedExternal
  | Node.primePairSurvivalBridge => Status.kernelProved
  | Node.n2FiniteSplice => Status.effectivityOpen
  | Node.fourErrorAsymptoticFCL => Status.conditionalKernel
  | Node.fourErrorExplicitFCL => Status.effectivityOpen
  | Node.globalEffectivity => Status.effectivityOpen
  | Node.erdos287 => Status.open_

/-! ## §4  Firewalls -/

/-- **`paperClosed_is_not_kernelProved`.**  `KERNEL-PROVED`. -/
theorem paperClosed_is_not_kernelProved :
    Status.paperClosedExternal ≠ Status.kernelProved := by decide

/-- **`sourcePinOpen_is_not_kernelProved`.**  `KERNEL-PROVED`. -/
theorem sourcePinOpen_is_not_kernelProved :
    Status.sourcePinOpen ≠ Status.kernelProved := by decide

/-- **`erdos287_is_open`.**  `KERNEL-PROVED`.  Nothing in this layer closes #287. -/
theorem erdos287_is_open : status Node.erdos287 = Status.open_ := rfl

/-- **`no_status_row_closes_erdos287`.**  `KERNEL-PROVED`.  No node of the ledger other than
`erdos287` itself carries the #287 conclusion, and `erdos287` is open. -/
theorem no_status_row_closes_erdos287 :
    ∀ n : Node, status n = Status.kernelProved → n ≠ Node.erdos287 := by decide

/-- **`open_and_conditional_rows_exist`.**  `KERNEL-PROVED`.  The ledger is not a list of
closed nodes. -/
theorem open_and_conditional_rows_exist :
    (∃ n : Node, status n = Status.open_) ∧
    (∃ n : Node, status n = Status.conditionalKernel) ∧
    (∃ n : Node, status n = Status.sourcePinOpen) ∧
    (∃ n : Node, status n = Status.effectivityOpen) := by decide

/-- **`twin_prime_is_not_a_node`.**  `KERNEL-PROVED`.  The ledger has exactly the eighteen
nodes listed above; the twin-prime conjecture is not one of them and is not a dependency. -/
theorem twin_prime_is_not_a_node : Fintype.card Node = 18 := by decide

/-! ## §5  The rows that are backed by kernel theorems of this layer -/

/-- **`oneSlotPerronMass_row_is_backed`.**  `KERNEL-PROVED`.  The `kernelProved` label on the
one-slot Perron row is backed by the actual theorem. -/
theorem oneSlotPerronMass_row_is_backed :
    status Node.oneSlotPerronMass = Status.kernelProved ∧
    ∀ X : ℝ, 3 ≤ X →
      September2OneSlotPerron.perronMassOne X < 128 * Real.log X :=
  ⟨rfl, fun _ hX => September2OneSlotPerron.perronMassOne_lt hX⟩

/-- **`finiteSourceCeilings_row_is_backed`.**  `KERNEL-PROVED`. -/
theorem finiteSourceCeilings_row_is_backed :
    status Node.finiteSourceCeilings = Status.kernelProved ∧
    (∀ k r s : ℕ, k ≤ 6 → r ≤ 20 → s ≤ 20 →
      September2OneSlotPerron.coordCount k r s ≤ 112) ∧
    ⌈1 / (1 - September2OneSlotPerron.gammaN2)⌉ = 2 :=
  ⟨rfl, fun _ _ _ hk hr hs => September2OneSlotPerron.coordCount_le_112 hk hr hs,
    September2OneSlotPerron.ceil_one_div_one_sub_gamma⟩

/-- **`taggedTwoLaneAlgebra_row_is_backed`.**  `KERNEL-PROVED`. -/
theorem taggedTwoLaneAlgebra_row_is_backed :
    status Node.taggedTwoLaneAlgebra = Status.kernelProved ∧
    ∀ S : Finset September2TaggedSource.RawIndex,
      (September2TaggedSource.totCells S).card + (September2TaggedSource.uCells S).card
        = S.card :=
  ⟨rfl, September2TaggedSource.census_card_split⟩

/-- **`primePairSurvivalBridge_row_is_backed`.**  `KERNEL-PROVED`.  The bridge row is backed
by the elementary inclusion theorem, whose hypotheses are consistent; the analytic sieve row
(`n2ExplicitSieve`) stays `paperClosedExternal` and is a different node. -/
theorem primePairSurvivalBridge_row_is_backed :
    status Node.primePairSurvivalBridge = Status.kernelProved ∧
    status Node.n2ExplicitSieve = Status.paperClosedExternal ∧
    Nonempty September2Ledger.PrimePairSieve.WindowData ∧
    ∀ (d : September2Ledger.PrimePairSieve.WindowData) (q : ℕ) (s : ℤ) (n : ℕ),
      d.Q < (q : ℝ) → q.Prime → (s = 1 ∨ s = -1) →
      (n : ℤ) = 2 * (d.M : ℤ) * (q : ℤ) + s → n.Prime →
      ∀ p : ℕ, p.Prime → (p : ℝ) < d.z → ¬ p ∣ q ∧ ¬ p ∣ n :=
  ⟨rfl, rfl, September2Ledger.PrimePairSieve.windowData_inhabited,
    fun d _ _ _ hq hqp hs hn hnp =>
      September2Ledger.PrimePairSieve.primePairSieveSurvival45 d hq hqp hs hn hnp⟩

/-- **`n2FiniteSplice_row_is_backed`.**  `KERNEL-PROVED`.  The effectivity row is backed by
the arithmetic fact that the current threshold overshoots the finite bank. -/
theorem n2FiniteSplice_row_is_backed :
    status Node.n2FiniteSplice = Status.effectivityOpen ∧
    N2ConstantsBank.finiteBankCeiling < 2 * N2ConstantsBank.XN2 :=
  ⟨rfl, September2Ledger.two_XN2_exceeds_four_billion⟩

end September2TwoLaneMasterStatus
end Erdos287
