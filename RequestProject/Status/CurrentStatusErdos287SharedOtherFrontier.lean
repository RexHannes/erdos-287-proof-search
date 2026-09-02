import RequestProject.Status.CurrentStatusErdos287TwoLaneFCLFrontier
import RequestProject.CurrentProgramme.Erdos287SharedOtherAdaptersAndCompiler

/-!
# Append-only status layer — the 287A / shared-other45 frontier

This module is **append-only** and sits *strictly later* than every existing 287 status
layer.  No earlier row is rewritten.

```
E_T  (Type-I estimate)                        : paperClosedExternal
E_2  (N2 λ-collar)                            : paperClosedExternal
E_M / Bsrc / N1 comparison                    : paperClosedExternal
hard U, k ≥ 1 (Ford 7.22 other parent)        : openExternal
E_L                                           : conditionalKernel
asymptotic FCL                                : conditionalKernel
effectivity                                   : effectivityOpen
Erdős #287                                    : openExternal
dependent raw packet / Tot exclusion firewall : kernelProved
determinant line, centred two-copy, coeffs    : kernelProved
Δ-router (routing only)                       : kernelProved
two independent adapters                      : kernelProved
```

`SharedOtherStatus` is **metadata**.  In particular `paperClosedExternal ≠ kernelProved`:
an external analytic statement is *never* called kernel-proved merely because its interface
is represented in Lean.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace SharedOtherFrontierStatus

/-! ## §1  The status vocabulary of this layer -/

/-- The status vocabulary of the 287A / shared-other45 frontier. -/
inductive SharedOtherStatus
  /-- Proved in the Lean kernel. -/
  | kernelProved
  /-- A Lean theorem all of whose research antecedents remain uninhabited. -/
  | conditionalKernel
  /-- Closed in the published literature; **never** a Lean theorem here. -/
  | paperClosedExternal
  /-- An open external obligation. -/
  | openExternal
  /-- An open effectivity obligation. -/
  | effectivityOpen
  deriving DecidableEq, Fintype, Repr

open SharedOtherStatus

/-! ## §2  Nodes -/

/-- Nodes of the 287A / shared-other45 ledger. -/
inductive SharedOtherNode
  /-- The dependent raw packet type and the `Tot` exclusion firewall. -/
  | dependentRawPacket
  /-- The deterministic selected `E*` and the generated coefficients `A_η`, `B_η`. -/
  | generatedCoefficients
  /-- The determinant-line transformation. -/
  | determinantLine
  /-- The centred two-copy identity and exact coefficient preservation. -/
  | centredTwoCopy
  /-- The proof-local conductor / shared-gcd data. -/
  | sharedConductorData
  /-- The Δ-router. -/
  | deltaRouter
  /-- The `E_T` Type-I estimate. -/
  | E_T_typeI
  /-- The `E_2` λ-collar. -/
  | E_2_collar
  /-- The `E_M` / `Bsrc` / `N1` comparison. -/
  | E_M_comparison
  /-- The hard `U`, `k ≥ 1` Ford-7.22 other-parent covariance. -/
  | hardU
  /-- The `E_L` compiler. -/
  | E_L_compiler
  /-- The two independent adapters. -/
  | twoAdapters
  /-- The asymptotic FCL. -/
  | asymptoticFCL
  /-- The effectivity socket. -/
  | effectivity
  /-- Erdős #287 itself. -/
  | erdos287
  deriving DecidableEq, Fintype, Repr

open SharedOtherNode

/-! ## §3  The ledger -/

/-- The authoritative status of each node of this layer. -/
def sharedOtherLedger : SharedOtherNode → SharedOtherStatus
  | dependentRawPacket => kernelProved
  | generatedCoefficients => kernelProved
  | determinantLine => kernelProved
  | centredTwoCopy => kernelProved
  | sharedConductorData => kernelProved
  | deltaRouter => kernelProved
  | E_T_typeI => paperClosedExternal
  | E_2_collar => paperClosedExternal
  | E_M_comparison => paperClosedExternal
  | hardU => openExternal
  | E_L_compiler => conditionalKernel
  | twoAdapters => kernelProved
  | asymptoticFCL => conditionalKernel
  | effectivity => effectivityOpen
  | erdos287 => openExternal

/-! ## §4  Precedence -/

/-- The status layers of this development, in order. -/
inductive SharedOtherStatusLayer
  /-- The full analytic-kernel import frontier. -/
  | fullAnalyticKernelImportFrontier
  /-- The fixed-certificate endgame frontier. -/
  | fixedCertificateEndgameFrontier
  /-- The two-lane FCL frontier. -/
  | twoLaneFCLFrontier
  /-- This layer. -/
  | sharedOtherFrontier
  deriving DecidableEq, Repr

/-- Layer index: larger means later. -/
def SharedOtherStatusLayer.index : SharedOtherStatusLayer → ℕ
  | .fullAnalyticKernelImportFrontier => 2
  | .fixedCertificateEndgameFrontier => 3
  | .twoLaneFCLFrontier => 4
  | .sharedOtherFrontier => 5

/-- **`sharedOtherFrontier_is_later`.**  `LEAN_PROVED`. -/
theorem sharedOtherFrontier_is_later :
    SharedOtherStatusLayer.twoLaneFCLFrontier.index
        < SharedOtherStatusLayer.sharedOtherFrontier.index ∧
    SharedOtherStatusLayer.fixedCertificateEndgameFrontier.index
        < SharedOtherStatusLayer.sharedOtherFrontier.index ∧
    SharedOtherStatusLayer.fullAnalyticKernelImportFrontier.index
        < SharedOtherStatusLayer.sharedOtherFrontier.index := by decide

/-- **`earlier_twoLane_ledger_retained_unchanged`.**  `LEAN_PROVED`.

The previous ledger is re-checked, not rewritten. -/
theorem earlier_twoLane_ledger_retained_unchanged :
    Erdos287.TwoLaneFCLFrontierStatus.twoLaneLedger
        Erdos287.TwoLaneFCLFrontierStatus.TwoLaneNode.twoLaneRawSource
      = Erdos287.TwoLaneFCLFrontierStatus.TwoLaneStatus.kernelProved ∧
    Erdos287.TwoLaneFCLFrontierStatus.twoLaneLedger
        Erdos287.TwoLaneFCLFrontierStatus.TwoLaneNode.erdos287
      = Erdos287.TwoLaneFCLFrontierStatus.TwoLaneStatus.sourceOpen := by decide

/-! ## §5  The kernel-proved rows -/

/-- **`dependentRawPacket_row_is_kernel_proved`.**  `LEAN_PROVED`.

`RawPacket X = RawData Tot X ⊕ RawData U X`, the lanes are disjoint, and the `Tot`
constructor excludes every forbidden field. -/
theorem dependentRawPacket_row_is_kernel_proved :
    sharedOtherLedger dependentRawPacket = kernelProved ∧
    (∀ f ∈ Erdos287.SharedOtherRaw.forbiddenTotFieldNames,
      f ∉ Erdos287.SharedOtherRaw.totFieldNames) ∧
    (∀ (X : ℕ) (t : Erdos287.SharedOtherRaw.RawDataTot X)
      (q : Erdos287.SharedOtherRaw.RawDataU X),
        Erdos287.SharedOtherRaw.RawPacket.tot t ≠ Erdos287.SharedOtherRaw.RawPacket.u q) :=
  ⟨rfl, Erdos287.SharedOtherRaw.tot_constructor_excludes_forbidden_fields,
    fun _ t q => Erdos287.SharedOtherRaw.rawPacket_lanes_are_disjoint t q⟩

/-- **`generatedCoefficients_row_is_kernel_proved`.**  `LEAN_PROVED`.

`E*` is a deterministic function of `𝓔`, and `A_η`, `B_η` are generated by it. -/
theorem generatedCoefficients_row_is_kernel_proved :
    sharedOtherLedger generatedCoefficients = kernelProved ∧
    (∀ (X : ℕ) (p q : Erdos287.SharedOtherRaw.RawDataU X),
      p.mathcalE = q.mathcalE → p.EStar = q.EStar) :=
  ⟨rfl, fun _ p q h => Erdos287.SharedOtherRaw.EStar_is_deterministic p q h⟩

/-- **`determinantLine_row_is_kernel_proved`.**  `LEAN_PROVED`. -/
theorem determinantLine_row_is_kernel_proved :
    sharedOtherLedger determinantLine = kernelProved ∧
    ∀ r a b₀ q₀ ell : ℤ,
      r * (q₀ + 2 * a * ell) - 2 * a * (b₀ + r * ell) = r * q₀ - 2 * a * b₀ :=
  ⟨rfl, Erdos287.SharedOtherRaw.determinant_line_invariant⟩

/-- **`centredTwoCopy_row_is_kernel_proved`.**  `LEAN_PROVED`. -/
theorem centredTwoCopy_row_is_kernel_proved :
    sharedOtherLedger centredTwoCopy = kernelProved ∧
    ∀ P M : ℂ, (P - M) * (starRingEnd ℂ) (P - M)
      = P * (starRingEnd ℂ) P - P * (starRingEnd ℂ) M - M * (starRingEnd ℂ) P
        + M * (starRingEnd ℂ) M :=
  ⟨rfl, Erdos287.SharedOtherRaw.centred_two_copy_identity⟩

/-- **`deltaRouter_row_is_kernel_proved`.**  `LEAN_PROVED`.  The router is total and
exact. -/
theorem deltaRouter_row_is_kernel_proved :
    sharedOtherLedger deltaRouter = kernelProved ∧
    ∀ D b₁ b₂ : ℤ,
      (Erdos287.SharedOtherParent.deltaRoute D b₁ b₂
          = Erdos287.SharedOtherParent.OtherOwner.c0 ↔ D = 0) ∧
      (Erdos287.SharedOtherParent.deltaRoute D b₁ b₂
          = Erdos287.SharedOtherParent.OtherOwner.transverse ↔ D ≠ 0 ∧ b₁ ≠ b₂) ∧
      (Erdos287.SharedOtherParent.deltaRoute D b₁ b₂
          = Erdos287.SharedOtherParent.OtherOwner.bDiagonal ↔ D ≠ 0 ∧ b₁ = b₂) :=
  ⟨rfl, fun D b₁ b₂ =>
    ⟨Erdos287.SharedOtherParent.deltaRoute_c0_iff D b₁ b₂,
     Erdos287.SharedOtherParent.deltaRoute_transverse_iff D b₁ b₂,
     Erdos287.SharedOtherParent.deltaRoute_bDiagonal_iff D b₁ b₂⟩⟩

/-- **`sharedConductorData_row_is_kernel_proved`.**  `LEAN_PROVED`.

The reduced factors of the shared gcd are coprime. -/
theorem sharedConductorData_row_is_kernel_proved :
    sharedOtherLedger sharedConductorData = kernelProved ∧
    ∀ (X : ℕ) (p₁ p₂ : Erdos287.SharedOtherRaw.RawDataU X)
      (D : Erdos287.SharedOtherParent.SharedConductorData p₁ p₂), Nat.Coprime D.n₁ D.n₂ :=
  ⟨rfl, fun _ _ _ D => D.reduced_factors_coprime⟩

/-- **`twoAdapters_row_is_kernel_proved`.**  `LEAN_PROVED`.

The #287 adapter is discharged from the shared input alone, uniformly in the other
project's downstream conclusion. -/
theorem twoAdapters_row_is_kernel_proved :
    sharedOtherLedger twoAdapters = kernelProved ∧
    ∀ (d : Erdos287.PhysicalSupport.PhysicalSupportData)
      (w : Erdos287.PhysicalSupport.PhysicalWeightData) (X : ℕ)
      (p : Erdos287.SharedOtherRaw.RawDataU X) (eta : ℕ → ℝ) (chi : ℕ → ℤ → ℝ)
      (S T : Finset ℕ) (kernel : ℕ → ℕ → ℤ → ℝ) (tau : ℤ) (bound : ℝ),
      Erdos287.SharedOtherCompiler.Erdos287HardUAdapter d w p eta chi S T kernel tau bound :=
  ⟨rfl, fun d w _ p eta chi S T kernel tau bound =>
    Erdos287.SharedOtherCompiler.erdos287HardUAdapter_holds d w p eta chi S T kernel tau
      bound⟩

/-! ## §6  The conditional and open rows -/

/-- **`E_L_row_is_conditional`.**  `LEAN_PROVED`.

The leakage bound is a Lean theorem whose antecedent, the shared other-parent input, is
refutable at explicit data. -/
theorem E_L_row_is_conditional :
    sharedOtherLedger E_L_compiler = conditionalKernel ∧
    (∀ (d : Erdos287.PhysicalSupport.PhysicalSupportData)
      (w : Erdos287.PhysicalSupport.PhysicalWeightData) (X : ℕ)
      (p : Erdos287.SharedOtherRaw.RawDataU X) (eta : ℕ → ℝ) (chi : ℕ → ℤ → ℝ)
      (S T : Finset ℕ) (kernel : ℕ → ℕ → ℤ → ℝ) (tau : ℤ) (bound : ℝ),
      Erdos287.SharedOtherCompiler.SharedOtherParentInput d w p eta chi S T kernel tau
          bound →
        Erdos287.PhysicalSupport.E_L_exact d w ≤ bound) ∧
    ∀ (d : Erdos287.PhysicalSupport.PhysicalSupportData)
      (w : Erdos287.PhysicalSupport.PhysicalWeightData),
      IsEmpty (Erdos287.SharedOtherCompiler.SharedOtherParentInput d w
        Erdos287.SharedOtherParent.sampleU (fun _ => 1) (fun _ _ => 1) ∅ ∅
        (fun _ _ _ => 1) 0 (-1)) :=
  ⟨rfl, fun _ _ _ _ _ _ _ _ _ _ _ I =>
      Erdos287.SharedOtherCompiler.E_L_bound_of_sharedOtherParent I,
    Erdos287.SharedOtherCompiler.sharedOtherParentInput_is_a_genuine_constraint⟩

/-- **`E_T_row_is_paper_closed_external`.**  `LEAN_PROVED`.

The Type-I estimate is *not* kernel-proved here.  Its `o(X/log X)` conclusion is a genuine
constraint: the identity function fails it. -/
theorem E_T_row_is_paper_closed_external :
    sharedOtherLedger E_T_typeI = paperClosedExternal ∧
    ¬ Erdos287.SharedOtherCompiler.IsLittleOXOverLogX (fun X : ℝ => X) :=
  ⟨rfl, Erdos287.SharedOtherCompiler.littleO_is_a_genuine_constraint⟩

/-- **`hardU_row_is_open_external`.**  `LEAN_PROVED`.

The `k ≥ 1` Ford-7.22 other-parent covariance socket is open, uninhabited and refutable at
explicit data, and it is not satisfiable by a `k = 0` leaf. -/
theorem hardU_row_is_open_external :
    sharedOtherLedger hardU = openExternal ∧
    IsEmpty (Erdos287.SharedOtherParent.Ford722OtherParentGeneratedUniformityInput
      Erdos287.SharedOtherParent.sampleU (fun _ => 1) (fun _ _ => 1) ∅ ∅
      (fun _ _ _ => 1) 0 (-1)) ∧
    Erdos287.SharedOtherParent.betaGProfile Erdos287.SharedOtherParent.sampleU
      = Erdos287.SharedOtherParent.betaGProfile Erdos287.SharedOtherParent.sampleU' ∧
    Erdos287.SharedOtherRaw.A_eta Erdos287.SharedOtherParent.sampleU (fun _ => 1)
        (fun _ _ => 1) 1 0
      ≠ Erdos287.SharedOtherRaw.A_eta Erdos287.SharedOtherParent.sampleU' (fun _ => 1)
        (fun _ _ => 1) 1 0 :=
  ⟨rfl, Erdos287.SharedOtherParent.ford722_socket_is_a_genuine_constraint,
    Erdos287.SharedOtherParent.betaG_profile_does_not_determine_the_generated_coefficients.1,
    Erdos287.SharedOtherParent.betaG_profile_does_not_determine_the_generated_coefficients.2⟩

/-- **`downstream_rows`.**  `LEAN_PROVED`. -/
theorem downstream_rows :
    sharedOtherLedger E_2_collar = paperClosedExternal ∧
    sharedOtherLedger E_M_comparison = paperClosedExternal ∧
    sharedOtherLedger asymptoticFCL = conditionalKernel ∧
    sharedOtherLedger effectivity = effectivityOpen ∧
    sharedOtherLedger erdos287 = openExternal := by decide

/-! ## §7  Metadata firewalls -/

/-- **`paperClosedExternal_is_not_kernelProved`.**  `LEAN_PROVED`.

No external analytic statement is called kernel-proved merely because its interface is
represented in Lean. -/
theorem paperClosedExternal_is_not_kernelProved :
    paperClosedExternal ≠ kernelProved ∧ paperClosedExternal ≠ conditionalKernel ∧
    openExternal ≠ kernelProved := by decide

/-- **`no_row_is_a_proof_claim`.**  `LEAN_PROVED`. -/
theorem no_row_is_a_proof_claim :
    sharedOtherLedger erdos287 ≠ kernelProved ∧
    sharedOtherLedger erdos287 ≠ conditionalKernel ∧
    sharedOtherLedger erdos287 ≠ paperClosedExternal := by decide

/-- **`first_open_research_socket_is_the_hard_U`.**  `LEAN_PROVED`.

Everything up to and including the Δ-router is kernel-proved; the earliest open node of
this layer is the hard `U`, `k ≥ 1` other-parent covariance. -/
theorem first_open_research_socket_is_the_hard_U :
    sharedOtherLedger dependentRawPacket = kernelProved ∧
    sharedOtherLedger generatedCoefficients = kernelProved ∧
    sharedOtherLedger deltaRouter = kernelProved ∧
    sharedOtherLedger hardU = openExternal := by decide

end SharedOtherFrontierStatus
end Erdos287
