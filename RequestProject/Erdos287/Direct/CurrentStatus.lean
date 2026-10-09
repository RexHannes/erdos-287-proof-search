import RequestProject.Erdos287.Direct.BoundaryKernel
import RequestProject.Erdos287.Direct.SparseSubreservoir
import RequestProject.Erdos287.Direct.AbsorberInterfaces
import RequestProject.Erdos287.Direct.LCMCarry

/-!
# Route D — current formal status ledger

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

This is the Route-D ledger.  It is *separate* from the Route-S ledger
(`Erdos287.Effectivity.latestEvidence` and its cut set), which is untouched; the two are
reconciled — without merging — in `Direct/Reconciliation.lean`.

Evidence classes follow the required taxonomy.  A published analytic theorem is **never**
tagged `kernelProved` merely because a bridge consuming it is kernel-proved.
-/

open scoped BigOperators

namespace Erdos287
namespace Direct

/-! ## D.38  Evidence taxonomy -/

/-- The evidence taxonomy of the Direct route. -/
inductive EvidenceDirect
  /-- reconstructed in the Lean kernel here, with no unproved hypothesis -/
  | kernelProved
  /-- kernel-proved *from explicitly named interface hypotheses* -/
  | kernelConditional
  /-- an external published theorem, not formalised here -/
  | externalPublished
  /-- an external claim with no published proof and no formalisation -/
  | externalUnformalised
  /-- awaiting a finite certificate that is not present in this repository -/
  | finiteCertificatePending
  /-- open -/
  | openNode
  /-- retired because refuted -/
  | retiredFalse
  /-- correct but cannot close its target -/
  | nonclosing
  /-- status not determined here -/
  | unknown
  deriving DecidableEq, Repr

/-- Only kernel-proved content counts as closed. -/
def EvidenceDirect.isClosed : EvidenceDirect → Bool
  | .kernelProved => true
  | _ => false

/-! ## D.39  Nodes -/

/-- The Route-D nodes tracked at this checkpoint. -/
inductive DirectNode
  /-- the combinatorial source and its bridges to the exact #287 predicate -/
  | directCore
  /-- the exact ambient-LCM reciprocal compiler -/
  | reciprocalCompiler
  /-- deterministic raw-mask arithmetic -/
  | rawMaskArithmetic
  /-- exact mask counting (needs a prime-counting input) -/
  | maskCountIdentities
  /-- restriction half of the boundary-kernel bridge -/
  | kernelRestriction
  /-- extension half of the boundary-kernel bridge -/
  | kernelExtension
  /-- the finite Fourier all-target lemma -/
  | finiteFourierAllTarget
  /-- the reciprocal exponential-sum input -/
  | reciprocalExpSumInput
  /-- the sparse subreservoir claim -/
  | sparseSubreservoir
  /-- exact LCM / carry algebra -/
  | lcmCarryAlgebra
  /-- the exact path-polynomial target theorem -/
  | pathPolynomialTarget
  /-- the value-preserving switch -/
  | valuePreservingSwitch
  /-- the value-moving switch -/
  | valueMovingSwitch
  /-- analytic supply/abundance of switches -/
  | switchSupply
  /-- the deterministic target-tuning bridge -/
  | targetTuningBridge
  /-- the exact signed absorber -/
  | exactSignedAbsorber
  /-- classification of augmented-mask/kernel survivors -/
  | maskSurvivorClassification
  /-- the full exact assembly of Route D -/
  | fullAssembly
  /-- unrestricted Erdős #287 -/
  | erdos287
  deriving DecidableEq, Repr

/-- Evidence class of each Route-D node. -/
def directEvidence : DirectNode → EvidenceDirect
  | .directCore => .kernelProved
  | .reciprocalCompiler => .kernelProved
  | .rawMaskArithmetic => .kernelProved
  | .maskCountIdentities => .kernelConditional
  | .kernelRestriction => .kernelProved
  | .kernelExtension => .openNode
  | .finiteFourierAllTarget => .kernelProved
  | .reciprocalExpSumInput => .externalPublished
  | .sparseSubreservoir => .openNode
  | .lcmCarryAlgebra => .kernelProved
  | .pathPolynomialTarget => .kernelProved
  | .valuePreservingSwitch => .kernelProved
  | .valueMovingSwitch => .kernelProved
  | .switchSupply => .openNode
  | .targetTuningBridge => .kernelConditional
  | .exactSignedAbsorber => .openNode
  | .maskSurvivorClassification => .openNode
  | .fullAssembly => .openNode
  | .erdos287 => .openNode

/-- **`direct_erdos287_open`.**  `KERNEL-PROVED` bookkeeping. -/
theorem direct_erdos287_open : directEvidence .erdos287 = EvidenceDirect.openNode := rfl

/-! ## D.40  What the closed nodes actually are

Each `kernelProved` tag below is discharged by exhibiting the theorem it refers to. -/

/-- **`directCore_closed`.**  `KERNEL-PROVED`.  The source bridges hold in both directions. -/
theorem directCore_closed :
    directEvidence .directCore = EvidenceDirect.kernelProved ∧
      (∀ (a M : ℕ) (eps : ℕ → Bool), DirectCounterexample a M eps →
        Erdos287Counterexample (selected a M eps)) ∧
      (∀ (A : Finset ℕ) (h : Erdos287Counterexample A),
        selected (A.min' h.nonempty) (A.max' h.nonempty) (fun n => decide (n ∈ A)) = A) :=
  ⟨rfl, fun _ _ _ h => directCounterexample_to_exact h,
    fun _ h => (exact_to_directCounterexample h).2⟩

/-- **`reciprocalCompiler_closed`.**  `KERNEL-PROVED`. -/
theorem reciprocalCompiler_closed :
    directEvidence .reciprocalCompiler = EvidenceDirect.kernelProved ∧
      (∀ (I : Finset ℕ), 0 ∉ I → ∀ A ⊆ I,
        (recipSum A = 1 ↔ ∑ n ∈ A, setLcm I / n = setLcm I)) :=
  ⟨rfl, fun _ h0 _ hA => compiler_ambient h0 hA⟩

/-- **`rawMask_closed`.**  `KERNEL-PROVED`.  Uniqueness of the large-prime factorisation in the
established regime. -/
theorem rawMask_closed :
    directEvidence .rawMaskArithmetic = EvidenceDirect.kernelProved ∧
      (∀ (M : ℕ), 18632 ≤ M → ∀ n d₁ r₁ d₂ r₂ : ℕ, 0 < n →
        n = d₁ * r₁ → r₁.Prime → M < 137 * r₁ →
        n = d₂ * r₂ → r₂.Prime → M < 137 * r₂ → d₂ ≤ 136 → r₁ = r₂ ∧ d₁ = d₂) :=
  ⟨rfl, fun _ hM _ _ _ _ _ hn h₁ hp₁ hlt₁ h₂ hp₂ hlt₂ hd₂ =>
    largePrime_factorisation_unique hM hn h₁ hp₁ hlt₁ h₂ hp₂ hlt₂ hd₂⟩

/-- **`lcmCarry_closed`.**  `KERNEL-PROVED`.  The jump identity and the descending recurrence. -/
theorem lcmCarry_closed :
    directEvidence .lcmCarryAlgebra = EvidenceDirect.kernelProved ∧
      (∀ n : ℕ, 1 ≤ n → LN (n + 1) = JN (n + 1) * LN n) ∧
      (∀ p k : ℕ, p.Prime → 1 ≤ k → JN (p ^ k) = p) ∧
      (∀ N : ℕ, ¬ IsPrimePow N → JN N = 1) :=
  ⟨rfl, fun n hn => LN_succ_eq n hn, fun _ _ hp hk => JN_prime_pow hp hk,
    fun _ h => JN_of_not_isPrimePow h⟩

/-- **`pathPolynomial_closed`.**  `KERNEL-PROVED`.  The exact target theorem. -/
theorem pathPolynomial_closed :
    directEvidence .pathPolynomialTarget = EvidenceDirect.kernelProved ∧
      (∀ (P V : Finset ℕ) (ell τ : ℕ), ell ≠ 0 → Disjoint P V →
        (∀ n ∈ P, n ≠ 0 ∧ n ∣ ell) → (∀ n ∈ V, n ≠ 0 ∧ n ∣ ell) →
        (∑ n ∈ P, ell / n) + τ = ell →
        ((∃ J ∈ indepSubsets V, recipSum (P ∪ J) = 1) ↔
          0 < (pathPoly V (fun n => ell / n)).coeff τ)) :=
  ⟨rfl, fun _ _ _ _ hell hdisj hP hV hτ => exact_reciprocal_target hell hdisj hP hV hτ⟩

/-- **`finiteFourier_closed`.**  `KERNEL-PROVED`.  The finite all-target lemma is internal
finite mathematics: it is proved in the kernel, *not* assumed. -/
theorem finiteFourier_closed :
    directEvidence .finiteFourierAllTarget = EvidenceDirect.kernelProved ∧
      (∀ (q : ℕ) (_ : NeZero q) (C : Finset ℕ) (a : ℕ → ZMod q) (B : ℝ),
        (∀ ψ : AddChar (ZMod q) ℂ, ψ ≠ 0 → ‖∏ n ∈ C, (1 + ψ (a n))‖ ≤ B) →
        ((q : ℝ) - 1) * B < 2 ^ C.card → ∀ t : ZMod q, 0 < subsetSumCount q C a t) :=
  ⟨rfl, fun _ _ C a B hB hlt t => subsetSumCount_pos_of_bound C a B hB hlt t⟩

/-- **`switches_closed`.**  `KERNEL-PROVED`.  Both switch calculi. -/
theorem switches_closed :
    directEvidence .valuePreservingSwitch = EvidenceDirect.kernelProved ∧
      directEvidence .valueMovingSwitch = EvidenceDirect.kernelProved ∧
      (∀ k : ℚ, k ≠ 0 → 1 / (6 * k) = 1 / (10 * k) + 1 / (15 * k)) ∧
      (∀ a M : ℕ, ∀ eps : ℕ → Bool, ∀ out inn : ℕ, ProtectedSwitch a M eps out inn →
        recipSum (selected a M (toggle eps out inn)) =
          recipSum (selected a M eps) + 1 / (inn : ℚ) - 1 / (out : ℚ)) :=
  ⟨rfl, rfl, fun k hk => sixSwitch_identity k hk, fun _ _ _ _ _ hs => recipSum_toggle hs⟩

/-! ## D.41  The conditional nodes -/

/-- **`targetTuning_is_conditional`.**  `KERNEL-PROVED` bookkeeping.  The tuning bridge is
tagged `kernelConditional`, never `kernelProved`: it is proved only from its four named
interfaces. -/
theorem targetTuning_is_conditional :
    directEvidence .targetTuningBridge = EvidenceDirect.kernelConditional ∧
      (∀ (a M K : ℕ) (ch : ℕ → (ℕ → Bool)) (E : ℚ) (budget : ℕ), 0 ≤ E →
        CoarseSwitchSupply a M K ch → FineSwitchSupply a M K ch E →
        HarmonicInterior a M K ch → SparseRepairCost a M K ch budget →
        TargetStraddling a M E budget) :=
  ⟨rfl, fun _ _ _ _ _ _ hE h1 h2 h3 h4 => targetTuning_of hE h1 h2 h3 h4⟩

/-- **`expSumInput_is_external`.**  `KERNEL-PROVED` bookkeeping.  The reciprocal
exponential-sum bound is an external published input: it is tagged `externalPublished`, is
*not* closed, and appears only as a hypothesis. -/
theorem expSumInput_is_external :
    directEvidence .reciprocalExpSumInput = EvidenceDirect.externalPublished ∧
      (directEvidence .reciprocalExpSumInput).isClosed = false ∧
      (∀ (q : ℕ) (_ : NeZero q) (C : Finset ℕ) (B : ℝ), ReciprocalExpSumInterface q C B →
        ((q : ℝ) - 1) * B < 2 ^ C.card → AttainsAllTargets q C) :=
  ⟨rfl, rfl, fun _ _ _ _ hBG hlt => allTargets_of_expSumInterface hBG hlt⟩

/-- **`absorber_open`.**  `KERNEL-PROVED` bookkeeping.  The exact signed absorber is open: only
its necessary lattice conditions are proved, and the predicate is not inhabited. -/
theorem absorber_open :
    directEvidence .exactSignedAbsorber = EvidenceDirect.openNode ∧
      (∀ (a M : ℕ) (eps : ℕ → Bool) (e : ℚ) (S : Finset ℕ) (outSite innSite : ℕ → ℕ)
        (bound : ℕ), ExactSignedAbsorber a M eps e S outSite innSite bound →
        ∃ m : ℤ,
          ((bufDen S (fun i => 1 / (innSite i : ℚ) - 1 / (outSite i : ℚ)) : ℚ)) * e = (m : ℚ) ∧
            bufGcd S (fun i => 1 / (innSite i : ℚ) - 1 / (outSite i : ℚ)) ∣ m) :=
  ⟨rfl, fun _ _ _ _ _ _ _ _ h => exactSignedAbsorber_lattice_necessary h⟩

/-! ## D.42  Dependencies and the current Route-D cut -/

/-- Recorded prerequisites of the Route-D nodes. -/
def directDeps : DirectNode → List DirectNode
  | .maskSurvivorClassification => [.rawMaskArithmetic, .kernelRestriction, .lcmCarryAlgebra]
  | .kernelExtension => [.kernelRestriction]
  | .sparseSubreservoir => [.finiteFourierAllTarget, .reciprocalExpSumInput]
  | .targetTuningBridge => [.valueMovingSwitch, .valuePreservingSwitch]
  | .exactSignedAbsorber => [.valueMovingSwitch]
  | .fullAssembly =>
      [.directCore, .reciprocalCompiler, .pathPolynomialTarget, .maskSurvivorClassification,
        .switchSupply, .exactSignedAbsorber, .kernelExtension, .sparseSubreservoir]
  | .erdos287 => [.fullAssembly]
  | _ => []

/-- The current Route-D conceptual cut: `D1` survivors, `D2` analytic activation/supply,
`D3` exact absorber, `D4` full assembly. -/
def directCutSet : List DirectNode :=
  [.maskSurvivorClassification, .switchSupply, .kernelExtension, .sparseSubreservoir,
    .exactSignedAbsorber, .fullAssembly]

/-- **`directCut_all_open`.**  `KERNEL-PROVED`.  Every Route-D cut node is open. -/
theorem directCut_all_open : ∀ n ∈ directCutSet, directEvidence n = EvidenceDirect.openNode := by
  intro n hn
  fin_cases hn <;> rfl

/-- **`directCut_not_closed`.**  `KERNEL-PROVED`.  No cut node is tagged closed. -/
theorem directCut_not_closed : ∀ n ∈ directCutSet, (directEvidence n).isClosed = false := by
  intro n hn
  fin_cases hn <;> rfl

/-- The independence of the four conceptual Route-D cut nodes has **not** been established by
dependency analysis; it is recorded as `unknown`, not asserted. -/
def directCutIndependence : EvidenceDirect := .unknown

/-- **`directCut_independence_unknown`.**  `KERNEL-PROVED` bookkeeping.  In particular the
recorded dependency graph does *not* make the cut nodes pairwise independent: `fullAssembly`
depends on four of them. -/
theorem directCut_independence_unknown :
    directCutIndependence = EvidenceDirect.unknown ∧
      DirectNode.maskSurvivorClassification ∈ directDeps .fullAssembly ∧
      DirectNode.switchSupply ∈ directDeps .fullAssembly ∧
      DirectNode.exactSignedAbsorber ∈ directDeps .fullAssembly ∧
      DirectNode.kernelExtension ∈ directDeps .fullAssembly := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> simp [directDeps]

/-- **`erdos287_needs_directCut`.**  `KERNEL-PROVED`.  Erdős #287 depends, along Route D, on
the full assembly, which depends on the whole cut. -/
theorem erdos287_needs_directCut :
    directDeps .erdos287 = [DirectNode.fullAssembly] ∧
      (∀ n ∈ directCutSet, n = DirectNode.fullAssembly ∨ n ∈ directDeps .fullAssembly) := by
  refine ⟨rfl, ?_⟩
  intro n hn
  fin_cases hn <;> simp [directDeps]

end Direct
end Erdos287
