import RequestProject.Erdos287.CurrentTail.ExponentLedger

/-!
# Erdős #287 — current tail consolidation: the auxiliary error ledger

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

Every error term arising in the Ordering-B reduction is an element of `AuxError`; there is
no unnamed "negligible error".  Each carries:

* `errorClass` — `ExactZero | ReciprocalDensityLogSaving | FixedPowerSaving |
  ExternalProvider | Open` (the *claimed* mechanism of the paper argument);
* `evidence` — what is actually in Lean: `kernelExact` (identity proved), `kernelReduction`
  (deterministic reduction proved, analytic input named), or `providerOnly` (only the named
  provider; the derivation is paper-level);
* `leanAnchor` — the Lean declaration(s) carrying it.

Kernel-checked facts about the ledger: completeness of `allErrors`, the main/aux partition, the
unique `ExactZero` entry, and that no entry is `Open`.  (The *source dictionary* routing these
pieces is not an error term; its status is `Candidate` in `ClosureDAG.lean`.)
-/

namespace Erdos287.CurrentTail

/-- All error terms of the Ordering-B reduction. -/
inductive AuxError
  | coprimality
  | divisorTruncation
  | nearDiagonal
  | smoothPruning
  | squarefullPruning
  | lemma136Remainder
  | zeroFrequency
  | boundary
  | baseFluctuation
  | rbdhFamily
  | e1Bilinear
  | e2Spectral
  deriving DecidableEq, Repr, Fintype

/-- Error classes. -/
inductive ErrorClass
  | ExactZero
  | ReciprocalDensityLogSaving
  | FixedPowerSaving
  | ExternalProvider
  | Open
  deriving DecidableEq, Repr

/-- Formal evidence available in Lean. -/
inductive FormalEvidence
  | kernelExact
  | kernelReduction
  | providerOnly
  deriving DecidableEq, Repr

/-- Claimed mechanism of each error. -/
def errorClass : AuxError → ErrorClass
  | .coprimality => .ReciprocalDensityLogSaving
  | .divisorTruncation => .ReciprocalDensityLogSaving
  | .nearDiagonal => .ReciprocalDensityLogSaving
  | .smoothPruning => .FixedPowerSaving
  | .squarefullPruning => .FixedPowerSaving
  | .lemma136Remainder => .ExternalProvider
  | .zeroFrequency => .ExactZero
  | .boundary => .FixedPowerSaving
  | .baseFluctuation => .ExternalProvider
  | .rbdhFamily => .ReciprocalDensityLogSaving
  | .e1Bilinear => .ExternalProvider
  | .e2Spectral => .ExternalProvider

/-- What is actually proved in Lean for each error. -/
def evidence : AuxError → FormalEvidence
  | .coprimality => .kernelReduction
  | .divisorTruncation => .providerOnly
  | .nearDiagonal => .kernelReduction
  | .smoothPruning => .providerOnly
  | .squarefullPruning => .providerOnly
  | .lemma136Remainder => .providerOnly
  | .zeroFrequency => .kernelExact
  | .boundary => .providerOnly
  | .baseFluctuation => .kernelReduction
  | .rbdhFamily => .kernelReduction
  | .e1Bilinear => .kernelReduction
  | .e2Spectral => .kernelReduction

/-- Lean anchors (declaration names) of each error. -/
def leanAnchor : AuxError → List String
  | .coprimality => ["relative_term_eq_DeltaRel", "TensorSource.Rrel_eq_main_sub_coprimality"]
  | .divisorTruncation => ["AuxPieceProviders"]
  | .nearDiagonal => ["pairs_congr_window_real", "nearDiagonal_to_reciprocalDensity",
      "NearDiagonalRangeComparison"]
  | .smoothPruning => ["AuxPieceProviders"]
  | .squarefullPruning => ["AuxPieceProviders"]
  | .lemma136Remainder => ["AuxPieceProviders"]
  | .zeroFrequency => ["TensorSource.Rrel_indep_main"]
  | .boundary => ["AuxPieceProviders"]
  | .baseFluctuation => ["TensorSource.Rpaid_bound", "BaseSWProvider"]
  | .rbdhFamily => ["RBDH_of_BDH", "family_payment_tau", "spectator_norm_of_moment"]
  | .e1Bilinear => ["DeltaRel_convolution", "MaynardE1Estimate"]
  | .e2Spectral => ["crt_phase_split_real", "dualLength_enlarged", "PascadiE2Printed",
      "QuantitativeTH"]

/-- The complete list of errors. -/
def allErrors : List AuxError :=
  [.coprimality, .divisorTruncation, .nearDiagonal, .smoothPruning, .squarefullPruning,
   .lemma136Remainder, .zeroFrequency, .boundary, .baseFluctuation, .rbdhFamily, .e1Bilinear,
   .e2Spectral]

theorem allErrors_complete : ∀ e : AuxError, e ∈ allErrors := by decide

/-- Pieces bounding the relative main part `R_rel^main` (after the Ordering-B reduction). -/
def mainPieces : Finset AuxError :=
  {.divisorTruncation, .nearDiagonal, .smoothPruning, .squarefullPruning, .lemma136Remainder,
   .boundary, .rbdhFamily, .e1Bilinear, .e2Spectral}

/-- Pieces whose smallness is an explicit auxiliary provider (not E₁/E₂/RBDH/base). -/
def auxPieces : Finset AuxError :=
  {.coprimality, .divisorTruncation, .nearDiagonal, .smoothPruning, .squarefullPruning,
   .lemma136Remainder, .boundary}

theorem no_open_error : ∀ e : AuxError, errorClass e ≠ .Open := by decide

theorem exactZero_iff : ∀ e : AuxError, errorClass e = .ExactZero ↔ e = .zeroFrequency := by
  decide

theorem every_error_anchored : ∀ e : AuxError, leanAnchor e ≠ [] := by
  intro e; cases e <;> simp [leanAnchor]

theorem zeroFrequency_not_main : AuxError.zeroFrequency ∉ mainPieces := by decide

end Erdos287.CurrentTail
