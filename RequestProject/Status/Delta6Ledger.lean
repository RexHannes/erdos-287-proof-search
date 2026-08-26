import Mathlib

/-!
# Δv6 status ledger and bibliographic records

Pure data: an enumeration of bank statuses, the dependency DAG as a list of entries, and
bibliographic records for external literature.

**No theorem is derived from any bibliographic record.**  A record is a string-valued
audit note, not a mathematical assumption, and none of these declarations is used in a
proof anywhere in the project.

Gate 1A, Gate 1B, ACBV45, mixed-start NSE / RLS45 and Erdős #287 are all **OPEN**.
-/

namespace Status
namespace Delta6

/-- Status labels used in the dependency ledger. -/
inductive BankStatus
  /-- Kernel-checked in this project, no open input. -/
  | leanProved
  /-- Kernel-checked, but with the open input as an explicit hypothesis. -/
  | conditionalKernelTheorem
  /-- Open analytic statement; stated only, never assumed. -/
  | openAnalytic
  /-- Requires a source definition that is absent from this repository. -/
  | sourceFieldRequired
  /-- External candidate whose range compatibility is not established. -/
  | externalCandidate
  /-- Retracted / dead as a universal closure. -/
  | retracted
  /-- Open until an effective threshold plus a finite verification below it. -/
  | openUntilEffectiveThreshold
  deriving DecidableEq, Repr

/-- One line of the dependency ledger. -/
structure LedgerEntry where
  /-- Gate / application area. -/
  area : String
  /-- The item. -/
  item : String
  /-- Its status. -/
  status : BankStatus
  /-- Where it lives, or why it is open. -/
  note : String
  deriving Repr

/-- The Δv6 dependency DAG. -/
def ledger : List LedgerEntry :=
  [ ⟨"GATE 1A", "source identity Ctilde = H·S + negligible", BankStatus.sourceFieldRequired,
      "authoritative Ctilde^gen definition absent from this repository; carried as an explicit hypothesis"⟩,
    ⟨"GATE 1A", "M-row conservation (M-CONSV)", BankStatus.leanProved,
      "TrustedBank/Gate1A/RowConservation.lean"⟩,
    ⟨"GATE 1A", "scale ledger, three exponent gaps 1/18, 1/36, 1/24", BankStatus.leanProved,
      "TrustedBank/Gate1A/ScaleLedger.lean"⟩,
    ⟨"GATE 1A", "SOURCE-AVG-JDR", BankStatus.openAnalytic,
      "Challenges/Delta6Interfaces.lean (stated only)"⟩,
    ⟨"GATE 1A", "AVG-JDR ⟹ Gate target", BankStatus.conditionalKernelTheorem,
      "TrustedBank/Gate1A/AvgJDRInterface.lean"⟩,
    ⟨"GATE 1A", "pointwise SB-ν / SRB-only / M-SYNC-WEAK / U^5-U^3", BankStatus.retracted,
      "non-controlling; auxiliary only"⟩,
    ⟨"GATE 1B", "centered rho product identity", BankStatus.leanProved,
      "TrustedBank/Gate1B/CenteredRho.lean"⟩,
    ⟨"GATE 1B", "clean squarefree Möbius collapse", BankStatus.leanProved,
      "TrustedBank/Gate1B/MobiusCollapse.lean"⟩,
    ⟨"GATE 1B", "separable SOURCE-MMD on a clean cell", BankStatus.leanProved,
      "TrustedBank/Gate1B/SeparableWeights.lean"⟩,
    ⟨"GATE 1B", "nonseparable weight cost inheritance", BankStatus.leanProved,
      "TrustedBank/Gate1B/SeparableWeights.lean (mmd_cost_bound)"⟩,
    ⟨"GATE 1B", "actual source weight MMD", BankStatus.sourceFieldRequired,
      "SourceMMDRequirements: no instance is supplied"⟩,
    ⟨"GATE 1B", "same-start SD45 diagonal", BankStatus.leanProved,
      "TrustedBank/Gate1B/StartInjectivity.lean"⟩,
    ⟨"GATE 1B", "mixed-start NSE / RLS45", BankStatus.openAnalytic,
      "mixedStart_not_diagonal shows same-start does not imply it"⟩,
    ⟨"GATE 1B", "ACBV45", BankStatus.openAnalytic,
      "not a direct corollary of the published 5/8-type results"⟩,
    ⟨"GATE 1B", "B_cross universal", BankStatus.openAnalytic,
      "positive Cauchy closure retracted"⟩,
    ⟨"R9", "finite certificate value 70", BankStatus.conditionalKernelTheorem,
      "TrustedBank/R9/Certificate.lean; the exact Ford H_g formula is a hypothesis"⟩,
    ⟨"R9", "R9 fraction estimate", BankStatus.openAnalytic, "analytic mass question"⟩,
    ⟨"R9", "nu = 1/5 compatibility", BankStatus.externalCandidate,
      "current engine Type-II range is approximately up to exponent 1/6"⟩,
    ⟨"ERDOS 287", "top-layer fibre congruence", BankStatus.leanProved,
      "Erdos287/TopLayer.lean (existing bank)"⟩,
    ⟨"ERDOS 287", "good-prime exclusion", BankStatus.leanProved,
      "TrustedBank/Erdos287/GoodPrime.lean"⟩,
    ⟨"ERDOS 287", "adjacent good-factor blocker", BankStatus.leanProved,
      "TrustedBank/Erdos287/GoodPrime.lean"⟩,
    ⟨"ERDOS 287", "log-cofactor finite blocker (abstract J)", BankStatus.leanProved,
      "TrustedBank/Erdos287/GoodPrime.lean (logCofactor_finite_blocker)"⟩,
    ⟨"ERDOS 287", "log-cofactor asymptotic step", BankStatus.openAnalytic,
      "Challenges/Delta6Interfaces.lean (external elementary asymptotics)"⟩,
    ⟨"ERDOS 287", "global LCB_eta supply", BankStatus.openAnalytic,
      "Challenges/Delta6Interfaces.lean"⟩,
    ⟨"ERDOS 287", "finite completion", BankStatus.openUntilEffectiveThreshold,
      "needs an effective threshold plus verification below it"⟩ ]

/-- A bibliographic / audit record.  **Not** a mathematical assumption. -/
structure LiteratureRecord where
  /-- Short key. -/
  key : String
  /-- What the published work provides, as an audit note. -/
  content : String
  /-- What still has to be supplied before it could be used here. -/
  gap : String
  deriving Repr

/-- External literature records.  No Gate theorem is proved from any of these. -/
def literature : List LiteratureRecord :=
  [ ⟨"FORD_MAYNARD",
      "a general nonnegative prime-producing sieve uses Type I and Type II information; substantial Type II information is necessary in their general framework",
      "no Lean consequence is drawn; recorded for audit only"⟩,
    ⟨"PASCADI_5_8",
      "5/8 - o(1) distribution capacity for primes / smooth numbers under the paper's specified factorable-weight hypotheses",
      "the coefficient-class hypotheses must be mapped to the actual source coefficients"⟩,
    ⟨"YANG_CONVOLUTION_BV",
      "convolution-type Bombieri-Vinogradov with well-factorable weights under the published hypotheses",
      "same coefficient-class mapping is unverified here"⟩,
    ⟨"WRIGHT_FIXED_FACTOR",
      "partially-fixed denominator Kloosterman-fraction machinery",
      "not instantiated for the actual source"⟩,
    ⟨"BLOMER_PASCADI",
      "critical bilinear Kloosterman saving",
      "not instantiated for the actual source"⟩ ]

/-- Range guard: the current engine's Type-II range, recorded separately from any
external `nu = 1/5` certificate candidate. -/
def currentEngineTypeIIRange : String :=
  "approximately up to exponent 1/6"

/-- The `nu = 1/5` Ford certificate is an external candidate whose range compatibility
with the current engine is open. -/
def fordNu15Status : BankStatus := BankStatus.externalCandidate

end Delta6
end Status
