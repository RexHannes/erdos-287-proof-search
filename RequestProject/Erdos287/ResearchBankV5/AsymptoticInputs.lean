import RequestProject.Erdos287.ResearchBankV5.Routes

/-!
# Research Bank V5 — the external asymptotic-input ledger

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

This file makes the load-bearing *external* mathematics visible.  Every entry is an analytic
statement that the contact-core programme consumes but that is **not** formalized in this project.
No entry is inhabited anywhere in the bank; the corresponding Lean `Prop`s live in
`ContactCore/ExternalInterfaces.lean` and appear only as hypotheses.
-/

namespace Erdos287
namespace ResearchBankV5

open EvidenceKind ResearchStatus

/-- Metadata of an external analytic input. -/
structure ExternalInput where
  /-- Short name. -/
  name : String
  /-- The exact mathematical statement, in words. -/
  statement : String
  /-- Source / reference metadata, if available. -/
  source : String
  /-- Where the input is consumed inside the programme. -/
  consumedAt : String
  /-- Research status. -/
  status : ResearchStatus
  /-- Evidence kind; never `kernelProof` for an external input. -/
  evidence : EvidenceKind
  /-- Whether the statement has been independently refereed. -/
  refereed : Bool
  /-- Whether the statement is formalized in this project. -/
  formalized : Bool
  deriving DecidableEq, Repr

/-- **The external asymptotic-input ledger.** -/
def externalAsymptoticInputs : List ExternalInput :=
  [ { name := "Croot general-modulus reciprocal coverage"
      statement :=
        "For every sufficiently large modulus n, a sufficiently large supply of distinct small " ++
        "primes not dividing n has reciprocal subset sums hitting every residue modulo n."
      source := "Croot-type reciprocal covering result; no formal proof supplied here"
      consumedAt := "ContactCore.CrootGeneralModulus; VAL-TRANS one-demand interface"
      status := bank
      evidence := externalAnalyticBank
      refereed := false
      formalized := false },
    { name := "Croot prime-power corollary"
      statement :=
        "The same coverage statement for prime-power moduli ℓ^k."
      source := "corollary of the general-modulus statement"
      consumedAt := "ContactCore.CrootPrimePowerModulus; valuation-layer one-demand"
      status := bank
      evidence := externalAnalyticBank
      refereed := false
      formalized := false },
    { name := "Croot/PNT multiscale incidence"
      statement :=
        "Multiscale incidence estimate between reciprocal subset sums of primes in dyadic " ++
        "ranges and residue classes, using the prime number theorem."
      source := "multiscale incidence argument; no formal proof supplied here"
      consumedAt := "proof of FP-INTERFACE-GEN"
      status := bank
      evidence := externalAnalyticBank
      refereed := false
      formalized := false },
    { name := "FP-INTERFACE-GEN"
      statement :=
        "If the projection of a Croot-long first-power row language to a Boolean interface T " ++
        "is not the full cube, then |T| ≫_δ N log log p / log N."
      source := "multiscale Croot/PNT incidence argument"
      consumedAt := "ContactCore.FPInterfaceGen"
      status := bank
      evidence := externalAnalyticBank
      refereed := false
      formalized := false },
    { name := "FP-INTERFACE"
      statement :=
        "In the range N ≤ (log p)^B: a non-full-cube projection forces |T| ≥ κ_{δ,B} N."
      source := "specialization of FP-INTERFACE-GEN to the intended range"
      consumedAt := "ContactCore.FPInterface; hypothesis of LINEAR-CHARGE"
      status := bank
      evidence := externalAnalyticBank
      refereed := false
      formalized := false },
    { name := "positive-density multiscale burden"
      statement :=
        "At positive density of scales, the surviving long first-power owners carry a burden " ++
        "of interface coordinates proportional to their heights."
      source := "programme-level asymptotic input"
      consumedAt := "Gate C reduced excess-core analysis"
      status := ResearchStatus.«open»
      evidence := researchConjecture
      refereed := false
      formalized := false } ]

/-- **No external input is formalized in this project.** -/
theorem externalInputs_not_formalized :
    ∀ e ∈ externalAsymptoticInputs, e.formalized = false := by decide

/-- **No external input is recorded as a kernel proof.** -/
theorem externalInputs_not_kernelProof :
    ∀ e ∈ externalAsymptoticInputs, e.evidence ≠ kernelProof := by decide

/-- **No external input is recorded as independently refereed** in this project's metadata. -/
theorem externalInputs_not_refereed :
    ∀ e ∈ externalAsymptoticInputs, e.refereed = false := by decide

end ResearchBankV5
end Erdos287
