import RequestProject.CurrentProgramme.StatusTypes

/-!
# Erdős #287 — 1 Sep 2026 direct3221 / reassembly status

This file is deliberately a status layer only.  It records the distinction between
(1) the still-open generic arbitrary-log-power supersquare-root socket and
(2) the newer source-specific Balanced7 physical endpoint, which is closed only at
paper/research level and is not promoted here to a kernel proof.
-/

namespace Erdos287Sep1Status

inductive ResearchStatus
  | open
  | paperClosed
  | conditional
  | kernelProved
  deriving DecidableEq, Repr

/-- The reusable arbitrary-`A` supersquare-root socket remains open. -/
def genericSupersqrtArbitraryA : ResearchStatus := .open

/-- The source-specific direct3221 Balanced7 supersquare-root endpoint is a research/paper closure. -/
def balanced7Direct3221Physical : ResearchStatus := .paperClosed

/-- Full-q Balanced7 is paper/research closed under the frozen source bridge and comparison bank. -/
def balanced7FullQ : ResearchStatus := .paperClosed

/-- The controlling research frontier after the direct3221 endpoint. -/
def k0Sp2UniformFragmentationReassembly : ResearchStatus := .open

/-- The complete full-source local analytic kernel is not yet established. -/
def fullSourceLocalAnalyticKernel : ResearchStatus := .open

/-- WindowPair remains downstream and is not inferred from Balanced7 alone. -/
def windowPair : ResearchStatus := .open

/-- Public theorem status. -/
def erdos287 : ResearchStatus := .open

/-- Firewall: a paper-level physical endpoint is not a kernel proof of the generic socket. -/
theorem physical_endpoint_not_generic_kernel :
    balanced7Direct3221Physical = .paperClosed ∧
    genericSupersqrtArbitraryA = .open := by
  constructor <;> rfl

/-- The current research frontier is reassembly rather than the old supersquare-root socket. -/
theorem current_frontier_is_reassembly :
    k0Sp2UniformFragmentationReassembly = .open := by
  rfl

end Erdos287Sep1Status
