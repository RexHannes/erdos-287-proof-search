import RequestProject.Main
import RequestProject.CurrentProgramme.Erdos287Direct3221CenteredDefect
import RequestProject.CurrentProgramme.Erdos287Direct3221Interfaces
import RequestProject.CurrentProgramme.Erdos287Direct3221RawRawGeometry
import RequestProject.CurrentProgramme.Erdos287K0SP2FragmentationInterfaces
import RequestProject.CurrentProgramme.Erdos287K0SP2LogBudget
import RequestProject.Status.CurrentStatusErdos287Direct3221Reassembly
import RequestProject.Status.AxiomAuditErdos287Direct3221CenteredDefect
import RequestProject.Status.AxiomAuditErdos287Direct3221RawRawGeometry
import RequestProject.Status.AxiomAuditErdos287Direct3221Reassembly
import RequestProject.Status.AxiomAuditErdos287K0SP2Fragmentation

/-!
# Current Erdős #287 formal entrypoint — 1 September 2026

This is the living formal entrypoint for the 1-Sep #287 status layer.

It imports the established #287 `RequestProject.Main` spine and then the new direct3221 / K0-SP2
finite-data, interface, log-budget, status and axiom-audit modules.

No Gate-1A / Gate-1B / Twin-Prime source module is imported here.  Older cross-project-named
trusted-bank and challenge modules may remain in Git history or as legacy source files, but they are
not dependencies of this entrypoint and carry no theorem ownership for the current #287 programme.

Analytic provider interfaces remain uninhabited unless separately formalized.  In particular this
entrypoint does not prove Erdős #287.
-/

namespace Erdos287Current

/-- Machine-readable public nonclaim for the living entrypoint. -/
theorem erdos287_remains_open_metadata :
    Erdos287Sep1Status.erdos287 = .open := by
  rfl

/-- The controlling research-status node is the K0-SP2 reassembly interface. -/
theorem controlling_frontier_is_k0_sp2_reassembly :
    Erdos287Sep1Status.k0Sp2UniformFragmentationReassembly = .open := by
  rfl

end Erdos287Current
