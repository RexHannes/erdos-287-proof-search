import RequestProject.Erdos287.Direct.Core
import RequestProject.Erdos287.Direct.ReciprocalCompiler
import RequestProject.Erdos287.Direct.RawMask
import RequestProject.Erdos287.Direct.BoundaryKernel
import RequestProject.Erdos287.Direct.LCMCarry
import RequestProject.Erdos287.Direct.PathPolynomial
import RequestProject.Erdos287.Direct.LargePrimeCompletionFinite
import RequestProject.Erdos287.Direct.SparseSubreservoir
import RequestProject.Erdos287.Direct.ProtectedSwitches
import RequestProject.Erdos287.Direct.TargetTuningFinite
import RequestProject.Erdos287.Direct.AbsorberInterfaces
import RequestProject.Erdos287.Direct.CurrentStatus
import RequestProject.Erdos287.Direct.Reconciliation

/-!
# Erdős #287 — Route D (Direct Reciprocal programme) aggregator

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

This aggregator collects the append-only Route-D namespace.  It changes nothing in the
existing (Route-S) development: the earlier ledger, its cut set and the certified finite
ceiling are re-checked, unchanged, in `Direct/Reconciliation.lean`.
-/
