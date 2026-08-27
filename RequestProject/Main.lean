import RequestProject.Erdos287.Defs
import RequestProject.Erdos287.Cnum
import RequestProject.Erdos287.TopLayer
import RequestProject.Erdos287.Window
import RequestProject.Erdos287.Counterexample
import RequestProject.Erdos287.PrimeFree
import RequestProject.Erdos287.Uniform
import RequestProject.Erdos287.Blocker
import RequestProject.Erdos287.Fiber
import RequestProject.Erdos287.Universal
import RequestProject.Erdos287.BadPrimes
import RequestProject.Erdos287.Chain
import RequestProject.Erdos287.SFTAudit
import RequestProject.Erdos287.ChenP2Audit
import RequestProject.Erdos287.CeilingCRT
import RequestProject.Erdos287.RoughPrime
import RequestProject.Erdos287.NonAdjacentHoles
import RequestProject.Erdos287.KernelAPBlocker
import RequestProject.Erdos287.SophieOptimal
import RequestProject.Erdos287.SophieBandCompiler
import RequestProject.Erdos287.V2SophieFinite
import RequestProject.Erdos287.V2SophieBand
import RequestProject.Erdos287.V2BandSupplyChecks
import RequestProject.Status.Erdos287V2Status
import RequestProject.Erdos287.ProblemStatement
import RequestProject.Erdos287.FiniteMasterReduction
import RequestProject.Erdos287.FiniteRemainder
import RequestProject.Erdos287.FiniteRangeExtension
import RequestProject.Erdos287.ClosureInputs
import RequestProject.Status.Erdos287EndToEndStatus
import RequestProject.Status.Erdos287V13Frontier

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false
