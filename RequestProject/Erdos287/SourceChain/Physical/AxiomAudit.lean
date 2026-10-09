import RequestProject.Erdos287.SourceChain.Physical.Tail
import RequestProject.Erdos287.SourceChain.Physical.Profile

/-!
# Erdős #287 — physical source: build-time axiom audit

Each line prints the axioms of a physical-source theorem at build time.  Expected output for
every line: `[propext, Classical.choice, Quot.sound]` (or a subset).  No `sorryAx`, no
`Lean.ofReduceBool`, no custom axiom.
-/

open Erdos287.Physical Erdos287.Physical.PhysData

#print axioms Erdos287.Physical.crt_int
#print axioms Erdos287.Physical.crt_two
#print axioms Erdos287.Physical.mul_congr_iff_inv
#print axioms Erdos287.Physical.PhysData.cRes_spec
#print axioms Erdos287.Physical.PhysData.cRes_unique
#print axioms Erdos287.Physical.PhysData.cRes_unit
#print axioms Erdos287.Physical.PhysData.AB_coprime
#print axioms Erdos287.Physical.PhysData.g_coprime
#print axioms Erdos287.Physical.PhysData.reduce_iff
#print axioms Erdos287.Physical.PhysData.bRes_spec
#print axioms Erdos287.Physical.PhysData.bRes_unique
#print axioms Erdos287.Physical.PhysData.bRes_unit
#print axioms Erdos287.Physical.PhysData.base_iff
#print axioms Erdos287.Physical.PhysData.spectator_iff
#print axioms Erdos287.Physical.PhysData.scalar_iff
#print axioms Erdos287.Physical.PhysData.packet_congruence_iff
#print axioms Erdos287.Physical.PhysData.cnt_eq
#print axioms Erdos287.Physical.PhysData.pairSum_eq_packets
#print axioms Erdos287.Physical.PhysData.pairSum_eq_main_add_rem
#print axioms Erdos287.Physical.PhysData.RSigmaP_eq_packetIndexed
#print axioms Erdos287.Physical.PhysData.pairTotal_eq_main_add_RSigmaP
#print axioms Erdos287.Physical.PhysData.RSigmaP_eq_rel_add_base
#print axioms Erdos287.Physical.PhysData.RSigmaP_eq_sum_packetTensor
#print axioms Erdos287.Physical.PhysData.RSigmaP_eq_sum_rel_paid
#print axioms Erdos287.Physical.generic_unrestricted_j_overcounts
#print axioms Erdos287.Physical.wgood_eventually
#print axioms Erdos287.Physical.PhysData.maynardInner_eq_divisors
#print axioms Erdos287.Physical.framework_iff
#print axioms Erdos287.Physical.tail_of_littleO_for
#print axioms Erdos287.Physical.physDataAt_wgood
#print axioms Erdos287.Physical.PhysicalFamily.physical_littleO_of_rel_base
#print axioms Erdos287.Physical.PhysicalFamily.Tail287_of_physical
#print axioms Erdos287.Physical.physPsi_contDiff
#print axioms Erdos287.Physical.physPsi_plateau
#print axioms Erdos287.Physical.physPsi_hasCompactSupport
