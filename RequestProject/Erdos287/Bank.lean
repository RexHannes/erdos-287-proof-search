import RequestProject.Erdos287.SourceWeights
import RequestProject.Erdos287.GcdDescent
import RequestProject.Erdos287.BernoulliKernel
import RequestProject.Erdos287.MediumKSource
import RequestProject.Erdos287.RepeatedCores
import RequestProject.Erdos287.DirectedLedger
import RequestProject.Erdos287.FloorInterface

/-!
# Erdős #287 — effectivity certificate bank: aggregator and axiom audit

This module imports the whole banked package and prints the axiom dependencies of every
major theorem.  The only foundational axioms that may appear are `propext`,
`Classical.choice` and `Quot.sound`.  There are **no** custom axioms, no `sorry`, no
`native_decide` and no `unsafe` declarations anywhere in the package.

```
CORE
  coprime_indicator_mobius                 : KERNEL-PROVED
  beta / B0 / lam multiplicativity         : KERNEL-PROVED
  Bsrc typed (non-)multiplicativity        : KERNEL-PROVED
  beta_sub_B0_prime  (λ local factor)      : KERNEL-PROVED
  physicalBsrcMobiusCollapse45             : KERNEL-PROVED   (P0 repair)
  regression_q15_physical                  : KERNEL-PROVED
  local_coefficient_identity               : KERNEL-PROVED
  squarefree_gcd_descent (+ real instance) : KERNEL-PROVED
  descentIndex_coprime  gcd(b,qv)=1        : KERNEL-PROVED
  phase / W-argument / derivative descent  : KERNEL-PROVED
  hyperbola_support_gcd_descent            : KERNEL-PROVED
  mediumK_source_normal_form               : KERNEL-PROVED (per finite truncation)
  jointKernel_noLattice                    : KERNEL-PROVED
  repeated_core_ledger_disjoint / _total   : KERNEL-PROVED

CERTIFICATE
  certifiedSubtotal_correct                : KERNEL-PROVED  = 52188738751 / 10^17
  printed 5.218873872e-7 consistent        : NO
  remainingCapacity_correct                : KERNEL-PROVED  = 36417761249 / 10^17
  printed 3.641776128e-7 consistent        : NO
  sawtooth L² mass, ≤ 11/108 for q ≥ 3     : KERNEL-PROVED
  q = 3 prefix certificate                 : EXTERNAL-CERT (format + interface only)

OPEN
  medium-k joint Bernoulli                 : OPEN
  two-high a ≤ 180                         : OPEN
  signed B_src floor                       : OPEN
  Maynard                                  : NOT ENTERED
  Erdős #287                               : OPEN
```
-/

namespace Erdos287
namespace Bank

section AxiomAudit

open Erdos287

-- §1  source weights and the P0 physical repair
#print axioms Erdos287.SourceWeights.beta_mul
#print axioms Erdos287.SourceWeights.B0_mul
#print axioms Erdos287.SourceWeights.lam_mul
#print axioms Erdos287.SourceWeights.Bsrc_mul_typed
#print axioms Erdos287.SourceWeights.lam_eq_B0_mul_beta
#print axioms Erdos287.SourceWeights.beta_sub_B0_prime
#print axioms Erdos287.SourceWeights.normalizedB0MobiusCollapse45
#print axioms Erdos287.SourceWeights.physicalBsrcMobiusCollapse45
#print axioms Erdos287.SourceWeights.regression_q15_normalized
#print axioms Erdos287.SourceWeights.regression_q15_physical

-- §2–5  gcd descent
#print axioms Erdos287.GcdDescent.coprime_indicator_mobius
#print axioms Erdos287.GcdDescent.local_coefficient_identity
#print axioms Erdos287.GcdDescent.descentIndex_coprime
#print axioms Erdos287.GcdDescent.squarefree_gcd_descent_map
#print axioms Erdos287.GcdDescent.squarefree_gcd_descent
#print axioms Erdos287.GcdDescent.squarefree_gcd_descent_real
#print axioms Erdos287.GcdDescent.onePrime_shared_cancellation
#print axioms Erdos287.GcdDescent.phase_descent
#print axioms Erdos287.GcdDescent.W_argument_descent
#print axioms Erdos287.GcdDescent.derivative_argument_descent
#print axioms Erdos287.GcdDescent.hyperbola_support_gcd_descent

-- §6, §8  sawtooth and joint Bernoulli kernel
#print axioms Erdos287.BernoulliKernel.psi_intCast
#print axioms Erdos287.BernoulliKernel.psi_add_intCast
#print axioms Erdos287.BernoulliKernel.jointKernel_noLattice

-- §7  medium-k source normal form
#print axioms Erdos287.MediumKSource.mediumK_source_normal_form
#print axioms Erdos287.MediumKSource.mediumKWeight_descended
#print axioms Erdos287.MediumKSource.Rmed_descended_window

-- §9  repeated-core ledger
#print axioms Erdos287.RepeatedCores.repeated_core_ledger_disjoint
#print axioms Erdos287.RepeatedCores.repeated_core_ledger_total
#print axioms Erdos287.RepeatedCores.repeated_noLattice_only_global

-- §10–11, §13  certificate ledger and subtotal audit
#print axioms Erdos287.DirectedLedger.certifiedSubtotal_correct
#print axioms Erdos287.DirectedLedger.printed_subtotal_is_not_an_upper_bound
#print axioms Erdos287.DirectedLedger.remainingCapacity_correct
#print axioms Erdos287.DirectedLedger.printed_remaining_overstates_capacity
#print axioms Erdos287.DirectedLedger.sawtooth_sq_mean
#print axioms Erdos287.DirectedLedger.sawtooth_l2_mass_le

-- §12, §14  conditional floor closure
#print axioms Erdos287.FloorInterface.q3_normalised_bound
#print axioms Erdos287.FloorInterface.mediumK_gap_budget_implies_boundary_target
#print axioms Erdos287.FloorInterface.boundary_target_of_ledger_budget
#print axioms Erdos287.FloorInterface.open_nodes_imply_boundary_target

end AxiomAudit

end Bank
end Erdos287
