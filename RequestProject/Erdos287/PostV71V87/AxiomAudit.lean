import RequestProject.Erdos287.PostV71V87.ClosureDAG

/-!
# Erdős #287 (post-V71 → V87) — axiom audit

`#assert_std_axioms foo` collects the axioms of `foo` (as `#print axioms` does) and **fails
the build** if any axiom other than `propext`, `Classical.choice`, `Quot.sound` occurs.
In particular `sorryAx`, any custom axiom, and the `native_decide` axiom
`Lean.ofReduceBool` are rejected.  Each principal theorem is additionally printed with
`#print axioms`.
-/

open Lean Elab Command in
/-- Fail unless the named declaration depends only on `propext`, `Classical.choice`,
`Quot.sound`. -/
elab "#assert_std_axioms " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← liftCoreM <| Lean.collectAxioms n
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for a in axs do
    unless ok.contains a do
      throwError "{n} depends on non-standard axiom {a}"
  logInfo m!"{n} : standard axioms only {axs}"

namespace Erdos287.PostV71V87

-- Model
#assert_std_axioms ExactWord.toCounterexample
#assert_std_axioms ofCounterexample_one_lt_a
#assert_std_axioms exact_implies_surrogate
#assert_std_axioms Word.guard_pattern
#assert_std_axioms Word.active_of_lt_qstar
-- V83 (retired minor route)
#assert_std_axioms MinorData.actual_sub_target
#assert_std_axioms MinorData.den_actual
#assert_std_axioms MinorData.actual_integral_iff
#assert_std_axioms fixed_depth_compression
#assert_std_axioms fixed_depth_not_exact_mass
#assert_std_axioms integer_det_integral
-- V84/V85 positional
#assert_std_axioms ExactWord.two_le_layer_card
#assert_std_axioms ExactWord.not_active_of_lt_two_mul
#assert_std_axioms ExactWord.conditioned_row_rejection
#assert_std_axioms ExactWord.positional_chain
#assert_std_axioms ExactWord.Q_two_le_D
-- V84/V85 conditional (the provider is a hypothesis; no axiom)
#assert_std_axioms dyadic_supply_modulus_one
#assert_std_axioms fixed_modulus_saturation
#assert_std_axioms fixed_base_primary_growth
#assert_std_axioms qstar_tendsto_of_fixed
#assert_std_axioms uniform_modulus_saturation
#assert_std_axioms growing_base_primary_growth
#assert_std_axioms qstar_gt_of_uniform
#assert_std_axioms maximal_carrier_of_uniform
-- V86 endpoint-anchored CRT
#assert_std_axioms Word.endpoint_anchored_crt
#assert_std_axioms Word.Q_mul_Q_gt_D
#assert_std_axioms Word.small_ceiling_unique
#assert_std_axioms Word.card_small_ceilings_le_one
#assert_std_axioms Word.low_start_chamber
#assert_std_axioms Word.Q_pair_annulus
#assert_std_axioms Word.owner_disjoint
#assert_std_axioms Word.guard_triple_owner_unique
#assert_std_axioms ExactWord.dyadic_two_sided_saturation
#assert_std_axioms ExactWord.ceiling_annulus
-- V87 reciprocal image / minimal grid
#assert_std_axioms chebyshev_upper
#assert_std_axioms primeCounting_lower
#assert_std_axioms Srec_block_bound
#assert_std_axioms log_Srec_le
#assert_std_axioms ExactWord.shell_fingerprint
#assert_std_axioms ExactWord.entropy_core
#assert_std_axioms entropy_inequality
#assert_std_axioms entropy_inversion
#assert_std_axioms repaired_recurrence
-- Physical consequences
#assert_std_axioms Word.card_internalMultiples_ge
#assert_std_axioms Word.guard_at_internal_qstar
#assert_std_axioms Word.exists_disjoint_guard_family
#assert_std_axioms many_disjoint_guards
#assert_std_axioms Word.carrier_reserve
#assert_std_axioms Word.carrier_overlap_le_four
#assert_std_axioms ExactWord.carrier_union_lower
-- Firewalls / frontier
#assert_std_axioms highShell_trivial
#assert_std_axioms highShell_some_empty_row
#assert_std_axioms nearbyTransition_implies_proximity
#assert_std_axioms proximity_not_from_trivial_highShell
#assert_std_axioms realisation_of_exact
#assert_std_axioms crossScale_iff_tail
#assert_std_axioms tail_closure_of_crossScale
#assert_std_axioms erdos287_of_crossScale_and_finite
#assert_std_axioms polylog_window_not_excluded
-- Regression fixtures
#assert_std_axioms reg_dvd_ne_zero
#assert_std_axioms reg_actual_ne_target
#assert_std_axioms reg_surrogate_not_exact
#assert_std_axioms reg_pointwise_not_uniform
#assert_std_axioms reg_endpoint_second_branch
#assert_std_axioms reg_active_above_qstar
#assert_std_axioms reg_superlog_not_polylog
-- Closure DAG
#assert_std_axioms DAG.dag_acyclic
#assert_std_axioms DAG.dag_exact_support
#assert_std_axioms DAG.dag_conditional_has_open
#assert_std_axioms DAG.dag_no_retired_use
#assert_std_axioms DAG.dag_erdos287_open
#assert_std_axioms DAG.dag_erdos287_open_support
#assert_std_axioms DAG.dag_proved_have_decls

#print axioms repaired_recurrence
#print axioms log_Srec_le
#print axioms Word.endpoint_anchored_crt
#print axioms ExactWord.shell_fingerprint
#print axioms many_disjoint_guards
#print axioms ExactWord.carrier_union_lower
#print axioms tail_closure_of_crossScale

end Erdos287.PostV71V87

/-! ## Provider-construction audit

`#audit_providers` scans every declaration in the namespace `Erdos287.PostV71V87` whose
statement *concludes* one of the open / analytic provider propositions.  The build fails if
such a declaration has no `Prop`-valued hypothesis (i.e. if it would construct a provider
outright), except for the single explicitly whitelisted trivial-threshold instance
`highShell_trivial : HighShellExtinction (fun M => M / 2) 0`.  The surviving (conditional)
declarations are listed for review. -/

open Lean Meta Elab Command in
/-- Audit that no declaration in the subtree constructs an open provider. -/
elab "#audit_providers" : command => do
  let env ← getEnv
  let pre : Name := `Erdos287.PostV71V87
  let providers : List Name :=
    [`Erdos287.PostV71V87.FixedModulusDyadicSupply, `Erdos287.PostV71V87.UniformDyadicSupply,
     `Erdos287.PostV71V87.HighShellExtinction,
     `Erdos287.PostV71V87.IntermediateScaleControl287,
     `Erdos287.PostV71V87.NearbyTransition287, `Erdos287.PostV71V87.Proximity287,
     `Erdos287.PostV71V87.CrossScaleSynchronization287,
     `Erdos287.PostV71V87.FiniteExclusionBelow]
  let allowed : List Name := [`Erdos287.PostV71V87.highShell_trivial]
  for p in providers do
    unless env.contains p do throwError "provider {p} not found"
  let mut hits : Array MessageData := #[]
  let mut bad : Array Name := #[]
  for (n, ci) in env.constants.toList do
    unless pre.isPrefixOf n do continue
    if n.isInternal then continue
    let res ← liftTermElabM <| forallTelescope ci.type fun xs concl => do
      let some h := concl.getAppFn.constName? | return none
      unless providers.contains h do return none
      let mut nprop := 0
      for x in xs do
        if ← isProp (← inferType x) then nprop := nprop + 1
      return some (h, nprop)
    if let some (h, nprop) := res then
      hits := hits.push m!"{n} ⊢ {h} (Prop hypotheses: {nprop})"
      if nprop == 0 && !allowed.contains n then bad := bad.push n
  unless bad.isEmpty do
    throwError "provider constructed without hypotheses: {bad}"
  logInfo m!"provider audit passed; provider-concluding declarations:\n{MessageData.joinSep hits.toList "\n"}"

#audit_providers
