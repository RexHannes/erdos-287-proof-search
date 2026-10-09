import RequestProject.Erdos287.PostV87V90R.ClosureDAG

/-!
# Erdős #287 (post-V87 → V90R) — axiom, provider and naming audit

* `#assert_std_axioms_v90 foo` — collects the transitive axioms of `foo` (as `#print axioms`
  does) and **fails the build** unless they are among `propext`, `Classical.choice`,
  `Quot.sound`.  `sorryAx`, custom axioms and the `native_decide` axiom `Lean.ofReduceBool` are
  therefore rejected.
* `#assert_unconditional foo` — fails if the *statement* of `foo` mentions any open provider /
  owner constant (an exact theorem must not secretly assume a provider).
* `#assert_conditional foo` — fails unless the statement of `foo` mentions an open provider
  (a conditional theorem must visibly carry its assumption).
* `#audit_providers_v90` — scans every declaration of `Erdos287.PostV87V90R` whose statement
  *concludes* a guarded provider / owner / open-statement constant and fails if it has no
  hypothesis of guarded type, or if it has a hypothesis of type `False` or `IsEmpty _`
  (vacuous `False.elim` / `IsEmpty` constructions).  Structure constructors and auxiliary
  recursors are skipped (their hypotheses *are* the fields).
-/

open Lean Elab Command Meta

/-- Fail unless `id` depends only on `propext`, `Classical.choice`, `Quot.sound`. -/
elab "#assert_std_axioms_v90 " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← liftCoreM <| Lean.collectAxioms n
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for a in axs do
    unless ok.contains a do
      throwError "{n} depends on non-standard axiom {a}"
  logInfo m!"{n} : standard axioms only {axs}"

/-- Open provider / owner / open-statement constants guarded by the audit. -/
def guardedV90 : List Name :=
  [`Erdos287.PostV87V90R.WidthThreeMomentProvider, `Erdos287.PostV87V90R.WindowMomentData,
   `Erdos287.PostV87V90R.NarrowWidthClosureProvider, `Erdos287.PostV87V90R.E287_11_4_Provider,
   `Erdos287.PostV87V90R.AffineContactCompiler, `Erdos287.PostV87V90R.AnnulusBarrier287,
   `Erdos287.PostV87V90R.W3Statement, `Erdos287.PostV87V90R.TailExclusion,
   `Erdos287.PostV71V87.FiniteExclusionBelow,
   `Erdos287.PostV71V87.CrossScaleSynchronization287]

/-- Open *providers* (the analytic / closure inputs) — mention marks a theorem conditional. -/
def providersV90 : List Name :=
  [`Erdos287.PostV87V90R.WidthThreeMomentProvider, `Erdos287.PostV87V90R.WindowMomentData,
   `Erdos287.PostV87V90R.NarrowWidthClosureProvider, `Erdos287.PostV87V90R.E287_11_4_Provider,
   `Erdos287.PostV87V90R.AnnulusBarrier287, `Erdos287.PostV71V87.FiniteExclusionBelow,
   `Erdos287.PostV71V87.CrossScaleSynchronization287]

/-- Fail if the statement of `id` mentions an open provider. -/
elab "#assert_unconditional " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let ci ← getConstInfo n
  let used := ci.type.getUsedConstants
  for p in providersV90 do
    if used.contains p then
      throwError "{n} is labelled unconditional but its statement mentions provider {p}"
  logInfo m!"{n} : statement mentions no open provider"

/-- Fail unless the statement of `id` mentions an open provider. -/
elab "#assert_conditional " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let ci ← getConstInfo n
  let used := ci.type.getUsedConstants
  let hits := providersV90.filter used.contains
  if hits.isEmpty then
    throwError "{n} is labelled conditional but its statement mentions no open provider"
  logInfo m!"{n} : conditional on {hits}"

/-- Audit that no declaration of the subtree constructs a guarded provider outright or from a
vacuous hypothesis. -/
elab "#audit_providers_v90" : command => do
  let env ← getEnv
  let pre : Name := `Erdos287.PostV87V90R
  for p in guardedV90 do
    unless env.contains p do throwError "guarded constant {p} not found"
  let skipSuffix : List String :=
    ["mk", "casesOn", "recOn", "rec", "brecOn", "binductionOn", "below", "ibelow",
     "noConfusion", "noConfusionType", "ctorIdx", "ctorElim", "ctorElimType", "injEq", "inj",
     "sizeOf_spec"]
  let mut hits : Array MessageData := #[]
  let mut bad : Array Name := #[]
  for (n, ci) in env.constants.toList do
    unless pre.isPrefixOf n do continue
    if n.isInternal then continue
    if (ci matches .ctorInfo _) || (ci matches .recInfo _) then continue
    if let .str _ s := n then
      if skipSuffix.contains s then continue
    let res ← liftTermElabM <| forallTelescope ci.type fun xs concl => do
      let some h := concl.getAppFn.constName? | return none
      unless guardedV90.contains h do return none
      let mut good := false
      let mut vac := false
      for x in xs do
        let ty ← inferType x
        let hd ← forallTelescope ty fun _ b => pure b.getAppFn.constName?
        if let some hn := hd then
          if guardedV90.contains hn then good := true
        let ty' ← whnfR ty
        if let some hn := ty'.getAppFn.constName? then
          if hn == ``False || hn == ``IsEmpty || hn == ``Empty then vac := true
      return some (h, good, vac)
    if let some (h, good, vac) := res then
      hits := hits.push m!"{n} ⊢ {h} (guarded hypothesis: {good}, vacuous hypothesis: {vac})"
      if !good || vac then bad := bad.push n
  unless bad.isEmpty do
    throwError "provider constructed without a guarded hypothesis or from a vacuous one: {bad}"
  logInfo m!"provider audit passed; guarded-concluding declarations:\n{MessageData.joinSep hits.toList "\n"}"

namespace Erdos287.PostV87V90R

/-! ## Transitive axioms of the principal theorems -/

-- model compatibility
#assert_std_axioms_v90 counterexample_iff_exactWord
#assert_std_axioms_v90 ExactWord.exp_lower
#assert_std_axioms_v90 ExactWord.exp_upper
-- V88 retained / retired consumers / regression facts
#assert_std_axioms_v90 conductor_replication
#assert_std_axioms_v90 primePower_replication
#assert_std_axioms_v90 guardOwner_unique
#assert_std_axioms_v90 lcm_transfer
#assert_std_axioms_v90 isolated_omissions_realizable
#assert_std_axioms_v90 single_grid_realizable
#assert_std_axioms_v90 even_multigrid_realizable
#assert_std_axioms_v90 exterior_obligations_do_not_combine
#assert_std_axioms_v90 proximity_density_no_contact
#assert_std_axioms_v90 crossScale_retired_equiv_tail
-- V90 geometry
#assert_std_axioms_v90 card_shiftSet_ge
#assert_std_axioms_v90 indep_card_le
#assert_std_axioms_v90 arc_indep
#assert_std_axioms_v90 alpha_contactCycle
#assert_std_axioms_v90 alpha_G
#assert_std_axioms_v90 exists_useful_edge
#assert_std_axioms_v90 G_11_2_adj_iff
#assert_std_axioms_v90 alpha_G_11_2
#assert_std_axioms_v90 G_11_2_four_subsets_have_edge
#assert_std_axioms_v90 G_11_2_three_indep
#assert_std_axioms_v90 width_ratio
#assert_std_axioms_v90 widthParam_spec
#assert_std_axioms_v90 width_lt_of_widthParam
-- repaired moment consumer
#assert_std_axioms_v90 pointwise_cauchy
#assert_std_axioms_v90 moment_cauchy
#assert_std_axioms_v90 expected_occupancy_lower
#assert_std_axioms_v90 exists_occupancy_of_moment
#assert_std_axioms_v90 moment_numerical
#assert_std_axioms_v90 occupancy_of_normalized_moments
#assert_std_axioms_v90 occupancy_11_3
#assert_std_axioms_v90 qbal_le_pairs
#assert_std_axioms_v90 qbal_supporting_line
#assert_std_axioms_v90 sharp_mean_consumer
#assert_std_axioms_v90 exists_occupancy_of_sharp
-- affine compiler
#assert_std_axioms_v90 gcd_eq_sub_iff
#assert_std_axioms_v90 affine_adjacency
#assert_std_axioms_v90 nMinus_mul_d
#assert_std_axioms_v90 nPlus_mul_d
#assert_std_axioms_v90 AffineContactCompiler.edge_adjacent
-- row rigidity
#assert_std_axioms_v90 BH_pos
#assert_std_axioms_v90 selRow_empty_of_bounded_cofactors
#assert_std_axioms_v90 selRow_eq_empty
#assert_std_axioms_v90 selRow_empty_of_lt
#assert_std_axioms_v90 adjacent_empty_rows_contradiction
#assert_std_axioms_v90 ContactWitness.false
-- consumers
#assert_std_axioms_v90 false_of_edge
#assert_std_axioms_v90 occupancy_contact_false
#assert_std_axioms_v90 moment_contact_false
#assert_std_axioms_v90 sharp_contact_false
-- conditional
#assert_std_axioms_v90 WindowMomentData.false
#assert_std_axioms_v90 W3_of_provider
#assert_std_axioms_v90 W3Statement_of_provider
#assert_std_axioms_v90 W3_counterexample_form
#assert_std_axioms_v90 W3_family_of_providers
#assert_std_axioms_v90 wideWindow_exists
#assert_std_axioms_v90 narrowWidth_bounds
#assert_std_axioms_v90 tail_of_W3Statement_narrow
#assert_std_axioms_v90 tail_of_W3_narrow
#assert_std_axioms_v90 tail_of_W3family_narrow
#assert_std_axioms_v90 erdos287_of_W3_narrow_finite
#assert_std_axioms_v90 E287_11_4_geometry
#assert_std_axioms_v90 E287_11_4
#assert_std_axioms_v90 tail_of_E287_11_4
#assert_std_axioms_v90 residualWindow_exists
-- regression suite
#assert_std_axioms_v90 C_lt_11_3_alone_insufficient
#assert_std_axioms_v90 obsolete_11_6_not_threshold
#assert_std_axioms_v90 crossScale_not_reduction
#assert_std_axioms_v90 width_exclusion_not_global
#assert_std_axioms_v90 fixed_s_not_pointwise_three
#assert_std_axioms_v90 wordQuantified_provider_trivial
#assert_std_axioms_v90 predicate_provider_trivial
#assert_std_axioms_v90 windowMomentData_exposes
#assert_std_axioms_v90 finite_verifier_not_asymptotic
#assert_std_axioms_v90 three_blocks_no_contact
#assert_std_axioms_v90 finite_bank_gap
-- closure DAG
#assert_std_axioms_v90 DAG.dag_acyclic
#assert_std_axioms_v90 DAG.dag_exact_support
#assert_std_axioms_v90 DAG.dag_conditional_has_open
#assert_std_axioms_v90 DAG.dag_no_retired_use
#assert_std_axioms_v90 DAG.dag_erdos287_open
#assert_std_axioms_v90 DAG.dag_erdos287_open_support
#assert_std_axioms_v90 DAG.dag_global_needs_narrow_and_finite
#assert_std_axioms_v90 DAG.dag_narrow_is_owner
#assert_std_axioms_v90 DAG.dag_proved_have_decls

/-! ## Naming audit: exact theorems mention no provider; conditional ones visibly do -/

#assert_unconditional alpha_contactCycle
#assert_unconditional alpha_G_11_2
#assert_unconditional moment_cauchy
#assert_unconditional exists_occupancy_of_moment
#assert_unconditional occupancy_of_normalized_moments
#assert_unconditional occupancy_11_3
#assert_unconditional qbal_le_pairs
#assert_unconditional sharp_mean_consumer
#assert_unconditional affine_adjacency
#assert_unconditional selRow_empty_of_bounded_cofactors
#assert_unconditional adjacent_empty_rows_contradiction
#assert_unconditional occupancy_contact_false
#assert_unconditional moment_contact_false
#assert_unconditional single_grid_realizable
#assert_unconditional counterexample_iff_exactWord

#assert_conditional W3_of_provider
#assert_conditional W3Statement_of_provider
#assert_conditional W3_counterexample_form
#assert_conditional W3_family_of_providers
#assert_conditional tail_of_W3_narrow
#assert_conditional tail_of_W3family_narrow
#assert_conditional erdos287_of_W3_narrow_finite
#assert_conditional E287_11_4
#assert_conditional tail_of_E287_11_4

#print axioms alpha_contactCycle
#print axioms moment_cauchy
#print axioms sharp_mean_consumer
#print axioms affine_adjacency
#print axioms selRow_empty_of_bounded_cofactors
#print axioms occupancy_contact_false
#print axioms W3_of_provider
#print axioms E287_11_4
#print axioms erdos287_of_W3_narrow_finite

end Erdos287.PostV87V90R

#audit_providers_v90
